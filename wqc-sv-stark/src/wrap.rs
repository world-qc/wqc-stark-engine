//! The STARK side of the SNARK wrap: brings a task's root to one proof shape that a fixed
//! Groth16 circuit verifies.
//!
//! A root's verifier depends on the task (the leaf circuits fix every layer's preprocessed
//! commitment), and its statement is the leaf statements concatenated, so its length depends on
//! the leaves. A Groth16 circuit is fixed once, so the wrap chain removes both:
//!
//! 1. A [`DigestLayer`] verifies the root with the root's relation taken from the proof's shape
//!    and its preprocessed commitment as an input, and exports one 4-element digest: a Poseidon2
//!    sponge over every table's public values (the root statement among them) and that
//!    commitment. The digest binds the root's statement and its relation; its length is fixed.
//! 2. [`NORMALIZE_LAYERS`] recursion layers over it: the shape of a layer's proof depends only
//!    on its child's shape, and from here on it no longer changes.
//! 3. A top layer with [`FriParams::WRAP`]: fewer queries, so fewer Merkle paths for the SNARK.
//!
//! The SNARK then runs the verifier circuit of the top proof ([`verifier_circuit`]), which takes
//! the top layer's preprocessed commitment as an input: that commitment and the digest are what
//! a task's verifier must check.

use std::ops::Range;

use p3_challenger::{CanObserve, CanSample, DuplexChallenger};
use p3_circuit::tables::Traces;
use p3_circuit::{Circuit, CircuitBuilder, ExprId, StatementExport, WitnessId};
use p3_circuit_prover::batch_stark_prover::CircuitVerifier;
use p3_circuit_prover::batch_stark_prover::TableProver;
use p3_circuit_prover::{
    BatchStarkProver, ConstraintProfile, PreparedCircuitProver, StatementAirBuilder,
    StatementPreprocessor, StatementProver,
};
use p3_field::PrimeField64;
use p3_lookup::logup::LogUpGadget;
use p3_recursion::verifier::verify_p3_batch_proof_circuit;
use p3_recursion::{
    replay_recursion_input_transcript, BatchOnly, BatchStarkVerifierInputsBuilder,
    CircuitChallenger, FriRecursionConfig, PcsRecursionBackend, Poseidon2Config, RecursionInput,
    RecursiveChallenger,
};
use serde::{Deserialize, Serialize};

use crate::leaf::{decode_proof, encode_proof};
use crate::recursion::{backend, params, verify, Backend, Layer, RecursionProof};
use crate::{Cfg, Challenge, Error, FriParams, F};

/// Recursion layers between the [`DigestLayer`] and the top layer.
pub const NORMALIZE_LAYERS: usize = 2;

/// Elements of the digest a [`DigestLayer`] exports.
pub const DIGEST_LEN: usize = 4;

type Inputs = BatchStarkVerifierInputsBuilder<
    Cfg,
    <Cfg as FriRecursionConfig>::Commitment,
    <Cfg as FriRecursionConfig>::OpeningProof,
>;

fn rec(e: impl core::fmt::Debug) -> Error {
    Error::Recursion(format!("{e:?}"))
}

/// The verifier circuit of `child`'s proofs, with the child's relation taken from the shape of
/// `sample` and its preprocessed commitment an input (Plonky3-recursion's untrusted path).
pub struct VerifierCircuit {
    pub circuit: Circuit<Challenge>,
    inputs: Inputs,
    op_ids: Vec<p3_circuit::NonPrimitiveOpId>,
    /// Public-input positions of the child's preprocessed commitment.
    pub commitment: Range<usize>,
    /// Public-input positions of the child's table public values (the statement among them).
    pub table_publics: Range<usize>,
}

fn input<'a>(
    child: &'a CircuitVerifier<Cfg>,
    proof: &'a RecursionProof,
) -> Result<RecursionInput<'a, Cfg, BatchOnly>, Error> {
    let table_public_inputs = child
        .table_public_values(&proof.statement)
        .map_err(|e| Error::InvalidStatement(e.to_string()))?;
    Ok(RecursionInput::BatchStark {
        proof: &proof.proof,
        common_data: child.common_data(),
        table_public_inputs,
    })
}

/// The table provers that rebuild a child proof's tables: the backend's, and the statement
/// table (which the backend's own input path does not know).
fn input_provers(
    child: &CircuitVerifier<Cfg>,
    proof: &RecursionProof,
) -> Vec<Box<dyn TableProver<Cfg>>> {
    let op_types: Vec<_> = proof
        .proof
        .non_primitives
        .iter()
        .map(|e| e.op_type.clone())
        .collect();
    let mut provers =
        PcsRecursionBackend::<Cfg, BatchOnly, 2>::input_table_provers(&backend(), 2, &op_types);
    provers.push(Box::new(StatementProver::<2>::new(
        child.statement_layout().schema().clone(),
    )));
    provers
}

fn commitment_values(child: &CircuitVerifier<Cfg>) -> Result<Vec<F>, Error> {
    let pre = child
        .common_data()
        .preprocessed
        .as_ref()
        .ok_or_else(|| Error::Recursion("child has no preprocessed commitment".into()))?;
    Ok(pre.commitment.roots().iter().flatten().copied().collect())
}

/// Builds the verifier circuit; `digest` adds the [`DigestLayer`]'s sponge and exports it.
fn build(
    child: &CircuitVerifier<Cfg>,
    sample: &RecursionProof,
    digest: Option<&[ExprId]>,
) -> Result<(VerifierCircuit, Option<p3_circuit::StatementSchema>), Error> {
    let backend = backend();
    let config = child.config();
    let prev = input(child, sample)?;
    let b = &backend;
    // The backend's `validate_input` would rebuild the child's tables without the statement
    // table and refuse; every child proof here is verified natively before its circuit is used.
    PcsRecursionBackend::<Cfg, BatchOnly, 2>::preflight_input(b, config, &prev).map_err(rec)?;
    let provers = input_provers(child, sample);

    let mut builder = CircuitBuilder::<Challenge>::new();
    PcsRecursionBackend::<Cfg, BatchOnly, 2>::prepare_circuit(b, config, &mut builder)
        .map_err(rec)?;
    let (inputs, op_ids) = verify_p3_batch_proof_circuit::<
        Cfg,
        <Cfg as FriRecursionConfig>::Commitment,
        <Cfg as FriRecursionConfig>::InputProof,
        <Cfg as FriRecursionConfig>::OpeningProof,
        _,
        _,
        8,
        4,
        2,
    >(
        config,
        &mut builder,
        &sample.proof,
        config.pcs_verifier_params(),
        child.common_data(),
        &LogUpGadget::new(),
        Poseidon2Config::GOLDILOCKS_D2_W8,
        &provers,
    )
    .map_err(rec)?;

    // Public inputs are allocated table values first and the child's commitment last; `run`
    // checks both ranges against the values it packs.
    let publics: usize = inputs.air_public_targets.iter().map(Vec::len).sum();
    let total = builder.public_input_count();
    let commitment_len = commitment_values(child)?.len();
    let commitment = total - commitment_len..total;

    let schema = match digest {
        None => None,
        Some(commitment_exprs) => {
            let mut sponge =
                CircuitChallenger::<8, 4, Poseidon2Config>::new(Poseidon2Config::GOLDILOCKS_D2_W8);
            sponge.init::<F, Challenge>(&mut builder);
            for &t in inputs.air_public_targets.iter().flatten() {
                RecursiveChallenger::<F, Challenge>::observe(&mut sponge, &mut builder, t);
            }
            for &t in commitment_exprs {
                RecursiveChallenger::<F, Challenge>::observe(&mut sponge, &mut builder, t);
            }
            let out: Vec<StatementExport> = (0..DIGEST_LEN)
                .map(|_| {
                    StatementExport::Base(RecursiveChallenger::<F, Challenge>::sample(
                        &mut sponge,
                        &mut builder,
                    ))
                })
                .collect();
            Some(builder.set_statement_exports::<F>(&out).map_err(rec)?)
        }
    };
    let circuit = builder.build().map_err(rec)?;
    Ok((
        VerifierCircuit {
            circuit,
            inputs,
            op_ids,
            commitment,
            table_publics: 0..publics,
        },
        schema,
    ))
}

/// The expressions holding the public inputs at `positions` (any one per witness slot).
fn public_exprs(
    circuit: &Circuit<Challenge>,
    positions: Range<usize>,
) -> Result<Vec<ExprId>, Error> {
    positions
        .map(|pos| {
            let w: WitnessId = circuit.public_rows[pos];
            circuit
                .expr_to_widx
                .iter()
                .filter(|(_, &v)| v == w)
                .map(|(&e, _)| e)
                .min()
                .ok_or_else(|| Error::Recursion(format!("no expression for public input {pos}")))
        })
        .collect()
}

/// The verifier circuit of `child`'s proofs; `sample` fixes the allocation shape.
pub fn verifier_circuit(
    child: &CircuitVerifier<Cfg>,
    sample: &RecursionProof,
) -> Result<VerifierCircuit, Error> {
    Ok(build(child, sample, None)?.0)
}

impl VerifierCircuit {
    /// Runs the circuit on `proof` (a proof of `child`), returning every table's trace.
    pub fn run(
        &self,
        child: &CircuitVerifier<Cfg>,
        proof: &RecursionProof,
    ) -> Result<Traces<Challenge>, Error> {
        let prev = input(child, proof)?;
        let RecursionInput::BatchStark {
            common_data,
            table_public_inputs,
            ..
        } = &prev
        else {
            unreachable!()
        };
        let (public, private) =
            self.inputs
                .pack_values(table_public_inputs, &proof.proof.proof, common_data);
        let flat: Vec<Challenge> = table_public_inputs
            .iter()
            .flatten()
            .chain(&commitment_values(child)?)
            .map(|&v| v.into())
            .collect();
        let at = |r: &Range<usize>| public.get(r.clone()).unwrap_or_default().to_vec();
        if [at(&self.table_publics), at(&self.commitment)].concat() != flat {
            return Err(Error::Recursion(
                "public inputs are not laid out as expected".into(),
            ));
        }
        let mut runner = self.circuit.runner();
        runner.set_public_inputs(&public).map_err(rec)?;
        runner.set_private_inputs(&private).map_err(rec)?;
        // The backend's `set_private_data`, with the statement table's prover added.
        let config = child.config();
        let transcript =
            replay_recursion_input_transcript(config, &prev, &input_provers(child, proof))
                .map_err(rec)?;
        Cfg::with_fri_opening_proof(&prev, |opening| {
            Cfg::set_fri_private_data(config, &mut runner, &self.op_ids, opening, transcript)
        })
        .map_err(rec)?;
        runner.run().map_err(rec)
    }
}

/// The digest a [`DigestLayer`] over `child` exports for a child proof with `statement`.
pub fn statement_digest(
    child: &CircuitVerifier<Cfg>,
    statement: &[F],
) -> Result<[F; DIGEST_LEN], Error> {
    let publics = child
        .table_public_values(statement)
        .map_err(|e| Error::InvalidStatement(e.to_string()))?;
    let mut sponge = DuplexChallenger::<F, _, 8, 4>::new(
        p3_recursion::builtin_config::fixed_goldilocks_poseidon2_8(),
    );
    for v in publics.iter().flatten() {
        sponge.observe(*v);
    }
    for v in commitment_values(child)? {
        sponge.observe(v);
    }
    Ok(core::array::from_fn(|_| sponge.sample()))
}

/// Verifies a child proof and exports [`statement_digest`] as its statement.
pub struct DigestLayer {
    child: CircuitVerifier<Cfg>,
    vc: VerifierCircuit,
    prepared: PreparedCircuitProver<Cfg>,
}

impl DigestLayer {
    pub fn new(child: CircuitVerifier<Cfg>, sample: &RecursionProof) -> Result<Self, Error> {
        Self::new_with(child, sample, FriParams::RECURSION)
    }

    pub(crate) fn new_with(
        child: CircuitVerifier<Cfg>,
        sample: &RecursionProof,
        fri: FriParams,
    ) -> Result<Self, Error> {
        // The commitment's public inputs come from inside the verifier, which does not return
        // them: find their expressions in a first build, then build again with the sponge. The
        // build is deterministic, and the second circuit is checked to hash exactly them.
        let (plain, _) = build(&child, sample, None)?;
        let exprs = public_exprs(&plain.circuit, plain.commitment.clone())?;
        let (vc, schema) = build(&child, sample, Some(&exprs))?;
        if vc.commitment != plain.commitment {
            return Err(Error::Recursion(
                "commitment inputs moved between builds".into(),
            ));
        }
        for (e, pos) in exprs.iter().zip(vc.commitment.clone()) {
            if vc.circuit.expr_to_widx.get(e) != Some(&vc.circuit.public_rows[pos]) {
                return Err(Error::Recursion(format!(
                    "digest input {e:?} is not public input {pos}"
                )));
            }
        }
        let schema = schema.expect("built with the digest");
        let b: Backend = backend();
        let mut preprocessors =
            PcsRecursionBackend::<Cfg, BatchOnly, 2>::non_primitive_preprocessors(&b);
        preprocessors.push(Box::new(StatementPreprocessor::new(schema.clone())));
        let mut air_builders =
            PcsRecursionBackend::<Cfg, BatchOnly, 2>::non_primitive_air_builders(&b);
        air_builders.push(Box::new(StatementAirBuilder::<2>::new(schema.clone())));
        let mut prover =
            BatchStarkProver::new(fri.config()).with_table_packing(params(fri).table_packing);
        for p in PcsRecursionBackend::<Cfg, BatchOnly, 2>::non_primitive_provers(&b, 2) {
            prover.register_table_prover(p);
        }
        prover.register_table_prover(Box::new(StatementProver::<2>::new(schema)));
        let prepared = prover
            .prepare_circuit::<Challenge, 2>(
                &vc.circuit,
                &preprocessors,
                &air_builders,
                ConstraintProfile::Standard,
            )
            .map_err(rec)?;
        Ok(Self {
            child,
            vc,
            prepared,
        })
    }

    pub fn prove(&self, child_proof: &RecursionProof) -> Result<RecursionProof, Error> {
        let traces = self.vc.run(&self.child, child_proof)?;
        let proof = self.prepared.prove(&traces).map_err(rec)?;
        let statement = statement_digest(&self.child, &child_proof.statement)?.to_vec();
        Ok(RecursionProof { proof, statement })
    }

    pub fn verifier(&self) -> CircuitVerifier<Cfg> {
        self.prepared.verifier()
    }
}

/// Shape of every proof that leaves the [`NORMALIZE_LAYERS`] (at [`FriParams::RECURSION`]):
/// primitive table rows (witness, public/const, ALU) and each table's degree bits.
pub const FIXED_ROWS: [usize; 3] = [281, 68, 37865];
pub const FIXED_DEGREE_BITS: [usize; 6] = [9, 7, 14, 14, 11, 4];

fn check_fixed_shape(proof: &RecursionProof, fri: FriParams) -> Result<(), Error> {
    if fri != FriParams::RECURSION {
        return Ok(());
    }
    let rows: Vec<usize> = proof.proof.rows.iter().collect();
    if rows != FIXED_ROWS || proof.proof.proof.degree_bits != FIXED_DEGREE_BITS {
        return Err(Error::Recursion(format!(
            "normalized proof has rows {rows:?} and degree bits {:?}, not the fixed shape",
            proof.proof.proof.degree_bits
        )));
    }
    Ok(())
}

/// A wrap chain's proofs ([`encode_proof`] bytes): the [`DigestLayer`], the
/// [`NORMALIZE_LAYERS`], then the top layer.
#[derive(Serialize, Deserialize)]
pub struct WrapProof {
    pub proofs: Vec<Vec<u8>>,
}

/// The top of a wrap chain, which the SNARK verifies. Its statement is the
/// [`statement_digest`] of the root.
pub struct Wrapped {
    pub verifier: CircuitVerifier<Cfg>,
    pub proof: RecursionProof,
}

/// Proves the wrap chain over a root with verifier `root_verifier` (see
/// [`crate::root::verified_root`]).
pub fn prove_wrap(
    root_verifier: CircuitVerifier<Cfg>,
    root: &RecursionProof,
) -> Result<(WrapProof, Wrapped), Error> {
    prove_wrap_with(root_verifier, root, FriParams::RECURSION, FriParams::WRAP)
}

/// Verifies a wrap chain over a verified root, returning its top.
///
/// # Security
///
/// The root must come from [`crate::root::verified_root`] with the task's leaves: the chain
/// only binds the root's statement and relation through the digest.
pub fn verify_wrap(
    root_verifier: CircuitVerifier<Cfg>,
    root: &RecursionProof,
    wrap: &WrapProof,
) -> Result<Wrapped, Error> {
    verify_wrap_with(
        root_verifier,
        root,
        wrap,
        FriParams::RECURSION,
        FriParams::WRAP,
    )
}

pub(crate) fn prove_wrap_with(
    root_verifier: CircuitVerifier<Cfg>,
    root: &RecursionProof,
    fri: FriParams,
    top_fri: FriParams,
) -> Result<(WrapProof, Wrapped), Error> {
    let digest = DigestLayer::new_with(root_verifier, root, fri)?;
    let mut cur = digest.prove(root)?;
    let mut proofs = vec![encode_proof(&cur.proof)];
    let mut child = digest.verifier();
    for _ in 0..NORMALIZE_LAYERS {
        let layer = Layer::over_layer_with(child, &cur, fri)?;
        cur = layer.prove(&cur.proof, &cur.statement)?;
        proofs.push(encode_proof(&cur.proof));
        child = layer.verifier();
    }
    check_fixed_shape(&cur, fri)?;
    let top = Layer::over_layer_with(child, &cur, top_fri)?;
    let proof = top.prove(&cur.proof, &cur.statement)?;
    proofs.push(encode_proof(&proof.proof));
    Ok((
        WrapProof { proofs },
        Wrapped {
            verifier: top.verifier(),
            proof,
        },
    ))
}

pub(crate) fn verify_wrap_with(
    root_verifier: CircuitVerifier<Cfg>,
    root: &RecursionProof,
    wrap: &WrapProof,
    fri: FriParams,
    top_fri: FriParams,
) -> Result<Wrapped, Error> {
    if wrap.proofs.len() != NORMALIZE_LAYERS + 2 {
        return Err(Error::Verify(format!(
            "{} wrap proofs, expected {}",
            wrap.proofs.len(),
            NORMALIZE_LAYERS + 2
        )));
    }
    let statement = statement_digest(&root_verifier, &root.statement)?.to_vec();
    let mut proofs = wrap.proofs.iter();
    let mut next = |verifier: &CircuitVerifier<Cfg>| {
        let proof = decode_proof(proofs.next().expect("counted above"))?;
        verify(verifier, &proof, &statement)?;
        Ok::<_, Error>(RecursionProof {
            proof,
            statement: statement.clone(),
        })
    };
    let mut child = DigestLayer::new_with(root_verifier, root, fri)?.verifier();
    let mut cur = next(&child)?;
    for _ in 0..NORMALIZE_LAYERS {
        child = Layer::over_layer_with(child, &cur, fri)?.verifier();
        cur = next(&child)?;
    }
    check_fixed_shape(&cur, fri)?;
    let verifier = Layer::over_layer_with(child, &cur, top_fri)?.verifier();
    let proof = next(&verifier)?;
    Ok(Wrapped { verifier, proof })
}

/// The SNARK's public inputs for a wrap top: the digest, then the top layer's preprocessed
/// commitment (see [`crate::snark`]).
pub fn snark_public_inputs(top: &Wrapped) -> Result<Vec<u64>, Error> {
    Ok(top
        .proof
        .statement
        .iter()
        .copied()
        .chain(commitment_values(&top.verifier)?)
        .map(|v| v.as_canonical_u64())
        .collect())
}

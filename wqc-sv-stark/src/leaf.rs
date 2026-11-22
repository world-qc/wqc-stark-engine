//! Leaf circuit: build, prove, verify against a `[context, digest]` statement, or
//! `[context, digest, seed, shots, counts digest]` for a sampling leaf.
//!
//! The circuit (gate list, qubit count, and for sampling the measurements and shot count) is
//! part of the prepared relation: its preprocessed columns are committed at [`build`] time and
//! every verifier derived from the leaf checks proofs against that commitment. The statement
//! does not name the circuit, so a statement means nothing without the verifier of the circuit
//! it came from.

use p3_circuit::builder::CircuitBuilder;
use p3_circuit::{StatementExport, StatementSchema};
use p3_circuit_prover::batch_stark_prover::{
    BatchStarkProof, BatchStarkProver, CircuitVerifier, PreparedCircuitProver, TablePacking,
};
use p3_circuit_prover::common::{NpoAirBuilder, NpoPreprocessor};
use p3_circuit_prover::{
    ConstraintProfile, StatementAirBuilder, StatementPreprocessor, StatementProver,
};
use p3_field::{PrimeCharacteristicRing, PrimeField64};

use crate::born::{counts_digest, sample, seed_words, Sampling};
use crate::digest::DIGEST_LEN;
use crate::exec::*;
use crate::npo::*;
use crate::verify_cfg::VerifyCfg;
use crate::{Cfg, Error, FriParams, SecurityLevel, EF, F, MAX_QUBITS, MAX_ROWS};

/// Statement length: 4 context elements, then the 4-element terminal digest.
pub const STATEMENT_LEN: usize = 4 + DIGEST_LEN;
/// Sampling statement length: the above, then the seed (low and high 32 bits), the shot count
/// and the 4-element counts digest.
pub const SAMPLING_STATEMENT_LEN: usize = STATEMENT_LEN + 3 + DIGEST_LEN;

/// A prepared leaf circuit.
pub struct Leaf {
    prepared: PreparedCircuitProver<Cfg>,
    circuit: p3_circuit::Circuit<EF>,
    schema: StatementSchema,
    n: usize,
    /// Fused.
    gates: Vec<Gate>,
    sampling: Option<Sampling>,
    /// A segment leaf's initial logical state ([`build_segment`]).
    initial: Option<Vec<C>>,
}

/// A leaf proof with the statement it was proved for.
pub struct LeafProof {
    pub proof: BatchStarkProof<Cfg>,
    /// The prover's own claim. A verifier never verifies against it: it builds the expected
    /// statement itself (see [`Leaf::verify`]).
    pub statement: Vec<F>,
}

/// A leaf proof, without the prover's statement.
pub type Proof = BatchStarkProof<Cfg>;

/// A proof's bytes on the wire (postcard), as wqc-core sends them and [`decode_proof`] reads.
pub fn encode_proof(proof: &BatchStarkProof<Cfg>) -> Vec<u8> {
    postcard::to_allocvec(proof).expect("a proof serializes")
}

/// The statement `proof` claims: the prover's own, to prove a recursion layer over the proof
/// (a verifier builds the expected statement instead, see [`LeafVerifier::verify`]).
pub fn claimed_statement(proof: &BatchStarkProof<Cfg>) -> Result<Vec<F>, Error> {
    proof
        .non_primitives
        .iter()
        .find(|e| e.op_type == p3_circuit::ops::NpoTypeId::statement())
        .map(|e| e.public_values.clone())
        .ok_or_else(|| Error::Prove("proof carries no statement table".into()))
}

/// Reads [`encode_proof`]'s bytes; trailing bytes are an error.
pub fn decode_proof(bytes: &[u8]) -> Result<BatchStarkProof<Cfg>, Error> {
    decode(bytes)
}

/// [`decode_proof`] for either config: a [`VerifyCfg`] proof has the same fields and types as
/// a [`Cfg`] one, so the same bytes (a test checks it).
pub(crate) fn decode<SC>(bytes: &[u8]) -> Result<BatchStarkProof<SC>, Error>
where
    SC: p3_uni_stark::StarkGenericConfig,
    BatchStarkProof<SC>: serde::de::DeserializeOwned,
{
    match postcard::take_from_bytes(bytes) {
        Ok((proof, [])) => Ok(proof),
        Ok((_, rest)) => Err(Error::Verify(format!(
            "{} trailing bytes after the proof",
            rest.len()
        ))),
        Err(e) => Err(Error::Verify(format!("proof bytes: {e}"))),
    }
}

/// Builds and prepares the leaf circuit for `gates` on `n` qubits (`1 ≤ n ≤ MAX_QUBITS`) at
/// `level`, which fixes the FRI parameters ([`FriParams::leaf`]) and so the verifier.
pub fn build(level: SecurityLevel, n: usize, gates: Vec<Gate>) -> Result<Leaf, Error> {
    build_with_tamper(FriParams::leaf(level), n, gates, None, None, Tamper::None)
}

/// Builds a segment leaf: `gates` on `n` qubits from `initial` instead of `|0…0⟩`, with
/// `sampling` when the segment is a task's last and the task samples. `initial` is the
/// logical state the task's earlier segments reach ([`segment_start`]); it is part of the
/// circuit (a preprocessed column), so a verifier derives it itself, as it derives the gates,
/// and a proof made from another initial state fails. The statement is a leaf's
/// (`[context, digest]`, or a sampling one).
///
/// A circuit too deep for one leaf ([`MAX_ROWS`]) is cut into segments, each fused on its
/// own: the result is that of the segments applied in order, which rounds differently from
/// the whole circuit fused at once.
pub fn build_segment(
    level: SecurityLevel,
    n: usize,
    gates: Vec<Gate>,
    initial: Vec<C>,
    sampling: Option<Sampling>,
) -> Result<Leaf, Error> {
    build_with_tamper(
        FriParams::leaf(level),
        n,
        gates,
        sampling,
        Some(initial),
        Tamper::None,
    )
}

/// The logical state from which the segment after `earlier` starts: `|0…0⟩` through each
/// segment of `earlier` in order, each fused on its own ([`crate::exec::execute_from`]). The
/// prover and the verifier of a segment leaf both compute it.
pub fn segment_start(n: usize, earlier: &[Vec<Gate>]) -> Result<Vec<C>, Error> {
    let mut state: Option<Vec<C>> = None;
    for seg in earlier {
        // Fused once, as `build_segment` fuses the segment it proves. Only the state is kept,
        // so a long head costs time but not memory.
        state = Some(run_state(n, &validated_fuse(n, seg)?, state.as_deref()));
    }
    Ok(state.unwrap_or_else(|| {
        let mut zero = vec![(0, 0); 1 << n];
        zero[0] = (S, 0);
        zero
    }))
}

/// An initial state a segment leaf accepts: `2^n` amplitudes in the range a gate's output has
/// (`[−2S, 2S)` per component, as the gate table range-checks), so the field arithmetic stays the
/// integer one.
fn check_initial(n: usize, initial: &[C]) -> Result<(), Error> {
    if initial.len() != 1 << n {
        return Err(Error::InvalidCircuit(format!(
            "initial state of {} amplitudes, expected {}",
            initial.len(),
            1usize << n
        )));
    }
    let ok = |x: i64| (-2 * S..2 * S).contains(&x);
    if let Some(k) = initial.iter().position(|&(re, im)| !ok(re) || !ok(im)) {
        return Err(Error::InvalidCircuit(format!(
            "initial amplitude {k} out of range"
        )));
    }
    Ok(())
}

/// [`build`] for a `sample_counts` leaf: the circuit ends in `sampling`'s measurements, and a
/// proof also proves the counts of `sampling.shots` shots drawn under the seed in its
/// statement (see [`crate::born`]).
pub fn build_sampling(
    level: SecurityLevel,
    n: usize,
    gates: Vec<Gate>,
    sampling: Sampling,
) -> Result<Leaf, Error> {
    build_with_tamper(
        FriParams::leaf(level),
        n,
        gates,
        Some(sampling),
        None,
        Tamper::None,
    )
}

/// [`build`] with explicit FRI parameters (tests use [`FriParams::TESTING`] for speed).
#[cfg(test)]
pub(crate) fn build_with(fri: FriParams, n: usize, gates: Vec<Gate>) -> Result<Leaf, Error> {
    build_with_tamper(fri, n, gates, None, None, Tamper::None)
}

/// A leaf circuit before preparation.
struct Unprepared {
    circuit: p3_circuit::Circuit<EF>,
    schema: StatementSchema,
    /// Fused.
    gates: Vec<Gate>,
    packing: TablePacking,
}

fn construct(
    fri: FriParams,
    n: usize,
    gates: Vec<Gate>,
    sampling: &Option<Sampling>,
    initial: &Option<Vec<C>>,
    tamper: Tamper,
) -> Result<Unprepared, Error> {
    let gates = validated_fuse(n, &gates)?;
    if let Some(s) = &sampling {
        s.validate(n)?;
    }
    if let Some(init) = initial {
        check_initial(n, init)?;
    }
    let rows = rounding_steps(&gates) << (n - 1);
    if rows > MAX_ROWS {
        return Err(Error::InvalidCircuit(format!(
            "{rows} gate rows, supported up to {MAX_ROWS}"
        )));
    }
    let packing = TablePacking::default().with_min_trace_height(fri.min_trace_height());
    let mut b = CircuitBuilder::<EF>::new();
    b.register_npo(SvGatePlugin {
        n,
        gates: gates.clone(),
        sampling: sampling.clone(),
        initial: initial.clone(),
        tamper,
    });
    for p in gate_chunk_plugins() {
        b.register_npo(p);
    }
    for p in sampling_plugins() {
        b.register_npo(p);
    }
    let boundary = if initial.is_some() {
        seg_boundary_plugin()
    } else {
        boundary_plugin()
    };
    for p in [boundary, range_plugin(), digest_plugin(), perm_plugin()] {
        b.register_npo(p);
    }
    let ctx: Vec<_> = (0..4).map(|_| b.public_input()).collect();
    // seed_lo, seed_hi, shots: read by the draw table.
    let reads: Vec<_> = if sampling.is_some() {
        (0..3).map(|_| b.public_input()).collect()
    } else {
        Vec::new()
    };
    const LABELS: [&str; 2 * DIGEST_LEN] = ["d0", "d1", "d2", "d3", "c0", "c1", "c2", "c3"];
    let labels = LABELS[..outputs_len(sampling.is_some())]
        .iter()
        .map(|&l| Some(l))
        .collect();
    let inputs = if reads.is_empty() {
        vec![]
    } else {
        vec![reads.clone()]
    };
    let (_, _, outs) =
        b.push_non_primitive_op_with_outputs(gate_type(), inputs, labels, None, "sv");
    let outs: Vec<_> = outs.into_iter().flatten().collect();
    let (digest, counts) = outs.split_at(DIGEST_LEN);
    let exports: Vec<StatementExport> = ctx
        .iter()
        .chain(digest)
        .chain(&reads)
        .chain(counts)
        .copied()
        .map(StatementExport::Base)
        .collect();
    let schema = b
        .set_statement_exports::<F>(&exports)
        .map_err(|e| Error::InvalidCircuit(format!("{e:?}")))?;
    let circuit = b
        .build()
        .map_err(|e| Error::InvalidCircuit(format!("{e:?}")))?;
    Ok(Unprepared {
        circuit,
        schema,
        gates,
        packing,
    })
}

/// Prepares an [`Unprepared`] leaf with config `$cfg` (a [`Cfg`] or a [`VerifyCfg`]: the same
/// code, for two config types).
macro_rules! prepare {
    ($cfg:expr, $u:expr) => {{
        let u: &Unprepared = $u;
        let preps: Vec<Box<dyn NpoPreprocessor<F>>> = vec![
            Box::new(StatementPreprocessor::new(u.schema.clone())),
            Box::new(SvPreprocessor),
        ];
        let mut builders = vec![Box::new(StatementAirBuilder::<1>::new(u.schema.clone()))
            as Box<dyn NpoAirBuilder<_, 1>>];
        builders.extend(air_builders());
        let mut prover = BatchStarkProver::new($cfg).with_table_packing(u.packing.clone());
        prover.register_table_prover(Box::new(StatementProver::<1>::new(u.schema.clone())));
        for p in table_provers() {
            prover.register_table_prover(p);
        }
        prover
            .prepare_circuit::<EF, 1>(&u.circuit, &preps, &builders, ConstraintProfile::Standard)
            .map_err(|e| Error::InvalidCircuit(format!("{e:?}")))
    }};
}

pub(crate) fn build_with_tamper(
    fri: FriParams,
    n: usize,
    gates: Vec<Gate>,
    sampling: Option<Sampling>,
    initial: Option<Vec<C>>,
    tamper: Tamper,
) -> Result<Leaf, Error> {
    let u = construct(fri, n, gates, &sampling, &initial, tamper)?;
    let prepared = prepare!(fri.config(), &u)?;
    Ok(Leaf {
        prepared,
        circuit: u.circuit,
        schema: u.schema,
        n,
        gates: u.gates,
        sampling,
        initial,
    })
}

/// The verifier of the leaf [`build`] (or [`build_sampling`], with `sampling`) would give,
/// built in less memory: the preprocessed commitment is computed one coset at a time and no
/// proving data is kept (see [`crate::verify_cfg`]). It verifies the same proofs.
pub fn build_verifier(
    level: SecurityLevel,
    n: usize,
    gates: Vec<Gate>,
    sampling: Option<Sampling>,
) -> Result<LeafVerifier, Error> {
    build_segment_verifier(level, n, gates, None, sampling)
}

/// [`build_verifier`] for a segment leaf ([`build_segment`]) from `initial`, or for a leaf
/// from `|0…0⟩` when `None`.
pub fn build_segment_verifier(
    level: SecurityLevel,
    n: usize,
    gates: Vec<Gate>,
    initial: Option<Vec<C>>,
    sampling: Option<Sampling>,
) -> Result<LeafVerifier, Error> {
    let fri = FriParams::leaf(level);
    let u = construct(fri, n, gates, &sampling, &initial, Tamper::None)?;
    let prepared = prepare!(VerifyCfg::new(fri.config()), &u)?;
    Ok(LeafVerifier {
        verifier: Verifier::Coset(prepared.verifier()),
        sampling,
    })
}

/// Checks `n` and the gates, and fuses them. The leaf proves the fused circuit, whose gates
/// pass the same check.
fn validated_fuse(n: usize, gates: &[Gate]) -> Result<Vec<Gate>, Error> {
    if !(1..=MAX_QUBITS).contains(&n) {
        return Err(Error::InvalidCircuit(format!(
            "{n} qubits, supported 1..={MAX_QUBITS}"
        )));
    }
    for g in gates {
        g.validate(n)?;
    }
    let fused = fuse(n, gates);
    for g in &fused {
        g.validate(n)?;
    }
    Ok(fused)
}

/// Fused gates that round: each is one step of `2^(n−1)` gate rows.
fn rounding_steps(fused: &[Gate]) -> usize {
    fused.iter().filter(|g| g.rounds()).count()
}

/// The leaf's gate rows for `gates` on `n` qubits: rounding steps × `2^(n−1)`, the work `W`
/// that sets its proving time and memory. Cheap (no circuit is built). It rejects what
/// [`build`] rejects except more than [`MAX_ROWS`] rows, so a scheduler sees how far over a
/// circuit is. A sampling leaf has further tables this does not count.
pub fn gate_rows(n: usize, gates: &[Gate]) -> Result<usize, Error> {
    let fused = validated_fuse(n, gates)?;
    Ok(rounding_steps(&fused) << (n - 1))
}

/// The final state of `gates` on `n` qubits from `|0…0⟩` when no gate takes a rounding step
/// ([`gate_rows`] is 0): every gate then permutes amplitudes and multiplies them by unit
/// phases, so the state is one basis state `k` times `i^phase`, exactly. Bit `q` of `k` is
/// qubit `q`. `None` when a gate rounds. Rejects what [`gate_rows`] rejects.
///
/// Such a circuit has no leaf (there is nothing to prove a table for); a verifier recomputes
/// its results from this instead.
pub fn monomial_state(n: usize, gates: &[Gate]) -> Result<Option<(usize, u8)>, Error> {
    let fused = validated_fuse(n, gates)?;
    if rounding_steps(&fused) != 0 {
        return Ok(None);
    }
    let frame = crate::exec::plan_fused(n, &fused).frame;
    // Logical k holds i^phase[k] · stored[perm[k]], and the stored vector is still |0…0⟩.
    let k = frame
        .perm
        .iter()
        .position(|&p| p == 0)
        .expect("the frame's perm is a permutation");
    Ok(Some((k, frame.phase[k])))
}

/// An upper estimate of the memory [`build_verifier`] peaks at, in bytes, for a leaf of `rows`
/// gate rows ([`gate_rows`]) on `n` qubits with `shots` (0 for a unitary leaf): 400 bytes per
/// gate row, 600 per basis state, 800 per shot and 16 MiB. Measured peaks (live heap, n = 2 to
/// 16, up to 2^22 rows and 2^16 shots) stay 15–80% below it; at 2^22 rows and n = 16 it is
/// 1.73 GB against 1.45 GB measured. A scheduler divides the memory it can spare by it.
/// Saturates rather than overflow on out-of-range arguments.
pub fn verifier_peak_bytes(n: usize, rows: usize, shots: u64) -> u64 {
    let states = 1u64.checked_shl(n as u32).unwrap_or(u64::MAX);
    (rows as u64)
        .saturating_mul(400)
        .saturating_add(states.saturating_mul(600))
        .saturating_add(shots.saturating_mul(800))
        .saturating_add(16 << 20)
}

/// Gate rows a node budgets for a leaf of `rows` gate rows on `n` qubits: `rows`, plus 3 per
/// basis state above the 2^16 of n = 16. A prover's memory is about 4.7 KB per gate row plus
/// 6.0 KB per basis state (11.5 KB with sampling), so a basis state weighs 1.3 to 2.5 gate rows;
/// up to n = 16 the states fit the fixed part of a node's budget, as they always have.
/// Measured on an 8-core Mac (live heap, normal tier): 8.7 GiB at n = 20 and 2^19 rows, 24.3
/// GiB at 2^22 rows, 29.7 GiB with 1024 shots, against 18.8 GiB at n = 16 and 2^22 rows.
/// Schedulers compare this, not `rows`, with a node's `sv_max_rows`. Saturates.
pub fn effective_rows(n: usize, rows: usize) -> u64 {
    let states = 1u64.checked_shl(n as u32).unwrap_or(u64::MAX);
    (rows as u64).saturating_add(3u64.saturating_mul(states.saturating_sub(1 << 16)))
}

/// Domain tag of [`Dispatch::context`]. Its `V1` versions the context encoding only; it is
/// unrelated to the leaf format's version.
pub const CONTEXT_TAG: &[u8] = b"WQC_SV_CTX_V1";

/// The dispatch fields a leaf proof is bound to, exactly as the orchestrator signed them: the
/// bytes are hashed as given, with no normalization (hex case, an empty versus `"0"` slice).
#[derive(Clone, Copy, Debug)]
pub struct Dispatch<'a> {
    pub circuit_id: &'a str,
    pub sub_task_id: &'a str,
    pub node_id: &'a str,
    pub slice_id: &'a str,
}

impl Dispatch<'_> {
    /// The leaf context: SHA3-256 of [`CONTEXT_TAG`] followed by each field as its byte length
    /// (`u32` little-endian, UTF-8 bytes rather than characters) and its UTF-8 bytes, in the
    /// order `circuit_id`, `sub_task_id`, `node_id`, `slice_id`; the 32-byte hash is split into
    /// four little-endian `u64` words, each reduced modulo the Goldilocks prime.
    ///
    /// The context differs per node, while the digest does not, so a quorum compares the
    /// statement's digest half (`statement[4..]`). The security tier is not included: it is
    /// part of the verifier, not the statement.
    ///
    /// # Panics
    ///
    /// If a field is longer than `u32::MAX` bytes.
    pub fn context(&self) -> [u64; 4] {
        reduce_words(self.context_hash())
    }

    fn context_hash(&self) -> [u8; 32] {
        use sha3::{Digest, Sha3_256};
        let mut h = Sha3_256::new();
        h.update(CONTEXT_TAG);
        for field in [
            self.circuit_id,
            self.sub_task_id,
            self.node_id,
            self.slice_id,
        ] {
            let len =
                u32::try_from(field.len()).expect("dispatch field longer than u32::MAX bytes");
            h.update(len.to_le_bytes());
            h.update(field.as_bytes());
        }
        h.finalize().into()
    }
}

/// Four little-endian `u64` words, each reduced modulo the Goldilocks prime.
pub(crate) fn reduce_words(h: [u8; 32]) -> [u64; 4] {
    std::array::from_fn(|k| {
        let w = u64::from_le_bytes(h[8 * k..8 * k + 8].try_into().expect("8 bytes"));
        w % F::ORDER_U64
    })
}

/// Statement `[context, digest]` from canonical `u64`s; values at or above the field modulus
/// are rejected rather than reduced.
pub fn statement(ctx: [u64; 4], digest: [u64; DIGEST_LEN]) -> Result<Vec<F>, Error> {
    let mut s = canonical(ctx)?.to_vec();
    s.extend(canonical(digest)?);
    Ok(s)
}

/// Sampling statement `[context, digest, seed_lo, seed_hi, shots, counts digest]`, from
/// canonical values like [`statement`].
pub fn sampling_statement(
    ctx: [u64; 4],
    digest: [u64; DIGEST_LEN],
    seed: u64,
    shots: u32,
    counts_digest: [u64; DIGEST_LEN],
) -> Result<Vec<F>, Error> {
    let mut s = statement(ctx, digest)?;
    s.extend(seed_words(seed).map(F::from_u64));
    s.push(F::from_u32(shots));
    s.extend(canonical(counts_digest)?);
    Ok(s)
}

/// Statement words as field elements, rejecting any not below the modulus.
fn canonical<const N: usize>(words: [u64; N]) -> Result<[F; N], Error> {
    let mut out = [F::ZERO; N];
    for (o, &x) in out.iter_mut().zip(&words) {
        if x >= F::ORDER_U64 {
            return Err(Error::InvalidStatement(format!(
                "{x} is not below the field modulus"
            )));
        }
        *o = F::from_u64(x);
    }
    Ok(out)
}

impl Leaf {
    /// Proves the circuit under `ctx` (from [`Dispatch::context`]); the returned statement
    /// holds the terminal digest the circuit exported. A sampling leaf proves with
    /// [`Leaf::prove_sampling`].
    pub fn prove(&self, ctx: [u64; 4]) -> Result<LeafProof, Error> {
        if self.sampling.is_some() {
            return Err(Error::Prove("a sampling leaf needs a seed".into()));
        }
        self.prove_inputs(statement(ctx, [0; DIGEST_LEN])?[..4].to_vec())
    }

    /// Proves a sampling leaf under `ctx` and `seed`; also returns the counts (one per
    /// classical register value, at least four), which the statement binds by their digest.
    pub fn prove_sampling(&self, ctx: [u64; 4], seed: u64) -> Result<(LeafProof, Vec<u64>), Error> {
        let Some(sampling) = &self.sampling else {
            return Err(Error::Prove("not a sampling leaf".into()));
        };
        let mut inputs = statement(ctx, [0; DIGEST_LEN])?[..4].to_vec();
        inputs.extend(seed_words(seed).map(F::from_u64));
        inputs.push(F::from_u32(sampling.shots));
        let proof = self.prove_inputs(inputs)?;
        let plan = plan_fused(self.n, &self.gates);
        let logical = plan
            .frame
            .logical(&run_from(self.n, &plan, self.initial.as_deref()).1);
        let counts = sample(&logical, sampling, seed)?.counts;
        Ok((proof, counts))
    }

    fn prove_inputs(&self, inputs: Vec<F>) -> Result<LeafProof, Error> {
        let mut runner = self.circuit.runner();
        runner
            .set_public_inputs(&inputs)
            .map_err(|e| Error::Prove(format!("{e:?}")))?;
        let traces = runner.run().map_err(|e| Error::Prove(format!("{e:?}")))?;
        let proof = self
            .prepared
            .prove(&traces)
            .map_err(|e| Error::Prove(format!("{e:?}")))?;
        let statement = claimed_statement(&proof)?;
        Ok(LeafProof { proof, statement })
    }

    /// [`LeafVerifier::verify`].
    pub fn verify<'a>(
        &self,
        proof: impl Into<ProofInput<'a>>,
        statement: &[F],
    ) -> Result<(), Error> {
        self.leaf_verifier().verify(proof, statement)
    }

    /// [`LeafVerifier::verify_dispatch`].
    pub fn verify_dispatch<'a>(
        &self,
        proof: impl Into<ProofInput<'a>>,
        dispatch: &Dispatch<'_>,
        digest: [u64; DIGEST_LEN],
    ) -> Result<(), Error> {
        self.leaf_verifier()
            .verify_dispatch(proof, dispatch, digest)
    }

    /// [`LeafVerifier::verify_sampling`].
    pub fn verify_sampling<'a>(
        &self,
        proof: impl Into<ProofInput<'a>>,
        dispatch: &Dispatch<'_>,
        digest: [u64; DIGEST_LEN],
        seed: u64,
        counts: &[u64],
    ) -> Result<(), Error> {
        self.leaf_verifier()
            .verify_sampling(proof, dispatch, digest, seed, counts)
    }

    /// The verifier fixing this circuit's relation and preprocessed commitment.
    pub fn verifier(&self) -> CircuitVerifier<Cfg> {
        self.prepared.verifier()
    }

    /// The leaf's verifier without its proving data, to keep after the leaf is dropped (the
    /// orchestrator caches one per circuit).
    pub fn leaf_verifier(&self) -> LeafVerifier {
        LeafVerifier {
            verifier: Verifier::Leaf(self.prepared.verifier()),
            sampling: self.sampling.clone(),
        }
    }

    pub fn schema(&self) -> &StatementSchema {
        &self.schema
    }
}

/// A leaf's verifier: its circuit's relation and preprocessed commitment, and for a sampling
/// leaf the sampling the statement's counts refer to. It holds no proving data and clones
/// cheaply.
#[derive(Clone)]
pub struct LeafVerifier {
    verifier: Verifier,
    sampling: Option<Sampling>,
}

/// The same relation and commitment, from a proving leaf or from [`build_verifier`].
#[derive(Clone)]
enum Verifier {
    Leaf(CircuitVerifier<Cfg>),
    Coset(CircuitVerifier<VerifyCfg>),
}

/// A proof to verify: decoded, or its bytes ([`encode_proof`]). A verifier from
/// [`build_verifier`] reads bytes directly; given a decoded proof it re-reads its bytes.
#[derive(Clone, Copy)]
pub enum ProofInput<'a> {
    Proof(&'a BatchStarkProof<Cfg>),
    Bytes(&'a [u8]),
}

impl<'a> From<&'a BatchStarkProof<Cfg>> for ProofInput<'a> {
    fn from(p: &'a BatchStarkProof<Cfg>) -> Self {
        Self::Proof(p)
    }
}

impl<'a> From<&'a [u8]> for ProofInput<'a> {
    fn from(b: &'a [u8]) -> Self {
        Self::Bytes(b)
    }
}

impl LeafVerifier {
    /// The sampling of a `sample_counts` leaf, `None` for a unitary one.
    pub fn sampling(&self) -> Option<&Sampling> {
        self.sampling.as_ref()
    }

    /// Verifies `proof` against this circuit and the expected `statement`.
    ///
    /// # Security
    ///
    /// Only an expected statement binds anything: build it from the dispatch the verifier
    /// signed and the digest it expects (a quorum's, or one recomputed from the result), never
    /// from the prover's [`LeafProof::statement`]. [`LeafVerifier::verify_dispatch`] does this.
    pub fn verify<'a>(
        &self,
        proof: impl Into<ProofInput<'a>>,
        statement: &[F],
    ) -> Result<(), Error> {
        let checked = match (&self.verifier, proof.into()) {
            (Verifier::Leaf(v), ProofInput::Proof(p)) => v.verify(p, statement),
            (Verifier::Leaf(v), ProofInput::Bytes(b)) => v.verify(&decode(b)?, statement),
            (Verifier::Coset(v), ProofInput::Bytes(b)) => v.verify(&decode(b)?, statement),
            (Verifier::Coset(v), ProofInput::Proof(p)) => {
                v.verify(&decode(&encode_proof(p))?, statement)
            }
        };
        checked.map_err(|e| Error::Verify(format!("{e:?}")))
    }

    /// Verifies `proof` for `dispatch` with the expected terminal `digest`: [`LeafVerifier::verify`]
    /// against `statement(dispatch.context(), digest)`.
    pub fn verify_dispatch<'a>(
        &self,
        proof: impl Into<ProofInput<'a>>,
        dispatch: &Dispatch<'_>,
        digest: [u64; DIGEST_LEN],
    ) -> Result<(), Error> {
        self.verify(proof, &statement(dispatch.context(), digest)?)
    }

    /// Verifies a sampling leaf's `proof` for `dispatch` with the expected terminal `digest`,
    /// the dispatched `seed`, and the reported `counts`: [`LeafVerifier::verify`] against
    /// [`sampling_statement`] with the circuit's shot count and the counts' digest.
    ///
    /// # Security
    ///
    /// The digest reduces each count mod p, so it binds the counts only as field elements.
    /// The counts must also be canonical: `counts_len` entries, each at most `shots`, summing
    /// to `shots`. This checks that; a caller building the statement itself must too.
    pub fn verify_sampling<'a>(
        &self,
        proof: impl Into<ProofInput<'a>>,
        dispatch: &Dispatch<'_>,
        digest: [u64; DIGEST_LEN],
        seed: u64,
        counts: &[u64],
    ) -> Result<(), Error> {
        let Some(sampling) = &self.sampling else {
            return Err(Error::Verify("not a sampling leaf".into()));
        };
        let s = expected_sampling_statement(sampling, dispatch, digest, seed, counts)?;
        self.verify(proof, &s)
    }
}

/// The statement a sampling leaf of `sampling` must prove for `dispatch`, the expected terminal
/// `digest`, the dispatched `seed` and the reported `counts`, after checking the counts are
/// canonical (see [`LeafVerifier::verify_sampling`]).
pub fn expected_sampling_statement(
    sampling: &Sampling,
    dispatch: &Dispatch<'_>,
    digest: [u64; DIGEST_LEN],
    seed: u64,
    counts: &[u64],
) -> Result<Vec<F>, Error> {
    if counts.len() != sampling.counts_len() {
        return Err(Error::Verify(format!(
            "{} counts, expected {}",
            counts.len(),
            sampling.counts_len()
        )));
    }
    // Checking each count first keeps the sum from overflowing.
    let shots = u64::from(sampling.shots);
    if counts.iter().any(|&c| c > shots) || counts.iter().sum::<u64>() != shots {
        return Err(Error::Verify(format!(
            "counts do not add up to {shots} shots"
        )));
    }
    sampling_statement(
        dispatch.context(),
        digest,
        seed,
        sampling.shots,
        counts_digest(counts),
    )
}

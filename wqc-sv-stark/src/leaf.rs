//! Leaf circuit: build, prove, verify against a `[context, digest]` statement.
//!
//! The circuit (gate list and qubit count) is part of the prepared relation: its preprocessed
//! columns are committed at [`build`] time and every verifier derived from the leaf checks
//! proofs against that commitment. The statement carries only `[context(4), digest(4)]`, so a
//! statement means nothing without the verifier of the circuit it came from.

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

use crate::digest::DIGEST_LEN;
use crate::exec::*;
use crate::npo::*;
use crate::{Cfg, Error, FriParams, SecurityLevel, EF, F, MAX_QUBITS};

/// Statement length: 4 context elements, then the 4-element terminal digest.
pub const STATEMENT_LEN: usize = 4 + DIGEST_LEN;

/// A prepared leaf circuit.
pub struct Leaf {
    prepared: PreparedCircuitProver<Cfg>,
    circuit: p3_circuit::Circuit<EF>,
    schema: StatementSchema,
}

/// A leaf proof with the statement it was proved for.
pub struct LeafProof {
    pub proof: BatchStarkProof<Cfg>,
    pub statement: Vec<F>,
}

/// Builds and prepares the leaf circuit for `gates` on `n` qubits (`1 ≤ n ≤ MAX_QUBITS`) at
/// `level`, which fixes the FRI parameters ([`FriParams::leaf`]) and so the verifier.
pub fn build(level: SecurityLevel, n: usize, gates: Vec<Gate>) -> Result<Leaf, Error> {
    build_with_tamper(FriParams::leaf(level), n, gates, Tamper::None)
}

/// [`build`] with explicit FRI parameters (tests use [`FriParams::TESTING`] for speed).
#[cfg(test)]
pub(crate) fn build_with(fri: FriParams, n: usize, gates: Vec<Gate>) -> Result<Leaf, Error> {
    build_with_tamper(fri, n, gates, Tamper::None)
}

pub(crate) fn build_with_tamper(
    fri: FriParams,
    n: usize,
    gates: Vec<Gate>,
    tamper: Tamper,
) -> Result<Leaf, Error> {
    if !(1..=MAX_QUBITS).contains(&n) {
        return Err(Error::InvalidCircuit(format!(
            "{n} qubits, supported 1..={MAX_QUBITS}"
        )));
    }
    for g in &gates {
        g.validate(n)?;
    }
    // The leaf proves the fused circuit; its gates pass the same check.
    let gates = fuse(n, &gates);
    for g in &gates {
        g.validate(n)?;
    }
    let cfg: Cfg = fri.config();
    let packing = TablePacking::default().with_min_trace_height(fri.min_trace_height());
    let mut b = CircuitBuilder::<EF>::new();
    b.register_npo(SvGatePlugin { n, gates, tamper });
    for p in gate_chunk_plugins() {
        b.register_npo(p);
    }
    for p in [
        boundary_plugin(),
        range_plugin(),
        digest_plugin(),
        perm_plugin(),
    ] {
        b.register_npo(p);
    }
    let ctx: Vec<_> = (0..4).map(|_| b.public_input()).collect();
    let (_, _, outs) = b.push_non_primitive_op_with_outputs(
        gate_type(),
        vec![],
        vec![Some("d0"), Some("d1"), Some("d2"), Some("d3")],
        None,
        "sv",
    );
    let exports: Vec<StatementExport> = ctx
        .iter()
        .copied()
        .chain(outs.into_iter().flatten())
        .map(StatementExport::Base)
        .collect();
    let schema = b
        .set_statement_exports::<F>(&exports)
        .map_err(|e| Error::InvalidCircuit(format!("{e:?}")))?;
    let circuit = b
        .build()
        .map_err(|e| Error::InvalidCircuit(format!("{e:?}")))?;
    let preps: Vec<Box<dyn NpoPreprocessor<F>>> = vec![
        Box::new(StatementPreprocessor::new(schema.clone())),
        Box::new(SvPreprocessor),
    ];
    let mut builders: Vec<Box<dyn NpoAirBuilder<Cfg, 1>>> =
        vec![Box::new(StatementAirBuilder::<1>::new(schema.clone()))];
    builders.extend(air_builders());
    let mut prover = BatchStarkProver::new(cfg).with_table_packing(packing);
    prover.register_table_prover(Box::new(StatementProver::<1>::new(schema.clone())));
    for p in table_provers() {
        prover.register_table_prover(p);
    }
    let prepared = prover
        .prepare_circuit::<EF, 1>(&circuit, &preps, &builders, ConstraintProfile::Standard)
        .map_err(|e| Error::InvalidCircuit(format!("{e:?}")))?;
    Ok(Leaf {
        prepared,
        circuit,
        schema,
    })
}

/// Domain tag of [`context`]; the version changes if the encoding does.
pub const CONTEXT_TAG: &[u8] = b"WQC_SV_CTX_V1";

/// The leaf context: binds a proof to its dispatch. SHA3-256 of [`CONTEXT_TAG`] followed by
/// each field as its byte length (`u32` little-endian) and its UTF-8 bytes, in this order; the
/// 32-byte hash is split into four little-endian `u64` words, each reduced modulo the
/// Goldilocks prime.
///
/// The fields are the dispatch's `circuit_id`, `sub_task_id`, `node_id` and `slice_id`. The
/// context differs per node, while the digest does not, so a quorum compares digests. The
/// security tier is not included: it is part of the verifier, not the statement.
pub fn context(circuit_id: &str, sub_task_id: &str, node_id: &str, slice_id: &str) -> [u64; 4] {
    use sha3::{Digest, Sha3_256};
    let mut h = Sha3_256::new();
    h.update(CONTEXT_TAG);
    for field in [circuit_id, sub_task_id, node_id, slice_id] {
        let len = u32::try_from(field.len()).expect("dispatch field longer than 4 GiB");
        h.update(len.to_le_bytes());
        h.update(field.as_bytes());
    }
    let out = h.finalize();
    std::array::from_fn(|k| {
        let w = u64::from_le_bytes(out[8 * k..8 * k + 8].try_into().expect("8 bytes"));
        w % F::ORDER_U64
    })
}

/// Statement `[context, digest]` from canonical `u64`s; values at or above the field modulus
/// are rejected rather than reduced.
pub fn statement(ctx: [u64; 4], digest: [u64; DIGEST_LEN]) -> Result<Vec<F>, Error> {
    ctx.iter()
        .chain(digest.iter())
        .map(|&x| {
            if x < F::ORDER_U64 {
                Ok(F::from_u64(x))
            } else {
                Err(Error::InvalidStatement(format!(
                    "{x} is not below the field modulus"
                )))
            }
        })
        .collect()
}

impl Leaf {
    /// Proves the circuit under `ctx` (from [`context`]); the returned statement holds the
    /// terminal digest the circuit exported.
    pub fn prove(&self, ctx: [u64; 4]) -> Result<LeafProof, Error> {
        let ctx = statement(ctx, [0; DIGEST_LEN])?[..4].to_vec();
        let mut runner = self.circuit.runner();
        runner
            .set_public_inputs(&ctx)
            .map_err(|e| Error::Prove(format!("{e:?}")))?;
        let traces = runner.run().map_err(|e| Error::Prove(format!("{e:?}")))?;
        let proof = self
            .prepared
            .prove(&traces)
            .map_err(|e| Error::Prove(format!("{e:?}")))?;
        let statement = proof
            .non_primitives
            .iter()
            .find(|e| e.op_type == p3_circuit::ops::NpoTypeId::statement())
            .map(|e| e.public_values.clone())
            .ok_or_else(|| Error::Prove("proof carries no statement table".into()))?;
        Ok(LeafProof { proof, statement })
    }

    /// Verifies `proof` against this circuit and the expected `statement`.
    pub fn verify(&self, proof: &BatchStarkProof<Cfg>, statement: &[F]) -> Result<(), Error> {
        self.prepared
            .verifier()
            .verify(proof, statement)
            .map_err(|e| Error::Verify(format!("{e:?}")))
    }

    /// The verifier fixing this circuit's relation and preprocessed commitment.
    pub fn verifier(&self) -> CircuitVerifier<Cfg> {
        self.prepared.verifier()
    }

    pub fn schema(&self) -> &StatementSchema {
        &self.schema
    }
}

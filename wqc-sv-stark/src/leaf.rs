//! Leaf circuit: build, prove, verify against a `[context, digest]` statement.

use p3_circuit::builder::CircuitBuilder;
use p3_circuit::{StatementExport, StatementSchema};
use p3_circuit_prover::batch_stark_prover::{
    BatchStarkProof, BatchStarkProver, PreparedCircuitProver, TablePacking,
};
use p3_circuit_prover::common::{NpoAirBuilder, NpoPreprocessor};
use p3_circuit_prover::{
    ConstraintProfile, StatementAirBuilder, StatementPreprocessor, StatementProver,
};
use p3_field::PrimeCharacteristicRing;

use crate::exec::*;
use crate::npo::*;
use crate::{Cfg, FriParams, EF, F};

pub struct Leaf {
    pub prepared: PreparedCircuitProver<Cfg>,
    pub circuit: p3_circuit::Circuit<EF>,
    pub schema: StatementSchema,
}

/// Builds and prepares the leaf circuit for `gates` on `n` qubits.
pub fn build(fri: FriParams, n: usize, gates: Vec<Gate>) -> Leaf {
    build_with_tamper(fri, n, gates, Tamper::None)
}

pub(crate) fn build_with_tamper(
    fri: FriParams,
    n: usize,
    gates: Vec<Gate>,
    tamper: Tamper,
) -> Leaf {
    let cfg: Cfg = fri.config();
    let packing = TablePacking::default().with_min_trace_height(fri.min_trace_height());
    let mut b = CircuitBuilder::<EF>::new();
    b.register_npo(SvGatePlugin { n, gates, tamper });
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
        .chain(outs.iter().map(|o| o.unwrap()))
        .map(StatementExport::Base)
        .collect();
    let schema = b.set_statement_exports::<F>(&exports).unwrap();
    let circuit = b.build().unwrap();
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
        .unwrap();
    Leaf {
        prepared,
        circuit,
        schema,
    }
}

pub fn statement(ctx: [u64; 4], digest: [u64; 4]) -> Vec<F> {
    ctx.iter()
        .chain(digest.iter())
        .map(|&x| F::from_u64(x))
        .collect()
}

impl Leaf {
    pub fn prove(&self, ctx: [u64; 4]) -> BatchStarkProof<Cfg> {
        let mut runner = self.circuit.runner();
        runner.set_public_inputs(&ctx.map(F::from_u64)).unwrap();
        self.prepared.prove(&runner.run().unwrap()).unwrap()
    }
    pub fn verify(&self, proof: &BatchStarkProof<Cfg>, st: &[F]) -> Result<(), String> {
        self.prepared
            .verifier()
            .verify(proof, st)
            .map_err(|e| format!("{e:?}"))
    }
}

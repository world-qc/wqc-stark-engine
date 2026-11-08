use p3_field::PrimeCharacteristicRing;

use crate::digest::*;
use crate::exec::*;
use crate::leaf::{statement, Leaf};
use crate::recursion::{leaf_input, stock_backend, WqcBackend};
use crate::{Cfg, FriParams, F};

const CTX: [u64; 4] = [1, 2, 3, 4];

fn gates() -> Vec<Gate> {
    vec![
        Gate::h(0),
        Gate::cnot(0, 1),
        Gate::cnot(1, 2),
        Gate::ry(2, 0.7),
        Gate::rz(1, 1.3),
        Gate::t(0),
        Gate::h(2),
    ]
}

fn leaf(n: usize, gates: Vec<Gate>, tamper: Tamper) -> Leaf {
    crate::leaf::build_with_tamper(FriParams::TESTING, n, gates, tamper)
}

fn honest_digest() -> [u64; 4] {
    terminal_digest(&execute(3, &gates()).1)
}

#[test]
fn honest_verifies_with_ctx_and_digest_statement() {
    let l = leaf(3, gates(), Tamper::None);
    let proof = l.prove(CTX);
    l.verify(&proof, &statement(CTX, honest_digest())).unwrap();
    assert_eq!(
        proof.non_primitives.len(),
        6,
        "statement + five leaf tables"
    );
}

#[test]
fn relabelled_context_is_rejected() {
    let l = leaf(3, gates(), Tamper::None);
    let proof = l.prove(CTX);
    assert!(l
        .verify(&proof, &statement([9, 2, 3, 4], honest_digest()))
        .is_err());
}

#[test]
fn wrong_terminal_digest_is_rejected() {
    let l = leaf(3, gates(), Tamper::None);
    let proof = l.prove(CTX);
    let mut other = execute(3, &gates()).1;
    other[5].1 += 1;
    assert!(l
        .verify(&proof, &statement(CTX, terminal_digest(&other)))
        .is_err());
}

#[test]
fn other_circuit_is_rejected() {
    let l = leaf(3, gates(), Tamper::None);
    let proof = l.prove(CTX);
    let mut g2 = gates();
    g2[3] = Gate::ry(2, 0.71);
    let other = leaf(3, g2, Tamper::None);
    assert!(other
        .verify(&proof, &statement(CTX, honest_digest()))
        .is_err());
}

#[test]
fn forged_traces_are_rejected() {
    for t in [
        Tamper::GateOutput,
        Tamper::ReadMismatch,
        Tamper::Remainder,
        Tamper::DigestSwap,
    ] {
        let l = leaf(3, gates(), t);
        // The statement a forger would claim: the digest the forged execution outputs.
        let mut runner = l.circuit.runner();
        runner.set_public_inputs(&CTX.map(F::from_u64)).unwrap();
        let traces = runner.run().unwrap();
        let proof = l.prepared.prove(&traces).unwrap();
        let st = proof
            .non_primitives
            .iter()
            .find(|e| e.op_type == p3_circuit::ops::NpoTypeId::statement())
            .unwrap()
            .public_values
            .clone();
        let r = l.verify(&proof, &st);
        assert!(r.is_err(), "{t:?} accepted");
    }
}

#[test]
fn recursion_two_layers() {
    use p3_recursion::prelude::*;
    let l = leaf(3, gates(), Tamper::None);
    let proof = l.prove(CTX);
    let verifier = l.prepared.verifier();
    let params = ProveNextLayerParams::default();
    let cfg = FriParams::TESTING.config();
    let backend = WqcBackend::with_statement(l.schema.clone());
    let layer1 = build_and_prove_next_layer::<Cfg, BatchOnly, _, 2>(
        &leaf_input(&proof, verifier.common_data()),
        &cfg,
        &backend,
        &params,
    )
    .unwrap();
    build_and_prove_next_layer::<Cfg, BatchOnly, _, 2>(
        &layer1.into_recursion_input::<BatchOnly>(),
        &cfg,
        &stock_backend(),
        &params,
    )
    .unwrap();
}

#[test]
fn recursion_rejects_forged_leaves() {
    use p3_recursion::prelude::*;
    for t in [Tamper::ReadMismatch, Tamper::Remainder, Tamper::DigestSwap] {
        let l = leaf(3, gates(), t);
        let proof = l.prove(CTX);
        let verifier = l.prepared.verifier();
        let backend = WqcBackend::with_statement(l.schema.clone());
        let r = build_and_prove_next_layer::<Cfg, BatchOnly, _, 2>(
            &leaf_input(&proof, verifier.common_data()),
            &FriParams::TESTING.config(),
            &backend,
            &ProveNextLayerParams::default(),
        );
        assert!(r.is_err(), "{t:?} accepted by recursion");
    }
}

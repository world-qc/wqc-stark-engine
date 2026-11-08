//! Run in release: debug builds assert AIR constraints inside `prove`, so the forgery tests
//! are ignored there.

use p3_field::PrimeCharacteristicRing;

use crate::digest::*;
use crate::exec::*;
use crate::leaf::{build, build_with_tamper, statement, Leaf, LeafProof};
use crate::recursion::{verify, Aggregation, Layer, RecursionProof};
use crate::{Error, FriParams, F, MAX_QUBITS};

const CTX: [u64; 4] = [1, 2, 3, 4];
const FRI: FriParams = FriParams::TESTING;

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

fn leaf(tamper: Tamper) -> Leaf {
    build_with_tamper(FRI, 3, gates(), tamper).unwrap()
}

fn honest_statement() -> Vec<F> {
    statement(CTX, terminal_digest(&execute(3, &gates()).1)).unwrap()
}

fn layer1(l: &Leaf, p: &LeafProof) -> (Layer, RecursionProof) {
    let layer = Layer::over_leaf(l, p, FRI).unwrap();
    let out = layer.prove(&p.proof, &p.statement).unwrap();
    (layer, out)
}

#[test]
fn honest_leaf_exports_the_native_digest() {
    let l = leaf(Tamper::None);
    let p = l.prove(CTX).unwrap();
    assert_eq!(p.statement, honest_statement());
    l.verify(&p.proof, &p.statement).unwrap();
    assert_eq!(
        p.proof.non_primitives.len(),
        6,
        "statement + five leaf tables"
    );
}

/// Pins the digest's Poseidon2 constants (seeded with 7) and sponge layout: a change to either
/// changes what every published digest means.
#[test]
fn bell_state_digest_known_answer() {
    let fin = execute(2, &[Gate::h(0), Gate::cnot(0, 1)]).1;
    assert_eq!(
        terminal_digest(&fin),
        [
            4868592264552318960,
            4278567621881643886,
            15621577778702288575,
            7488096975589155297
        ]
    );
}

#[test]
fn statement_side_mismatches_are_rejected() {
    let l = leaf(Tamper::None);
    let p = l.prove(CTX).unwrap();
    let mut relabelled = p.statement.clone();
    relabelled[0] = F::from_u64(9);
    assert!(l.verify(&p.proof, &relabelled).is_err());
    let mut other = execute(3, &gates()).1;
    other[5].1 += 1;
    let wrong_digest = statement(CTX, terminal_digest(&other)).unwrap();
    assert!(l.verify(&p.proof, &wrong_digest).is_err());
    let mut g2 = gates();
    g2[3] = Gate::ry(2, 0.71);
    let other_circuit = build(FRI, 3, g2).unwrap();
    assert!(other_circuit.verify(&p.proof, &p.statement).is_err());
}

#[test]
#[cfg_attr(debug_assertions, ignore = "release only")]
fn forged_traces_are_rejected() {
    for t in [
        Tamper::GateOutput,
        Tamper::ReadMismatch,
        Tamper::Remainder,
        Tamper::DigestSwap,
    ] {
        let l = leaf(t);
        // The statement a forger claims: the one its forged execution exported.
        let p = l.prove(CTX).unwrap();
        assert!(l.verify(&p.proof, &p.statement).is_err(), "{t:?} accepted");
    }
}

#[test]
fn tampered_table_manifest_is_rejected() {
    let l = leaf(Tamper::None);
    let honest = l.prove(CTX).unwrap();
    let mut dropped = l.prove(CTX).unwrap();
    dropped.proof.non_primitives.pop();
    assert!(l.verify(&dropped.proof, &dropped.statement).is_err());
    let mut swapped = l.prove(CTX).unwrap();
    swapped.proof.non_primitives.swap(1, 2);
    assert!(l.verify(&swapped.proof, &swapped.statement).is_err());
    let mut renamed = l.prove(CTX).unwrap();
    renamed.proof.non_primitives[1].op_type = p3_circuit::ops::NpoTypeId::new("wqc/other");
    assert!(l.verify(&renamed.proof, &renamed.statement).is_err());
    // The trusted recursion layer rejects them too.
    let layer = Layer::over_leaf(&l, &honest, FRI).unwrap();
    for bad in [&dropped, &swapped, &renamed] {
        assert!(layer.prove(&bad.proof, &bad.statement).is_err());
    }
}

#[test]
fn invalid_circuits_are_rejected_at_build() {
    let invalid =
        |n: usize, g: Vec<Gate>| matches!(build(FRI, n, g), Err(Error::InvalidCircuit(_)));
    assert!(invalid(0, vec![]));
    assert!(invalid(MAX_QUBITS + 1, vec![]));
    assert!(invalid(1, vec![Gate::h(1)]));
    assert!(invalid(2, vec![Gate::cnot(2, 0)]));
    assert!(invalid(2, vec![Gate::cnot(1, 1)]));
    assert!(invalid(
        3,
        vec![Gate::new(
            0,
            vec![1, 1],
            [(1.0, 0.0), (0.0, 0.0), (0.0, 0.0), (1.0, 0.0)]
        )]
    ));
    assert!(invalid(
        1,
        vec![Gate::new(
            0,
            vec![],
            [(2.0, 0.0), (0.0, 0.0), (0.0, 0.0), (1.0, 0.0)]
        )]
    ));
}

#[test]
fn non_canonical_statement_values_are_rejected() {
    let p = <F as p3_field::PrimeField64>::ORDER_U64;
    assert!(statement([p, 0, 0, 0], [0; 4]).is_err());
    assert!(statement([0; 4], [0, 0, 0, u64::MAX]).is_err());
    assert!(statement([p - 1, 0, 0, 0], [0; 4]).is_ok());
}

#[test]
fn proof_codec_roundtrip() {
    let l = leaf(Tamper::None);
    let p = l.prove(CTX).unwrap();
    let bytes = postcard::to_allocvec(&p.proof).unwrap();
    let back = postcard::from_bytes(&bytes).unwrap();
    l.verify(&back, &p.statement).unwrap();
}

#[test]
fn recursion_layers_verify_against_the_leaf_statement() {
    let l = leaf(Tamper::None);
    let p = l.prove(CTX).unwrap();
    let (layer, r1) = layer1(&l, &p);
    verify(&layer.verifier(), &r1.proof, &p.statement).unwrap();
    let mut wrong = p.statement.clone();
    wrong[4] += F::ONE;
    assert!(verify(&layer.verifier(), &r1.proof, &wrong).is_err());

    let layer2 = Layer::over_layer(layer.verifier(), &r1, FRI).unwrap();
    let r2 = layer2.prove(&r1.proof, &r1.statement).unwrap();
    verify(&layer2.verifier(), &r2.proof, &p.statement).unwrap();
}

#[test]
fn aggregation_verifies_against_left_then_right() {
    let l = leaf(Tamper::None);
    let (pa, pb) = (l.prove(CTX).unwrap(), l.prove([5, 6, 7, 8]).unwrap());
    let layer = Layer::over_leaf(&l, &pa, FRI).unwrap();
    let ra = layer.prove(&pa.proof, &pa.statement).unwrap();
    let rb = layer.prove(&pb.proof, &pb.statement).unwrap();
    let agg = Aggregation::new((layer.verifier(), &ra), (layer.verifier(), &rb), FRI).unwrap();
    let root = agg.prove(&ra, &rb).unwrap();
    let both: Vec<F> = pa.statement.iter().chain(&pb.statement).copied().collect();
    assert_eq!(root.statement, both);
    verify(&agg.verifier(), &root.proof, &both).unwrap();
    let swapped: Vec<F> = pb.statement.iter().chain(&pa.statement).copied().collect();
    assert!(verify(&agg.verifier(), &root.proof, &swapped).is_err());
}

#[test]
fn recursion_rejects_another_circuits_leaf() {
    let l = leaf(Tamper::None);
    let p = l.prove(CTX).unwrap();
    let layer = Layer::over_leaf(&l, &p, FRI).unwrap();
    let mut g2 = gates();
    g2[3] = Gate::ry(2, 0.71);
    let other = build(FRI, 3, g2).unwrap().prove(CTX).unwrap();
    assert!(layer.prove(&other.proof, &other.statement).is_err());
}

#[test]
#[cfg_attr(debug_assertions, ignore = "release only")]
fn recursion_rejects_forged_leaves() {
    let l = leaf(Tamper::None);
    let honest = l.prove(CTX).unwrap();
    let layer = Layer::over_leaf(&l, &honest, FRI).unwrap();
    for t in [
        Tamper::GateOutput,
        Tamper::ReadMismatch,
        Tamper::Remainder,
        Tamper::DigestSwap,
    ] {
        let forged = leaf(t).prove(CTX).unwrap();
        assert!(
            layer.prove(&forged.proof, &forged.statement).is_err(),
            "{t:?} accepted by recursion"
        );
    }
}

#[test]
#[cfg_attr(debug_assertions, ignore = "release only")]
fn eight_qubit_smoke() {
    let n = 8;
    let g: Vec<Gate> = (0..32)
        .map(|k| match k % 4 {
            0 => Gate::h(k % n),
            1 => Gate::cnot(k % n, (k + 1) % n),
            2 => Gate::ry(k % n, 0.1 * k as f64),
            _ => Gate::t(k % n),
        })
        .collect();
    let l = build(FRI, n, g.clone()).unwrap();
    let p = l.prove(CTX).unwrap();
    assert_eq!(
        p.statement,
        statement(CTX, terminal_digest(&execute(n, &g).1)).unwrap()
    );
    l.verify(&p.proof, &p.statement).unwrap();
}

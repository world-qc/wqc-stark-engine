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
    let matrix = |m: [(f64, f64); 4]| Gate::from_f64(0, vec![], m);
    let id = [(1.0, 0.0), (0.0, 0.0), (0.0, 0.0), (1.0, 0.0)];
    assert!(invalid(3, vec![Gate::from_f64(0, vec![1, 1], id)]));
    assert!(invalid(
        1,
        vec![matrix([(2.0, 0.0), (0.0, 0.0), (0.0, 0.0), (1.0, 0.0)])]
    ));
    // Not unitary, though every entry is at most 1: a short column, then unit columns that
    // are not orthogonal (real and imaginary inner product).
    assert!(invalid(
        1,
        vec![matrix([(1.0, 0.0), (0.0, 0.0), (0.0, 0.0), (0.5, 0.0)])]
    ));
    assert!(invalid(
        1,
        vec![matrix([(1.0, 0.0), (1.0, 0.0), (0.0, 0.0), (0.0, 0.0)])]
    ));
    let r = std::f64::consts::FRAC_1_SQRT_2;
    assert!(invalid(
        1,
        vec![matrix([(r, 0.0), (0.0, r), (r, 0.0), (0.0, r)])]
    ));
    // A non-finite entry rounds to 0 instead of saturating, and is rejected without panic.
    assert!(invalid(
        1,
        vec![matrix([
            (f64::NEG_INFINITY, 0.0),
            (0.0, 0.0),
            (0.0, 0.0),
            (1.0, 0.0)
        ])]
    ));
    // A NaN or infinite angle gives NaN entries, hence the zero matrix.
    assert!(invalid(1, vec![Gate::rx(0, f64::NAN)]));
    assert!(invalid(1, vec![Gate::rz(0, f64::INFINITY)]));
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

/// wqc-core's gate set, applied with the formulas of its dense engine (`tn/dense.rs`). This is
/// a copy (wqc-core is meant to depend on this crate, so it cannot be imported here), and it
/// does not follow changes to the core by itself: a change there must be mirrored here.
#[derive(Clone, Copy)]
enum CoreGate {
    H(usize),
    X(usize),
    Y(usize),
    Z(usize),
    T(usize),
    S(usize),
    Cnot(usize, usize),
    Cz(usize, usize),
    Rx(usize, f64),
    Ry(usize, f64),
    Rz(usize, f64),
    Ccnot(usize, usize, usize),
}

type Cx = (f64, f64);

fn cmul(a: Cx, b: Cx) -> Cx {
    (a.0 * b.0 - a.1 * b.1, a.0 * b.1 + a.1 * b.0)
}

fn cadd(a: Cx, b: Cx) -> Cx {
    (a.0 + b.0, a.1 + b.1)
}

fn core_apply(st: &mut [Cx], g: CoreGate) {
    let unary = |st: &mut [Cx], t: usize, ctrl: &[usize], f: &dyn Fn(Cx, Cx) -> (Cx, Cx)| {
        for j in 0..st.len() {
            if (j >> t) & 1 == 0 && ctrl.iter().all(|&c| (j >> c) & 1 == 1) {
                let (a, b) = f(st[j], st[j | (1 << t)]);
                st[j] = a;
                st[j | (1 << t)] = b;
            }
        }
    };
    let r = std::f64::consts::FRAC_1_SQRT_2;
    let i = (0.0, 1.0);
    let neg = |a: Cx| (-a.0, -a.1);
    match g {
        CoreGate::H(t) => unary(st, t, &[], &|a, b| {
            (cmul(cadd(a, b), (r, 0.0)), cmul(cadd(a, neg(b)), (r, 0.0)))
        }),
        CoreGate::X(t) => unary(st, t, &[], &|a, b| (b, a)),
        CoreGate::Y(t) => unary(st, t, &[], &|a, b| (cmul(b, neg(i)), cmul(a, i))),
        CoreGate::Z(t) => unary(st, t, &[], &|a, b| (a, neg(b))),
        CoreGate::S(t) => unary(st, t, &[], &|a, b| (a, cmul(b, i))),
        CoreGate::T(t) => unary(st, t, &[], &|a, b| (a, cmul(b, (r, r)))),
        CoreGate::Cnot(c, t) => unary(st, t, &[c], &|a, b| (b, a)),
        CoreGate::Cz(c, t) => unary(st, t, &[c], &|a, b| (a, neg(b))),
        CoreGate::Rx(t, th) => {
            let (s, c) = (th / 2.0).sin_cos();
            unary(st, t, &[], &|a, b| {
                (
                    cadd(cmul(a, (c, 0.0)), cmul(b, (0.0, -s))),
                    cadd(cmul(a, (0.0, -s)), cmul(b, (c, 0.0))),
                )
            })
        }
        CoreGate::Ry(t, th) => {
            let (s, c) = (th / 2.0).sin_cos();
            unary(st, t, &[], &|a, b| {
                (
                    cadd(cmul(a, (c, 0.0)), cmul(b, (-s, 0.0))),
                    cadd(cmul(a, (s, 0.0)), cmul(b, (c, 0.0))),
                )
            })
        }
        CoreGate::Rz(t, th) => {
            let (s, c) = (th / 2.0).sin_cos();
            unary(st, t, &[], &|a, b| (cmul(a, (c, -s)), cmul(b, (c, s))))
        }
        CoreGate::Ccnot(c1, c2, t) => unary(st, t, &[c1, c2], &|a, b| (b, a)),
    }
}

fn to_leaf(g: CoreGate) -> Gate {
    match g {
        CoreGate::H(t) => Gate::h(t),
        CoreGate::X(t) => Gate::x(t),
        CoreGate::Y(t) => Gate::y(t),
        CoreGate::Z(t) => Gate::z(t),
        CoreGate::T(t) => Gate::t(t),
        CoreGate::S(t) => Gate::s(t),
        CoreGate::Cnot(c, t) => Gate::cnot(c, t),
        CoreGate::Cz(c, t) => Gate::cz(c, t),
        CoreGate::Rx(t, th) => Gate::rx(t, th),
        CoreGate::Ry(t, th) => Gate::ry(t, th),
        CoreGate::Rz(t, th) => Gate::rz(t, th),
        CoreGate::Ccnot(c1, c2, t) => Gate::ccnot(c1, c2, t),
    }
}

/// Every gate, with controls on both sides of the target, so a phase or orientation mismatch
/// with the core shows up in the final state.
fn all_gates() -> Vec<CoreGate> {
    use CoreGate::*;
    vec![
        H(0),
        H(1),
        H(2),
        Rx(0, 0.37),
        Ry(1, -1.1),
        Rz(2, 2.3),
        Y(0),
        S(1),
        T(2),
        Cnot(2, 0),
        Cz(0, 2),
        Ccnot(0, 2, 1),
        Z(1),
        X(2),
        Ccnot(2, 1, 0),
        Rx(2, -2.9),
        S(0),
        T(1),
        Y(2),
        Cnot(0, 1),
        Cz(1, 0),
    ]
}

/// Each gate once, after a preparation that leaves a generic state, so even a global-phase
/// mismatch with the core (which changes the digest) shows up; a gate appearing twice could
/// cancel its own phase error.
#[test]
fn every_gate_matches_the_core_engine() {
    use CoreGate::*;
    let scale = crate::exec::S as f64;
    let n = 3;
    let prep = [
        H(0),
        H(1),
        H(2),
        Ry(0, 0.3),
        Rx(1, 0.7),
        Rz(2, 1.1),
        Cnot(0, 2),
    ];
    for (k, g) in all_gates().into_iter().enumerate() {
        let core: Vec<CoreGate> = prep.iter().copied().chain([g]).collect();
        let mut reference = vec![(0.0, 0.0); 1 << n];
        reference[0] = (1.0, 0.0);
        for &c in &core {
            core_apply(&mut reference, c);
        }
        let fixed = execute(n, &core.iter().map(|&c| to_leaf(c)).collect::<Vec<_>>()).1;
        let err = fixed
            .iter()
            .zip(&reference)
            .map(|(a, b)| {
                (a.0 as f64 / scale - b.0)
                    .abs()
                    .max((a.1 as f64 / scale - b.1).abs())
            })
            .fold(0.0, f64::max);
        assert!(
            err < 1e-6,
            "gate {k} of all_gates() drifts from the core engine by {err}"
        );
    }
}

#[test]
#[cfg_attr(debug_assertions, ignore = "release only")]
fn every_gate_proves_and_verifies() {
    let gates: Vec<Gate> = all_gates().into_iter().map(to_leaf).collect();
    let l = build(FRI, 3, gates.clone()).unwrap();
    let p = l.prove(CTX).unwrap();
    assert_eq!(
        p.statement,
        statement(CTX, terminal_digest(&execute(3, &gates).1)).unwrap()
    );
    l.verify(&p.proof, &p.statement).unwrap();
}

//! Run in release: debug builds assert AIR constraints inside `prove`, so the forgery tests
//! are ignored there.

use p3_field::PrimeCharacteristicRing;

use crate::digest::*;
use crate::exec::*;
use crate::leaf::{
    build, build_with, build_with_tamper, reduce_words, statement, Dispatch, Leaf, LeafProof,
    STATEMENT_LEN,
};
use crate::recursion::{verify, Aggregation, Layer, RecursionProof};
use crate::{Error, FriParams, SecurityLevel, F, MAX_QUBITS};

const CTX: [u64; 4] = [1, 2, 3, 4];
const FRI: FriParams = FriParams::TESTING;

fn gates() -> Vec<Gate> {
    vec![
        Gate::h(0),
        Gate::cnot(0, 1),
        Gate::cnot(1, 2),
        Gate::ry(2, 0.7),
        Gate::cnot(2, 0),
        Gate::rz(1, 1.3),
        Gate::t(0),
        Gate::h(2),
    ]
}

fn leaf(tamper: Tamper) -> Leaf {
    build_with_tamper(FRI, 3, gates(), None, tamper).unwrap()
}

fn honest_statement() -> Vec<F> {
    statement(CTX, terminal_digest(&execute(3, &gates()).1)).unwrap()
}

fn layer1(l: &Leaf, p: &LeafProof) -> (Layer, RecursionProof) {
    let layer = Layer::over_leaf_with(l, p, FRI).unwrap();
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
        7,
        "statement + boundary, range, digest, perm + the two non-empty gate tables (4 + 1 steps)"
    );
}

/// Pins the digest's Poseidon2 constants (seeded with 7), sponge layout and the fixed-point
/// arithmetic (scale, rounding): a change to any changes what every published digest means.
#[test]
fn bell_state_digest_known_answer() {
    let fin = execute(2, &[Gate::h(0), Gate::cnot(0, 1)]).1;
    assert_eq!(
        terminal_digest(&fin),
        [
            14306323836031323521,
            6475076262719947663,
            3943220118981982523,
            6299049981826024799
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
    let other_circuit = build_with(FRI, 3, g2).unwrap();
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
    let layer = Layer::over_leaf_with(&l, &honest, FRI).unwrap();
    for bad in [&dropped, &swapped, &renamed] {
        assert!(layer.prove(&bad.proof, &bad.statement).is_err());
    }
}

#[test]
fn invalid_circuits_are_rejected_at_build() {
    let invalid =
        |n: usize, g: Vec<Gate>| matches!(build_with(FRI, n, g), Err(Error::InvalidCircuit(_)));
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
    use crate::leaf::{decode_proof, encode_proof};
    let l = leaf(Tamper::None);
    let p = l.prove(CTX).unwrap();
    let mut bytes = encode_proof(&p.proof);
    let back = decode_proof(&bytes).unwrap();
    // The verifier outlives the leaf and its proving data.
    let v = l.leaf_verifier();
    drop(l);
    v.verify(&back, &p.statement).unwrap();
    assert!(v.sampling().is_none());
    bytes.push(0);
    assert!(decode_proof(&bytes).is_err());
    assert!(decode_proof(&bytes[..bytes.len() / 2]).is_err());
}

/// `gate_rows` counts `2^(n−1)` rows per fused gate that rounds, without building.
#[test]
fn gate_rows_count_rounding_steps() {
    use crate::leaf::gate_rows;
    let cases: [(usize, Vec<Gate>, usize); 6] = [
        (4, vec![], 0),
        (4, vec![Gate::h(0)], 1),
        // Monomial gates fold into the frame.
        (
            4,
            vec![Gate::x(0), Gate::cnot(0, 1), Gate::cz(1, 2), Gate::s(3)],
            0,
        ),
        // A run of single-qubit gates fuses into one; H·H fuses to the identity.
        (4, vec![Gate::h(0), Gate::t(0), Gate::rz(0, 0.3)], 1),
        (4, vec![Gate::h(0), Gate::h(0)], 0),
        // The CNOT flushes the pending H, so the second H is another step.
        (4, vec![Gate::h(0), Gate::cnot(0, 1), Gate::h(0)], 2),
    ];
    for (n, g, steps) in cases {
        assert_eq!(gate_rows(n, &g).unwrap(), steps << (n - 1), "{g:?}");
    }
    let g = gates();
    assert_eq!(
        gate_rows(3, &g).unwrap(),
        plan(3, &g).steps << 2,
        "matches the executor's plan"
    );
    assert!(gate_rows(0, &[]).is_err());
    assert!(gate_rows(MAX_QUBITS + 1, &[]).is_err());
    assert!(gate_rows(2, &[Gate::h(2)]).is_err());
    assert!(gate_rows(2, &[Gate::rx(0, f64::NAN)]).is_err());
}

/// `build` refuses more than `MAX_ROWS` gate rows before preparing anything; `gate_rows`
/// still reports them.
#[test]
fn build_rejects_too_many_rows() {
    use crate::leaf::gate_rows;
    use crate::MAX_ROWS;
    let n = MAX_QUBITS;
    let steps = (MAX_ROWS >> (n - 1)) + 1;
    let g: Vec<Gate> = (0..steps)
        .flat_map(|_| [Gate::h(0), Gate::cnot(0, 1)])
        .collect();
    assert_eq!(gate_rows(n, &g).unwrap(), steps << (n - 1));
    let Err(Error::InvalidCircuit(m)) = build(SecurityLevel::Low, n, g) else {
        panic!("built a leaf over the row limit");
    };
    assert!(m.contains("gate rows"), "{m}");
}

/// The wire circuit is wqc-core's gate JSON and gives the same gates.
#[test]
fn wire_circuit_matches_core_gates() {
    use crate::born::Measure;
    use crate::wire::parse_circuit;
    let json = r#"[{"type":"H","params":0},{"type":"CNOT","params":[0,1]},
        {"type":"CNOT","params":[1,2]},{"type":"RY","params":[2,0.7]},
        {"type":"CNOT","params":[2,0]},{"type":"RZ","params":[1,1.3]},
        {"type":"T","params":0},{"type":"H","params":2},
        {"type":"MEASURE","params":{"qubit":2,"cbit":0}},
        {"type":"MEASURE","params":{"qubit":0,"cbit":1}}]"#;
    let c = parse_circuit(json).unwrap();
    assert_eq!(execute(3, &c.gates).1, execute(3, &gates()).1);
    assert_eq!(
        c.measures,
        [Measure { qubit: 2, cbit: 0 }, Measure { qubit: 0, cbit: 1 }]
    );
    let all = r#"[{"type":"X","params":0},{"type":"Y","params":1},{"type":"Z","params":2},
        {"type":"S","params":0},{"type":"CZ","params":[0,1]},{"type":"RX","params":[1,-0.25]},
        {"type":"CCNOT","params":[0,1,2]}]"#;
    let want = [
        Gate::x(0),
        Gate::y(1),
        Gate::z(2),
        Gate::s(0),
        Gate::cz(0, 1),
        Gate::rx(1, -0.25),
        Gate::ccnot(0, 1, 2),
    ];
    assert_eq!(
        execute(3, &parse_circuit(all).unwrap().gates).1,
        execute(3, &want).1
    );
    // An angle reads to the exact f64 Go marshals (shortest round-trip digits).
    let a = 0.1f64 + 0.2;
    let c = parse_circuit(&format!(r#"[{{"type":"RZ","params":[0,{a}]}}]"#)).unwrap();
    assert_eq!(execute(1, &c.gates).1, execute(1, &[Gate::rz(0, a)]).1);
    for bad in [
        r#"[{"type":"RESET","params":0}]"#,
        r#"[{"type":"IF","params":{"cbit":0,"value":1,"gate":{"type":"X","params":0}}}]"#,
        r#"[{"type":"MEASURE","params":{"qubit":0,"cbit":0}},{"type":"H","params":0}]"#,
        r#"[{"type":"U3","params":[0,1,2,3]}]"#,
        r#"[{"type":"H","params":[0,1]}]"#,
        r#"{"type":"H","params":0}"#,
    ] {
        assert!(parse_circuit(bad).is_err(), "{bad}");
    }
}

/// Counts JSON round-trips through the canonical form, and only that form is accepted.
#[test]
fn wire_counts_are_canonical() {
    use crate::born::{Measure, Sampling};
    use crate::wire::{counts_json, parse_counts};
    let s = Sampling {
        measures: vec![Measure { qubit: 0, cbit: 0 }],
        cbits: 3,
        shots: 10,
    };
    let counts = vec![4, 0, 0, 1, 0, 0, 5, 0];
    let json = counts_json(&counts, 3);
    assert_eq!(json, r#"{"counts":{"000":4,"011":1,"110":5},"shots":10}"#);
    assert_eq!(parse_counts(&json, &s).unwrap(), counts);
    // One cbit still pads the vector to four entries.
    let one = Sampling {
        cbits: 1,
        ..s.clone()
    };
    assert_eq!(
        parse_counts(r#"{"counts":{"0":3,"1":7},"shots":10}"#, &one).unwrap(),
        [3, 7, 0, 0]
    );
    for bad in [
        r#"{"counts":{"000":4,"011":1,"110":5},"shots":11}"#,
        r#"{"counts":{"000":4,"011":1,"110":4},"shots":10}"#,
        r#"{"counts":{"000":4,"011":1,"110":5,"111":0},"shots":10}"#,
        r#"{"counts":{"00":4,"011":1,"110":5},"shots":10}"#,
        r#"{"counts":{"000":4,"012":1,"110":5},"shots":10}"#,
        r#"{"counts":{"000":4,"+11":1,"110":5},"shots":10}"#,
        r#"{"counts":{"000":4,"011":1,"110":18446744073709551615},"shots":10}"#,
        r#"{"counts":{"000":10},"shots":10,"seed":1}"#,
        r#"{"counts":{"000":10}}"#,
        // Same counts, not the canonical bytes.
        r#"{"counts":{"110":5,"000":4,"011":1},"shots":10}"#,
        r#"{"counts": {"000":4,"011":1,"110":5},"shots":10}"#,
        r#"{"shots":10,"counts":{"000":4,"011":1,"110":5}}"#,
        r#"{"counts":{"000":4,"011":1,"110":5,"110":5},"shots":10}"#,
        r#"{"counts":{"000":4,"011":1,"110":05},"shots":10}"#,
    ] {
        assert!(parse_counts(bad, &s).is_err(), "{bad}");
    }
    // A sampling out of range is refused rather than sized.
    assert!(parse_counts(
        &json,
        &Sampling {
            cbits: 64,
            ..s.clone()
        }
    )
    .is_err());
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

    let layer2 = Layer::over_layer_with(layer.verifier(), &r1, FRI).unwrap();
    let r2 = layer2.prove(&r1.proof, &r1.statement).unwrap();
    verify(&layer2.verifier(), &r2.proof, &p.statement).unwrap();
}

#[test]
fn aggregation_verifies_against_left_then_right() {
    let l = leaf(Tamper::None);
    let (pa, pb) = (l.prove(CTX).unwrap(), l.prove([5, 6, 7, 8]).unwrap());
    let layer = Layer::over_leaf_with(&l, &pa, FRI).unwrap();
    let ra = layer.prove(&pa.proof, &pa.statement).unwrap();
    let rb = layer.prove(&pb.proof, &pb.statement).unwrap();
    let agg = Aggregation::new_with((layer.verifier(), &ra), (layer.verifier(), &rb), FRI).unwrap();
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
    let layer = Layer::over_leaf_with(&l, &p, FRI).unwrap();
    let mut g2 = gates();
    g2[3] = Gate::ry(2, 0.71);
    let other = build_with(FRI, 3, g2).unwrap().prove(CTX).unwrap();
    assert!(layer.prove(&other.proof, &other.statement).is_err());
}

#[test]
#[cfg_attr(debug_assertions, ignore = "release only")]
fn recursion_rejects_forged_leaves() {
    let l = leaf(Tamper::None);
    let honest = l.prove(CTX).unwrap();
    let layer = Layer::over_leaf_with(&l, &honest, FRI).unwrap();
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
    let l = build_with(FRI, n, g.clone()).unwrap();
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
    let l = build_with(FRI, 3, gates.clone()).unwrap();
    let p = l.prove(CTX).unwrap();
    assert_eq!(
        p.statement,
        statement(CTX, terminal_digest(&execute(3, &gates).1)).unwrap()
    );
    l.verify(&p.proof, &p.statement).unwrap();
}

/// The L2 distance from the ideal state grows by at most `ρ + ‖M̃ − U‖·‖ψ̃‖` per gate, where
/// `ρ = √(2^(n+1))·2^-(LOG_S+1)` is the output rounding and `‖M̃ − U‖ ≤ √8·2^-(LOG_S+1)` the
/// matrix quantization; `‖ψ̃‖ ≤ 2` is generous.
#[test]
fn rounding_error_stays_within_the_bound() {
    use CoreGate::*;
    let (n, count) = (10usize, 400usize);
    let mut seed = 0x9E37_79B9_7F4A_7C15u64;
    let mut next = move || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };
    let circuit: Vec<CoreGate> = (0..count)
        .map(|_| {
            let t = (next() % n as u64) as usize;
            let c = (t + 1 + (next() % (n as u64 - 1)) as usize) % n;
            let th = ((next() % 10_000) as f64 / 10_000.0 - 0.5) * std::f64::consts::TAU;
            match next() % 12 {
                0 => H(t),
                1 => X(t),
                2 => Y(t),
                3 => Z(t),
                4 => S(t),
                5 => T(t),
                6 => Cnot(c, t),
                7 => Cz(c, t),
                8 => Ccnot(c, (c + 1 + (c + 1 == t) as usize) % n, t),
                9 => Rx(t, th),
                10 => Ry(t, th),
                _ => Rz(t, th),
            }
        })
        .filter(|g| !matches!(*g, Ccnot(c1, c2, t) if c1 == t || c2 == t || c1 == c2))
        .collect();
    let mut reference = vec![(0.0, 0.0); 1 << n];
    reference[0] = (1.0, 0.0);
    for &g in &circuit {
        core_apply(&mut reference, g);
    }
    let fixed = execute(n, &circuit.iter().map(|&g| to_leaf(g)).collect::<Vec<_>>()).1;
    let scale = crate::exec::S as f64;
    let err = fixed
        .iter()
        .zip(&reference)
        .map(|(a, b)| (a.0 as f64 / scale - b.0).powi(2) + (a.1 as f64 / scale - b.1).powi(2))
        .sum::<f64>()
        .sqrt();
    let ulp = 0.5 / scale;
    // Fused gates count once.
    let gates: Vec<Gate> = circuit.iter().map(|&g| to_leaf(g)).collect();
    let fused = fuse(n, &gates).len();
    assert!(fused < circuit.len());
    let bound = fused as f64 * ((2f64.powi(n as i32 + 1)).sqrt() + 2.0 * 8f64.sqrt()) * ulp;
    assert!(circuit.len() > count * 9 / 10);
    eprintln!("L2 error {err:.2e}, bound {bound:.2e}");
    assert!(err <= bound, "L2 error {err} above the bound {bound}");
    // Sanity check, not a theorem: nearest rounding is unbiased, so the error walks rather
    // than drifts and lands far inside the bound. The margin is empirical for this fixed
    // circuit; revisit it if the generator or gate mix changes.
    assert!(err <= bound / 20.0, "L2 error {err} vs bound {bound}");
}

/// Pins the rotation quantization: entries come from the pinned `libm`, and a change there
/// would change the circuit every party derives.
#[test]
fn rotation_matrices_known_answer() {
    let ms: Vec<_> = [Gate::rx(0, 0.37), Gate::ry(0, -1.1), Gate::rz(0, 2.3)]
        .into_iter()
        .map(|g| g.m)
        .collect();
    assert_eq!(
        ms,
        vec![
            [
                (263854941, 0),
                (0, -49377772),
                (0, -49377772),
                (263854941, 0)
            ],
            [
                (228847809, 0),
                (140307785, 0),
                (-140307785, 0),
                (228847809, 0)
            ],
            [
                (109652512, -245018205),
                (0, 0),
                (0, 0),
                (109652512, 245018205)
            ],
        ]
    );
}

#[test]
fn tiers_map_to_leaf_parameters() {
    use SecurityLevel::*;
    let leaf = |l| FriParams::leaf(l);
    assert_eq!(
        [Low, Normal, High, Ultra].map(|l| leaf(l).num_queries),
        [22, 32, 37, 42]
    );
    assert_eq!(
        [Low, Normal, High, Ultra].map(|l| leaf(l).conjectured_bits()),
        [60, 80, 90, 100]
    );
    for l in [Low, Normal, High, Ultra] {
        // Rate and PoW are shared, so prove cost is (nearly) the same at every tier.
        assert_eq!((leaf(l).log_blowup, leaf(l).query_pow_bits), (2, 16));
        // The built-in descriptor accepts every tier.
        let _ = leaf(l).config();
    }
    assert_eq!(FriParams::RECURSION.conjectured_bits(), 100);
    let _ = FriParams::RECURSION.config();
}

/// Trimmed and case-insensitive like v1; empty is `ultra`; unknown names are rejected rather
/// than falling back as v1 does.
#[test]
fn security_level_names_parse_like_v1() {
    use SecurityLevel::*;
    let cases = [
        ("low", Some(Low)),
        (" Normal ", Some(Normal)),
        ("HIGH", Some(High)),
        ("ultra", Some(Ultra)),
        ("", Some(Ultra)),
        ("  ", Some(Ultra)),
        ("medium", None),
    ];
    for (name, want) in cases {
        assert_eq!(SecurityLevel::parse(name), want, "{name:?}");
    }
}

/// A tier is part of the leaf's verifier: a proof verifies only at the tier it was proved at.
/// The public recursion constructors (fixed `RECURSION` parameters) take leaves of any tier, up
/// to an aggregation; an `ultra` leaf proves too.
#[test]
#[cfg_attr(debug_assertions, ignore = "release only")]
fn a_leaf_verifies_only_at_its_own_tier() {
    let low = build(SecurityLevel::Low, 3, gates()).unwrap();
    let normal = build(SecurityLevel::Normal, 3, gates()).unwrap();
    let p = low.prove(CTX).unwrap();
    low.verify(&p.proof, &p.statement).unwrap();
    assert!(normal.verify(&p.proof, &p.statement).is_err());

    let ultra = build(SecurityLevel::Ultra, 3, gates()).unwrap();
    let u = ultra.prove([5, 6, 7, 8]).unwrap();
    ultra.verify(&u.proof, &u.statement).unwrap();
    assert!(normal.verify(&u.proof, &u.statement).is_err());

    let low_layer = Layer::over_leaf(&low, &p).unwrap();
    let ultra_layer = Layer::over_leaf(&ultra, &u).unwrap();
    let rl = low_layer.prove(&p.proof, &p.statement).unwrap();
    let ru = ultra_layer.prove(&u.proof, &u.statement).unwrap();
    verify(&low_layer.verifier(), &rl.proof, &p.statement).unwrap();
    verify(&ultra_layer.verifier(), &ru.proof, &u.statement).unwrap();
    // The first layer's verifier depends on the leaf's tier.
    assert!(verify(&ultra_layer.verifier(), &rl.proof, &p.statement).is_err());

    let agg = Aggregation::new((low_layer.verifier(), &rl), (ultra_layer.verifier(), &ru)).unwrap();
    let root = agg.prove(&rl, &ru).unwrap();
    verify(&agg.verifier(), &root.proof, &root.statement).unwrap();
}

/// The unfolded semantics: every gate executed on the dense state, rounding each output.
fn naive_execute(n: usize, gates: &[Gate]) -> Vec<C> {
    let mut st = vec![(0i64, 0i64); 1 << n];
    st[0] = (S, 0);
    for g in gates {
        let prev = st.clone();
        for i in 0..1usize << n {
            if (i >> g.target) & 1 == 1 || !g.controls.iter().all(|&c| (i >> c) & 1 == 1) {
                continue;
            }
            let j = i | 1 << g.target;
            let (a, b) = (prev[i], prev[j]);
            let out = |m0: C, m1: C| {
                let (x, y) = (cm(m0, a), cm(m1, b));
                round_div((x.0 + y.0, x.1 + y.1)).0
            };
            st[i] = out(g.m[0], g.m[1]);
            st[j] = out(g.m[2], g.m[3]);
        }
    }
    st
}

fn random_circuit(n: usize, count: usize, seed: u64) -> Vec<Gate> {
    let mut s = seed | 1;
    let mut next = move || {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        s
    };
    (0..count)
        .filter_map(|_| {
            let t = (next() % n as u64) as usize;
            let c1 = (next() % n as u64) as usize;
            let c2 = (next() % n as u64) as usize;
            let th = ((next() % 10_000) as f64 / 10_000.0 - 0.5) * std::f64::consts::TAU;
            let two = c1 != t;
            let three = two && c2 != t && c2 != c1;
            Some(match next() % 12 {
                0 => Gate::h(t),
                1 => Gate::x(t),
                2 => Gate::y(t),
                3 => Gate::z(t),
                4 => Gate::s(t),
                5 => Gate::t(t),
                6 if two => Gate::cnot(c1, t),
                7 if two => Gate::cz(c1, t),
                8 if three => Gate::ccnot(c1, c2, t),
                9 => Gate::rx(t, th),
                10 => Gate::ry(t, th),
                11 => Gate::rz(t, th),
                _ => return None,
            })
        })
        .collect()
}

/// Folding monomial gates into the frame changes the rows, not the result: the final state
/// equals executing every fused gate densely, bit for bit, and only rounding ones get rows.
#[test]
fn folding_matches_dense_execution() {
    for n in 1..=6 {
        for seed in 0..40u64 {
            let gates = random_circuit(n, 60, seed * 7919 + n as u64);
            let (rows, fin) = execute(n, &gates);
            assert_eq!(fin, naive_execute(n, &fuse(n, &gates)), "n={n} seed={seed}");
            let rounding = fuse(n, &gates)
                .iter()
                .filter(|g| plan(n, std::slice::from_ref(g)).steps == 1)
                .count();
            assert_eq!(rows.len(), rounding << (n - 1));
        }
    }
}

/// Which gates fold: the seven monomial ones, and none of the rounding ones.
#[test]
fn monomial_gates_fold_and_rounding_gates_do_not() {
    let steps = |g: Gate| plan(3, &[g]).steps;
    for g in [
        Gate::x(0),
        Gate::y(1),
        Gate::z(2),
        Gate::s(0),
        Gate::cnot(0, 1),
        Gate::cz(2, 0),
        Gate::ccnot(0, 1, 2),
    ] {
        assert_eq!(steps(g), 0);
    }
    for g in [
        Gate::h(0),
        Gate::t(1),
        Gate::rx(2, 0.3),
        Gate::ry(0, 0.3),
        Gate::rz(1, 0.3),
    ] {
        assert_eq!(steps(g), 1);
    }
}

/// A circuit of monomial gates only has an empty gate table: the frame alone carries the
/// state to the digest.
#[test]
#[cfg_attr(debug_assertions, ignore = "release only")]
fn monomial_only_circuit_proves() {
    let gates = vec![
        Gate::x(0),
        Gate::cnot(0, 1),
        Gate::y(2),
        Gate::s(1),
        Gate::cz(1, 2),
        Gate::ccnot(0, 2, 1),
        Gate::z(0),
    ];
    assert_eq!(plan(3, &gates).steps, 0);
    let l = build_with(FRI, 3, gates.clone()).unwrap();
    let p = l.prove(CTX).unwrap();
    assert_eq!(
        p.statement,
        statement(CTX, terminal_digest(&naive_execute(3, &fuse(3, &gates)))).unwrap()
    );
    l.verify(&p.proof, &p.statement).unwrap();
}

/// A final frame with a quarter-turn phase on top of a non-empty gate table: the boundary's
/// `d·re + c·im` term is exercised only when monomial gates follow the last rounding step.
#[test]
#[cfg_attr(debug_assertions, ignore = "release only")]
fn final_frame_phase_after_rounding_gates_proves() {
    let mut g = gates();
    // The CNOT ends the rounding runs, so S and Y fold into the frame on their own.
    g.extend([Gate::cnot(0, 1), Gate::s(0), Gate::y(1), Gate::cnot(1, 2)]);
    let p = plan(3, &g);
    assert!(p.steps > 0);
    assert!(p.frame.phase.iter().any(|&k| k & 1 == 1));
    let l = build_with(FRI, 3, g.clone()).unwrap();
    let proof = l.prove(CTX).unwrap();
    assert_eq!(
        proof.statement,
        statement(CTX, terminal_digest(&naive_execute(3, &fuse(3, &g)))).unwrap()
    );
    l.verify(&proof.proof, &proof.statement).unwrap();
}

/// A rotation that quantizes to a monomial matrix folds like the fixed monomial gates.
#[test]
fn monomial_rotations_fold() {
    let pi = std::f64::consts::PI;
    for g in [Gate::rx(0, 0.0), Gate::rz(0, pi), Gate::ry(0, pi)] {
        assert_eq!(plan(1, &[g]).steps, 0);
    }
}

#[test]
fn rounding_steps_split_into_power_of_two_tables() {
    let cases = [
        (0, [0, 0, 0]),
        (1, [1, 0, 0]),
        (5, [4, 1, 0]),
        (7, [4, 2, 1]),
        (48, [32, 16, 0]),
        (49, [32, 16, 1]),
        (63, [32, 16, 15]),
        (64, [64, 0, 0]),
    ];
    for (steps, want) in cases {
        assert_eq!(chunk_steps(steps), want, "{steps}");
    }
    // Padding: the rows pad to at most a quarter more than needed, where one table could pad
    // to nearly double.
    for steps in 1..=4096usize {
        let padded: usize = chunk_steps(steps)
            .iter()
            .map(|&k| if k == 0 { 0 } else { k.next_power_of_two() })
            .sum();
        assert!(4 * padded <= 5 * steps + 4, "{steps}: {padded}");
    }
}

/// Seven rounding steps fill all three gate tables (4 + 2 + 1); the memory bus runs across them.
#[test]
#[cfg_attr(debug_assertions, ignore = "release only")]
fn rows_across_three_gate_tables_prove() {
    let gates = vec![
        Gate::h(0),
        Gate::cnot(0, 1),
        Gate::ry(1, 0.4),
        Gate::cz(1, 2),
        Gate::t(2),
        Gate::cnot(2, 0),
        Gate::rx(0, -0.9),
        Gate::s(2),
        Gate::h(2),
        Gate::cz(2, 1),
        Gate::rz(1, 1.7),
        Gate::cnot(1, 0),
        Gate::h(1),
    ];
    assert_eq!(chunk_steps(plan(3, &gates).steps), [4, 2, 1]);
    let l = build_with(FRI, 3, gates.clone()).unwrap();
    let p = l.prove(CTX).unwrap();
    assert_eq!(
        p.proof.non_primitives.len(),
        8,
        "statement + boundary, range, digest, perm + three gate tables"
    );
    assert_eq!(
        p.statement,
        statement(CTX, terminal_digest(&naive_execute(3, &fuse(3, &gates)))).unwrap()
    );
    l.verify(&p.proof, &p.statement).unwrap();
}

#[test]
fn split_rows_partitions_by_chunk_steps() {
    for n in 1..=4 {
        for steps in [0, 1, 5, 7, 48, 63] {
            let width = 3;
            let rows: Vec<usize> = (0..(steps << (n - 1)) * width).collect();
            let parts = split_rows(n, steps, width, &rows);
            let want = chunk_steps(steps).map(|k| (k << (n - 1)) * width);
            assert_eq!(parts.map(|p| p.len()), want, "n={n} steps={steps}");
            assert_eq!(parts.concat(), rows);
        }
    }
}

/// 48 rounding steps split 32 + 16 with the third gate table absent.
#[test]
#[cfg_attr(debug_assertions, ignore = "release only")]
fn two_gate_tables_with_the_third_absent_prove() {
    // Each CZ ends its rotation's run, so nothing fuses.
    let gates: Vec<Gate> = (0..48)
        .flat_map(|k| {
            [
                Gate::ry(k % 3, 0.1 + k as f64),
                Gate::cz(k % 3, (k + 1) % 3),
            ]
        })
        .collect();
    assert_eq!(chunk_steps(plan(3, &gates).steps), [32, 16, 0]);
    let l = build_with(FRI, 3, gates.clone()).unwrap();
    let p = l.prove(CTX).unwrap();
    assert_eq!(p.proof.non_primitives.len(), 7);
    assert_eq!(
        p.statement,
        statement(CTX, terminal_digest(&naive_execute(3, &fuse(3, &gates)))).unwrap()
    );
    l.verify(&p.proof, &p.statement).unwrap();
}

/// The fusion rule: a run of single-qubit gates on one qubit becomes one gate, ended only by a
/// gate that touches that qubit; runs are emitted where they end, then at the end by qubit.
#[test]
fn single_qubit_runs_fuse() {
    let pi = std::f64::consts::PI;
    // A lone gate is unchanged.
    for g in [Gate::h(0), Gate::rx(1, 0.3), Gate::t(2)] {
        assert_eq!(fuse(3, std::slice::from_ref(&g))[0].m, g.m);
    }
    // H·H is the identity (no rows), even across gates on other qubits.
    assert_eq!(
        plan(3, &[Gate::h(0), Gate::cnot(1, 2), Gate::h(0)]).steps,
        0
    );
    // A gate touching the qubit, as control or target, ends the run.
    assert_eq!(
        plan(3, &[Gate::h(0), Gate::cnot(0, 1), Gate::h(0)]).steps,
        2
    );
    assert_eq!(plan(3, &[Gate::h(0), Gate::cz(1, 0), Gate::h(0)]).steps, 2);
    for q in 0..3 {
        let g = [Gate::h(q), Gate::ccnot(0, 1, 2), Gate::h(q)];
        assert_eq!(plan(3, &g).steps, 2, "CCNOT touching qubit {q}");
    }
    // Monomial gates join the run: H·S·H is one step, H·Z·H = X folds.
    assert_eq!(plan(1, &[Gate::h(0), Gate::s(0), Gate::h(0)]).steps, 1);
    assert_eq!(plan(1, &[Gate::h(0), Gate::z(0), Gate::h(0)]).steps, 0);
    // RY(a)·RY(b) is RY(a + b) up to rounding a few entries.
    let f = fuse(1, &[Gate::ry(0, 0.4), Gate::ry(0, 0.9)]);
    assert_eq!(f.len(), 1);
    for (x, y) in f[0].m.iter().zip(Gate::ry(0, 1.3).m) {
        assert!((x.0 - y.0).abs() <= 1 && (x.1 - y.1).abs() <= 1);
    }
    // RZ(π/2)·RZ(π/2) = RZ(π), which is monomial.
    assert_eq!(
        plan(1, &[Gate::rz(0, pi / 2.0), Gate::rz(0, pi / 2.0)]).steps,
        0
    );
    // Emission order: qubit 1's run ends at the CNOT; the others follow by qubit.
    let order: Vec<(usize, usize)> = fuse(
        3,
        &[
            Gate::h(2),
            Gate::t(0),
            Gate::ry(1, 0.2),
            Gate::cnot(1, 2),
            Gate::rx(1, 0.5),
        ],
    )
    .iter()
    .map(|g| (g.target(), g.controls().len()))
    .collect();
    assert_eq!(order, vec![(1, 0), (2, 0), (2, 1), (0, 0), (1, 0)]);
}

/// Pins a fused matrix: the `f64` product's operation order is part of the circuit.
#[test]
fn fused_matrix_known_answer() {
    let f = fuse(
        1,
        &[Gate::h(0), Gate::t(0), Gate::rx(0, 0.37), Gate::ry(0, -1.1)],
    );
    assert_eq!(f.len(), 1);
    assert_eq!(
        f[0].m,
        [
            (249063269, 29659112),
            (69053900, -66158735),
            (2047191, 95609771),
            (-197086486, -155142167)
        ]
    );
}

/// Fusion lowers the error from the ideal state: fewer roundings.
#[test]
fn fusion_does_not_add_error() {
    for seed in 0..20u64 {
        let n = 4;
        let gates = random_circuit(n, 80, seed * 31 + 5);
        let unfused = naive_execute(n, &gates);
        let fused = execute(n, &gates).1;
        let mut reference = vec![(0.0f64, 0.0f64); 1 << n];
        reference[0] = (1.0, 0.0);
        for g in &gates {
            let prev = reference.clone();
            for i in 0..1usize << n {
                if (i >> g.target) & 1 == 1 || !g.controls.iter().all(|&c| (i >> c) & 1 == 1) {
                    continue;
                }
                let j = i | 1 << g.target;
                let m = g.f;
                let c =
                    |x: (f64, f64), y: (f64, f64)| (x.0 * y.0 - x.1 * y.1, x.0 * y.1 + x.1 * y.0);
                let (a, b) = (prev[i], prev[j]);
                let (p, q, r, s) = (c(m[0], a), c(m[1], b), c(m[2], a), c(m[3], b));
                reference[i] = (p.0 + q.0, p.1 + q.1);
                reference[j] = (r.0 + s.0, r.1 + s.1);
            }
        }
        let err = |v: &[C]| {
            v.iter()
                .zip(&reference)
                .map(|(a, b)| {
                    (a.0 as f64 / S as f64 - b.0).powi(2) + (a.1 as f64 / S as f64 - b.1).powi(2)
                })
                .sum::<f64>()
                .sqrt()
        };
        let (eu, ef) = (err(&unfused), err(&fused));
        assert!(
            ef <= eu * 1.5 + 1e-8,
            "seed={seed}: fused {ef:.2e} vs unfused {eu:.2e}"
        );
    }
}

/// Fusion preserves the circuit's unitary before any integer rounding: the fused gates'
/// unrounded matrices give the same `f64` state as the gates as written.
#[test]
fn fusion_preserves_the_unrounded_circuit() {
    let apply = |n: usize, gates: &[Gate]| {
        let mut st = vec![(0.0f64, 0.0f64); 1 << n];
        st[0] = (1.0, 0.0);
        let c = |x: (f64, f64), y: (f64, f64)| (x.0 * y.0 - x.1 * y.1, x.0 * y.1 + x.1 * y.0);
        for g in gates {
            let prev = st.clone();
            for i in 0..1usize << n {
                if (i >> g.target) & 1 == 1 || !g.controls.iter().all(|&k| (i >> k) & 1 == 1) {
                    continue;
                }
                let j = i | 1 << g.target;
                let (a, b) = (prev[i], prev[j]);
                let (p, q, r, s) = (c(g.f[0], a), c(g.f[1], b), c(g.f[2], a), c(g.f[3], b));
                st[i] = (p.0 + q.0, p.1 + q.1);
                st[j] = (r.0 + s.0, r.1 + s.1);
            }
        }
        st
    };
    for n in 1..=5 {
        for seed in 0..20u64 {
            let gates = random_circuit(n, 60, seed * 131 + n as u64);
            let (a, b) = (apply(n, &gates), apply(n, &fuse(n, &gates)));
            let d = a
                .iter()
                .zip(&b)
                .map(|(x, y)| (x.0 - y.0).powi(2) + (x.1 - y.1).powi(2))
                .sum::<f64>()
                .sqrt();
            assert!(d < 1e-12, "n={n} seed={seed}: {d:e}");
        }
    }
}

fn context(circuit_id: &str, sub_task_id: &str, node_id: &str, slice_id: &str) -> [u64; 4] {
    Dispatch {
        circuit_id,
        sub_task_id,
        node_id,
        slice_id,
    }
    .context()
}

/// Pins the context encoding; the values were computed independently (Python `hashlib`). The
/// third vector's last word is reduced (raw `p + 930599047`), and the fourth has a non-ASCII
/// field whose length counts bytes (8), not characters (4).
#[test]
fn context_known_answer() {
    assert_eq!(
        context("3f2a9c", "sub-7", "12D3KooWExample", "0"),
        [
            2629832246304586780,
            6289402838643317648,
            3984696892480907753,
            15826953888818560288
        ]
    );
    assert_eq!(
        context("", "", "", ""),
        [
            6244185044995144319,
            17249683863875817547,
            190826013191292089,
            6584790768701115510
        ]
    );
    assert_eq!(
        context("c", "s5-54997470", "n", "0"),
        [
            2509611998161888353,
            10023014128191975046,
            27256567443016035,
            930599047
        ]
    );
    assert_eq!(
        context("回路-1", "sub-7", "12D3KooWExample", "0"),
        [
            16226241412038407406,
            11953317444174577628,
            3935241966496295430,
            2834988945403643933
        ]
    );
}

/// The word reduction on its own: words at or above the prime wrap.
#[test]
fn context_words_reduce_modulo_the_prime() {
    let p = <F as p3_field::PrimeField64>::ORDER_U64;
    let mut h = [0xFF; 32];
    assert_eq!(reduce_words(h), [u64::MAX - p; 4]);
    h[..8].copy_from_slice(&p.to_le_bytes());
    h[8..16].copy_from_slice(&(p - 1).to_le_bytes());
    h[16..24].copy_from_slice(&(p + 1).to_le_bytes());
    h[24..].copy_from_slice(&0u64.to_le_bytes());
    assert_eq!(reduce_words(h), [0, p - 1, 1, 0]);
}

/// Every field changes the context, field boundaries are unambiguous, and the words are
/// canonical field elements.
#[test]
fn context_separates_fields() {
    let base = context("c", "s", "n", "0");
    for other in [
        context("d", "s", "n", "0"),
        context("c", "t", "n", "0"),
        context("c", "s", "m", "0"),
        context("c", "s", "n", "1"),
        context("cs", "", "n", "0"),
        context("", "cs", "n", "0"),
        context("c", "s", "n0", ""),
    ] {
        assert_ne!(base, other);
    }
    for f in [base, context("", "", "", "")] {
        assert!(f
            .iter()
            .all(|&x| x < <F as p3_field::PrimeField64>::ORDER_U64));
        statement(f, [0; DIGEST_LEN]).unwrap();
    }
}

/// A proof made for one node's dispatch verifies only for that dispatch; the statement has
/// exactly `STATEMENT_LEN` elements.
#[test]
#[cfg_attr(debug_assertions, ignore = "release only")]
fn a_proof_is_bound_to_its_dispatch() {
    let l = leaf(Tamper::None);
    let mine = Dispatch {
        circuit_id: "circuit",
        sub_task_id: "sub-1",
        node_id: "node-a",
        slice_id: "0",
    };
    let p = l.prove(mine.context()).unwrap();
    assert_eq!(p.statement.len(), STATEMENT_LEN);
    // The verifier's expected digest, here from honest execution.
    let digest = terminal_digest(&execute(3, &gates()).1);
    l.verify_dispatch(&p.proof, &mine, digest).unwrap();
    for other in [
        Dispatch {
            node_id: "node-b",
            ..mine
        },
        Dispatch {
            sub_task_id: "sub-2",
            ..mine
        },
        Dispatch {
            slice_id: "1",
            ..mine
        },
        Dispatch {
            circuit_id: "other",
            ..mine
        },
    ] {
        assert!(
            l.verify_dispatch(&p.proof, &other, digest).is_err(),
            "{other:?}"
        );
    }
    let mut wrong = digest;
    wrong[0] ^= 1;
    assert!(l.verify_dispatch(&p.proof, &mine, wrong).is_err());
    // Statements of the wrong length are rejected.
    let full = statement(mine.context(), digest).unwrap();
    assert!(l.verify(&p.proof, &full[..STATEMENT_LEN - 1]).is_err());
    let mut longer = full.clone();
    longer.push(F::ZERO);
    assert!(l.verify(&p.proof, &longer).is_err());
}

fn bell_sampling(shots: u32) -> crate::born::Sampling {
    use crate::born::{Measure, Sampling};
    Sampling {
        measures: vec![Measure { qubit: 0, cbit: 0 }, Measure { qubit: 1, cbit: 1 }],
        cbits: 2,
        shots,
    }
}

fn sampling_leaf(tamper: Tamper) -> Leaf {
    let gates = vec![Gate::h(0), Gate::cnot(0, 1), Gate::ry(1, 0.7)];
    build_with_tamper(FRI, 2, gates, Some(bell_sampling(64)), tamper).unwrap()
}

/// The sampling leaf proves the counts its native sampling gives, and verifies only for its
/// dispatch, state digest, seed and counts.
#[test]
#[cfg_attr(debug_assertions, ignore = "release only")]
fn sampling_leaf_proves_its_counts() {
    use crate::born::{counts_digest, sample};
    use crate::leaf::{sampling_statement, SAMPLING_STATEMENT_LEN};
    let gates = vec![Gate::h(0), Gate::cnot(0, 1), Gate::ry(1, 0.7)];
    let l = sampling_leaf(Tamper::None);
    let d = Dispatch {
        circuit_id: "c",
        sub_task_id: "s",
        node_id: "n",
        slice_id: "0",
    };
    let seed = 0xDEAD_BEEF_0123_4567;
    let (p, counts) = l.prove_sampling(d.context(), seed).unwrap();
    assert_eq!(p.statement.len(), SAMPLING_STATEMENT_LEN);
    let fin = execute(2, &gates).1;
    let digest = terminal_digest(&fin);
    assert_eq!(
        counts,
        sample(&fin, &bell_sampling(64), seed).unwrap().counts
    );
    assert_eq!(counts.iter().sum::<u64>(), 64);
    assert_eq!(
        p.statement,
        sampling_statement(d.context(), digest, seed, 64, counts_digest(&counts)).unwrap()
    );
    l.verify_sampling(&p.proof, &d, digest, seed, &counts)
        .unwrap();

    let mut other = counts.clone();
    let k = other.iter().position(|&c| c > 0).unwrap();
    other[k] -= 1;
    other[(k + 1) % 4] += 1;
    assert!(l
        .verify_sampling(&p.proof, &d, digest, seed, &other)
        .is_err());
    // Counts congruent mod p have the same digest, but are not canonical.
    let p_u64 = <F as p3_field::PrimeField64>::ORDER_U64;
    let shifted: Vec<u64> = counts.iter().map(|&c| c + p_u64).collect();
    assert_eq!(counts_digest(&shifted), counts_digest(&counts));
    assert!(l
        .verify_sampling(&p.proof, &d, digest, seed, &shifted)
        .is_err());
    let mut wrapped = counts.clone();
    wrapped[0] += 1;
    wrapped[1] += p_u64 - 1;
    assert!(l
        .verify_sampling(&p.proof, &d, digest, seed, &wrapped)
        .is_err());
    assert!(l
        .verify_sampling(&p.proof, &d, digest, seed ^ 1, &counts)
        .is_err());
    let mut wrong = digest;
    wrong[0] ^= 1;
    assert!(l
        .verify_sampling(&p.proof, &d, wrong, seed, &counts)
        .is_err());
    let other_node = Dispatch { node_id: "m", ..d };
    assert!(l
        .verify_sampling(&p.proof, &other_node, digest, seed, &counts)
        .is_err());
    // The shot count is part of the statement.
    let mut more = p.statement.clone();
    more[STATEMENT_LEN + 2] += F::ONE;
    assert!(l.verify(&p.proof, &more).is_err());
    // A unitary leaf of the same circuit does not accept it.
    let unitary = build_with(FRI, 2, gates).unwrap();
    assert!(unitary
        .verify(&p.proof, &p.statement[..STATEMENT_LEN])
        .is_err());
    assert!(l.prove(d.context()).is_err());
}

/// Forged samplings are rejected even with the statement the forgery exports.
#[test]
#[cfg_attr(debug_assertions, ignore = "release only")]
fn forged_samplings_are_rejected() {
    for t in [Tamper::CountShift, Tamper::DrawMove] {
        let l = sampling_leaf(t);
        let (p, _) = l.prove_sampling(CTX, 7).unwrap();
        assert!(l.verify(&p.proof, &p.statement).is_err(), "{t:?} accepted");
    }
}

/// Pins the sampling: draws come from the leaf's Poseidon2 under the seed, so a change there
/// changes every count.
#[test]
fn sampling_known_answer() {
    use crate::born::sample;
    let fin = execute(2, &[Gate::h(0), Gate::cnot(0, 1), Gate::ry(1, 0.7)]).1;
    let run = sample(&fin, &bell_sampling(64), 0xDEAD_BEEF_0123_4567).unwrap();
    assert!(run.rejects > 0, "the rejection branch is exercised");
    assert_eq!(run.counts, vec![25, 4, 6, 29]);
}

/// Each shot picks a basis state with probability `p_b / T`: frequencies over many shots
/// match the Born probabilities.
#[test]
fn sampling_follows_born_probabilities() {
    use crate::born::{sample, Measure, Sampling};
    let n = 3;
    let gates = vec![
        Gate::ry(0, 1.1),
        Gate::h(1),
        Gate::cnot(1, 2),
        Gate::rx(2, 0.4),
    ];
    let fin = execute(n, &gates).1;
    let shots = 1 << 16;
    let s = Sampling {
        measures: (0..n).map(|q| Measure { qubit: q, cbit: q }).collect(),
        cbits: n,
        shots,
    };
    let counts = sample(&fin, &s, 99).unwrap().counts;
    let w: Vec<f64> = fin
        .iter()
        .map(|&(re, im)| (re as f64).powi(2) + (im as f64).powi(2))
        .collect();
    let total: f64 = w.iter().sum();
    for (b, &c) in counts.iter().enumerate() {
        let p = w[b] / total;
        let sd = (shots as f64 * p * (1.0 - p)).sqrt();
        let dev = (c as f64 - shots as f64 * p).abs();
        assert!(
            dev <= 5.0 * sd + 1.0,
            "basis {b}: {c} vs {:.1}",
            shots as f64 * p
        );
    }
}

/// Registers: a later measure into the same cbit wins, unmeasured cbits stay 0, and
/// unmeasured qubits are marginalized.
#[test]
fn sampling_outcomes_follow_the_measurements() {
    use crate::born::{Measure, Sampling};
    let s = Sampling {
        measures: vec![
            Measure { qubit: 0, cbit: 2 },
            Measure { qubit: 2, cbit: 0 },
            Measure { qubit: 1, cbit: 0 },
        ],
        cbits: 3,
        shots: 1,
    };
    assert_eq!(s.outcome(0b001), 0b100);
    assert_eq!(s.outcome(0b100), 0b000);
    assert_eq!(s.outcome(0b010), 0b001);
    assert_eq!(s.outcome(0b111), 0b101);
    assert_eq!(s.counts_len(), 8);
    let one = Sampling {
        measures: vec![Measure { qubit: 0, cbit: 0 }],
        cbits: 1,
        shots: 1,
    };
    assert_eq!(one.counts_len(), 4);
    assert!(build_with_tamper(FRI, 3, vec![Gate::h(0)], Some(one.clone()), Tamper::None).is_ok());
    for bad in [
        Sampling {
            measures: vec![],
            ..one.clone()
        },
        Sampling {
            shots: 0,
            ..one.clone()
        },
        Sampling {
            shots: (1 << 16) + 1,
            ..one.clone()
        },
        Sampling {
            cbits: 0,
            ..one.clone()
        },
        Sampling {
            cbits: 17,
            ..one.clone()
        },
        Sampling {
            measures: vec![Measure { qubit: 3, cbit: 0 }],
            ..one.clone()
        },
        Sampling {
            measures: vec![Measure { qubit: 0, cbit: 1 }],
            ..one.clone()
        },
    ] {
        assert!(
            build_with_tamper(FRI, 3, vec![Gate::h(0)], Some(bad.clone()), Tamper::None).is_err(),
            "{bad:?}"
        );
    }
}

/// Small sampling leaves prove in debug builds too, where `prove` checks every constraint: one
/// qubit (a single counts block for one cbit), and four qubits with one measured.
#[test]
fn small_sampling_leaves_satisfy_their_constraints() {
    use crate::born::{counts_digest, Measure, Sampling};
    use crate::leaf::sampling_statement;
    let cases = [
        (
            1,
            vec![Gate::ry(0, 0.9)],
            vec![Measure { qubit: 0, cbit: 0 }],
            1,
        ),
        (
            4,
            vec![Gate::h(0), Gate::cnot(0, 3), Gate::rz(3, 0.3), Gate::h(2)],
            vec![Measure { qubit: 3, cbit: 1 }],
            2,
        ),
        // Eight counts: two sponge blocks.
        (
            3,
            vec![Gate::h(0), Gate::h(1), Gate::ry(2, 1.1)],
            vec![
                Measure { qubit: 0, cbit: 0 },
                Measure { qubit: 1, cbit: 1 },
                Measure { qubit: 2, cbit: 2 },
            ],
            3,
        ),
    ];
    for (n, gates, measures, cbits) in cases {
        let s = Sampling {
            measures,
            cbits,
            shots: 5,
        };
        let l = build_with_tamper(FRI, n, gates.clone(), Some(s), Tamper::None).unwrap();
        let (p, counts) = l.prove_sampling(CTX, 3).unwrap();
        let digest = terminal_digest(&execute(n, &gates).1);
        let want = sampling_statement(CTX, digest, 3, 5, counts_digest(&counts)).unwrap();
        l.verify(&p.proof, &want).unwrap();
    }
}

/// Recursion takes a sampling leaf like any other: the layer verifies against the 15-element
/// statement.
#[test]
#[cfg_attr(debug_assertions, ignore = "release only")]
fn recursion_over_a_sampling_leaf() {
    let l = sampling_leaf(Tamper::None);
    let (p, _) = l.prove_sampling(CTX, 11).unwrap();
    let layer = Layer::over_leaf(&l, &p).unwrap();
    let r = layer.prove(&p.proof, &p.statement).unwrap();
    verify(&layer.verifier(), &r.proof, &p.statement).unwrap();
    let mut other = p.statement.clone();
    *other.last_mut().unwrap() += F::ONE;
    assert!(verify(&layer.verifier(), &r.proof, &other).is_err());
}

/// A verifier from `build_verifier` (coset-by-coset commitment, no proving data) accepts the
/// proofs of the leaf `build` gives and nothing the leaf's own verifier rejects.
#[test]
fn build_verifier_verifies_leaf_proofs() {
    use crate::born::{Measure, Sampling};
    use crate::leaf::{build_sampling, build_verifier};
    let level = SecurityLevel::Low;
    let g = gates();
    let l = build(level, 3, g.clone()).unwrap();
    let v = build_verifier(level, 3, g.clone(), None).unwrap();
    let p = l.prove(CTX).unwrap();
    let digest = terminal_digest(&execute(3, &g).1);
    v.verify(&p.proof, &statement(CTX, digest).unwrap())
        .unwrap();
    let mut wrong = digest;
    wrong[0] ^= 1;
    assert!(v.verify(&p.proof, &statement(CTX, wrong).unwrap()).is_err());
    // Another circuit's or another tier's verifier rejects it.
    let mut other = g.clone();
    other.push(Gate::h(1));
    let ov = build_verifier(level, 3, other, None).unwrap();
    assert!(ov.verify(&p.proof, &p.statement).is_err());
    let uv = build_verifier(SecurityLevel::Ultra, 3, g.clone(), None).unwrap();
    assert!(uv.verify(&p.proof, &p.statement).is_err());

    let s = Sampling {
        measures: vec![Measure { qubit: 0, cbit: 0 }, Measure { qubit: 2, cbit: 1 }],
        cbits: 2,
        shots: 100,
    };
    let sl = build_sampling(level, 3, g.clone(), s.clone()).unwrap();
    let sv = build_verifier(level, 3, g, Some(s)).unwrap();
    let d = Dispatch {
        circuit_id: "c",
        sub_task_id: "s",
        node_id: "n",
        slice_id: "",
    };
    let (sp, counts) = sl.prove_sampling(d.context(), 9).unwrap();
    sv.verify_sampling(&sp.proof, &d, digest, 9, &counts)
        .unwrap();
    assert!(sv
        .verify_sampling(&sp.proof, &d, digest, 10, &counts)
        .is_err());
}

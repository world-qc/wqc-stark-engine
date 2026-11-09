//! Run in release: debug builds assert AIR constraints inside `prove`, so the forgery tests
//! are ignored there.

use p3_field::PrimeCharacteristicRing;

use crate::digest::*;
use crate::exec::*;
use crate::leaf::{build, build_with, build_with_tamper, statement, Leaf, LeafProof};
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
    build_with_tamper(FRI, 3, gates(), tamper).unwrap()
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

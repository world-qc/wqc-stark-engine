//! Deterministic fixed-point execution of a circuit on a dense state vector.
//!
//! Amplitudes are integers in units of `1/S`. Each gate output is `Σ m·a / S` rounded to the
//! nearest integer, ties up: `b = floor((Σ m·a + S/2) / S)` with remainder `r ∈ [0, S)`. The
//! gate table proves `b·S + r = Σ m·a + S/2` and range-checks `b`, `r`.
//!
//! Execution is integer-only and therefore bit-exact on any hardware. Matrices are rounded from
//! `f64` once, at build; the one platform-dependent step there would be a rotation's
//! `sin`/`cos`, so those come from the pure-Rust `libm` (pinned) and every party derives the
//! same preprocessed circuit.
//!
//! Field soundness: entries are at most `S` and inputs lie in `[−2S, 2S)`, so both sides of the
//! row equation stay below `2^(2·LOG_S+4)` in magnitude (`8S² + S/2` on the right), far
//! below the Goldilocks modulus, and the field equation is the integer one.

use p3_field::Field;

pub const LOG_S: u32 = 28;
pub const S: i64 = 1 << LOG_S;
pub(crate) const HALF_S: i64 = S / 2;
pub(crate) const B_OFFSET: i64 = 2 * S;

/// A 2×2 complex matrix on `target`, applied where every `controls` bit is 1. Entries are
/// fixed point (units of `1/S`), rounded half away from zero from `f64`.
///
/// The constructors cover wqc-core's gate set (H, X, Y, Z, S, T, CNOT, CZ, CCNOT, RX, RY,
/// RZ) with the same matrices and phases as its dense engine; qubit `k` is bit `k` of the
/// state index. There is no public arbitrary-matrix gate: the protocol has none (rotations
/// are what the `CUSTOM_UNITARY` capability bit names).
#[derive(Clone, Debug)]
pub struct Gate {
    pub(crate) target: usize,
    pub(crate) controls: Vec<usize>,
    pub(crate) m: [(i64, i64); 4],
}

/// Rounds to fixed point. A non-finite value becomes 0 (a NaN angle yields NaN entries), so
/// such a matrix fails the unitarity check instead of saturating to `i64::MIN`.
pub(crate) fn q(x: f64) -> i64 {
    if x.is_finite() {
        (x * S as f64).round() as i64
    } else {
        0
    }
}

impl Gate {
    pub fn target(&self) -> usize {
        self.target
    }
    pub fn controls(&self) -> &[usize] {
        &self.controls
    }

    /// Rejects wiring outside `n` qubits and matrices that are not unitary up to rounding.
    /// Entries of magnitude at most 1 keep every product inside `i64` and far below the field
    /// modulus; unitarity keeps amplitudes inside `[−2, 2)` and catches a NaN angle, which
    /// rounds to the zero matrix.
    pub(crate) fn validate(&self, n: usize) -> Result<(), crate::Error> {
        let bad = |m: String| Err(crate::Error::InvalidCircuit(m));
        if self.target >= n {
            return bad(format!("target {} on {n} qubits", self.target));
        }
        for (k, &c) in self.controls.iter().enumerate() {
            if c >= n || c == self.target || self.controls[..k].contains(&c) {
                return bad(format!(
                    "control {c} on target {} with {n} qubits",
                    self.target
                ));
            }
        }
        let bound = S.unsigned_abs();
        if self
            .m
            .iter()
            .any(|&(re, im)| re.unsigned_abs() > bound || im.unsigned_abs() > bound)
        {
            return bad("matrix entry above 1 in magnitude".into());
        }
        if !self.is_unitary() {
            return bad("matrix is not unitary".into());
        }
        Ok(())
    }

    /// Columns of norm S² and orthogonal, each within 4S (the rounding of four entries).
    fn is_unitary(&self) -> bool {
        let e = |k: usize| (self.m[k].0 as i128, self.m[k].1 as i128);
        let norm2 = |a: (i128, i128)| a.0 * a.0 + a.1 * a.1;
        let s2 = (S as i128) * (S as i128);
        let tol = 4 * S as i128;
        let (m00, m01, m10, m11) = (e(0), e(1), e(2), e(3));
        let col0 = norm2(m00) + norm2(m10);
        let col1 = norm2(m01) + norm2(m11);
        // conj(m00)·m01 + conj(m10)·m11
        let dot = (
            m00.0 * m01.0 + m00.1 * m01.1 + m10.0 * m11.0 + m10.1 * m11.1,
            m00.0 * m01.1 - m00.1 * m01.0 + m10.0 * m11.1 - m10.1 * m11.0,
        );
        (col0 - s2).abs() <= tol
            && (col1 - s2).abs() <= tol
            && dot.0.abs() <= tol
            && dot.1.abs() <= tol
    }

    pub(crate) fn from_f64(target: usize, controls: Vec<usize>, m: [(f64, f64); 4]) -> Self {
        Self {
            target,
            controls,
            m: m.map(|(re, im)| (q(re), q(im))),
        }
    }
    pub fn h(t: usize) -> Self {
        let s = std::f64::consts::FRAC_1_SQRT_2;
        Self::from_f64(t, vec![], [(s, 0.0), (s, 0.0), (s, 0.0), (-s, 0.0)])
    }
    pub fn y(t: usize) -> Self {
        Self::from_f64(t, vec![], [(0.0, 0.0), (0.0, -1.0), (0.0, 1.0), (0.0, 0.0)])
    }
    pub fn z(t: usize) -> Self {
        Self::from_f64(t, vec![], [(1.0, 0.0), (0.0, 0.0), (0.0, 0.0), (-1.0, 0.0)])
    }
    pub fn s(t: usize) -> Self {
        Self::from_f64(t, vec![], [(1.0, 0.0), (0.0, 0.0), (0.0, 0.0), (0.0, 1.0)])
    }
    pub fn cz(c: usize, t: usize) -> Self {
        Self {
            controls: vec![c],
            ..Self::z(t)
        }
    }
    pub fn ccnot(c1: usize, c2: usize, t: usize) -> Self {
        Self {
            controls: vec![c1, c2],
            ..Self::x(t)
        }
    }
    pub fn rx(t: usize, theta: f64) -> Self {
        let (c, s) = sin_cos_half(theta);
        Self::from_f64(t, vec![], [(c, 0.0), (0.0, -s), (0.0, -s), (c, 0.0)])
    }
    pub fn x(t: usize) -> Self {
        Self::from_f64(t, vec![], [(0.0, 0.0), (1.0, 0.0), (1.0, 0.0), (0.0, 0.0)])
    }
    pub fn cnot(c: usize, t: usize) -> Self {
        Self {
            controls: vec![c],
            ..Self::x(t)
        }
    }
    pub fn ry(t: usize, theta: f64) -> Self {
        let (c, s) = sin_cos_half(theta);
        Self::from_f64(t, vec![], [(c, 0.0), (-s, 0.0), (s, 0.0), (c, 0.0)])
    }
    pub fn rz(t: usize, theta: f64) -> Self {
        let (c, s) = sin_cos_half(theta);
        Self::from_f64(t, vec![], [(c, -s), (0.0, 0.0), (0.0, 0.0), (c, s)])
    }
    pub fn t(t: usize) -> Self {
        let s = std::f64::consts::FRAC_1_SQRT_2;
        Self::from_f64(t, vec![], [(1.0, 0.0), (0.0, 0.0), (0.0, 0.0), (s, s)])
    }
}

/// `(cos θ/2, sin θ/2)` from the pinned `libm`: `std`'s `sin`/`cos` follow the platform libm
/// and may differ by an ulp, which could change a rounded entry and so the circuit.
fn sin_cos_half(theta: f64) -> (f64, f64) {
    (libm::cos(theta / 2.0), libm::sin(theta / 2.0))
}

pub type C = (i64, i64);

/// Rounds `v / S` to nearest (ties up): the gate output and its remainder.
pub(crate) fn round_div(v: C) -> (C, C) {
    let (re, im) = (v.0 + HALF_S, v.1 + HALF_S);
    (
        (re.div_euclid(S), im.div_euclid(S)),
        (re.rem_euclid(S), im.rem_euclid(S)),
    )
}

pub(crate) fn cm(m: C, x: C) -> C {
    (m.0 * x.0 - m.1 * x.1, m.0 * x.1 + m.1 * x.0)
}

#[derive(Clone, Debug)]
pub struct PairRow {
    pub t: usize,
    pub i: usize,
    pub j: usize,
    pub active: bool,
    pub m: [C; 4],
    pub a: [C; 2],
    pub b: [C; 2],
    pub r: [C; 2],
}

pub(crate) fn pairs(n: usize, g: &Gate) -> impl Iterator<Item = (usize, usize, bool)> + '_ {
    (0..1usize << n)
        .filter(move |i| (i >> g.target) & 1 == 0)
        .map(move |i| {
            let active = g.controls.iter().all(|&c| (i >> c) & 1 == 1);
            (i, i | (1 << g.target), active)
        })
}

pub fn execute(n: usize, gates: &[Gate]) -> (Vec<PairRow>, Vec<C>) {
    let mut st = vec![(0i64, 0i64); 1 << n];
    st[0] = (S, 0);
    let mut rows = Vec::new();
    for (t, g) in gates.iter().enumerate() {
        let mut nx = st.clone();
        for (i, j, active) in pairs(n, g) {
            let (ai, aj) = (st[i], st[j]);
            let (ni, nj) = if active {
                let (x, y, z, w) = (
                    cm(g.m[0], ai),
                    cm(g.m[1], aj),
                    cm(g.m[2], ai),
                    cm(g.m[3], aj),
                );
                ((x.0 + y.0, x.1 + y.1), (z.0 + w.0, z.1 + w.1))
            } else {
                ((ai.0 * S, ai.1 * S), (aj.0 * S, aj.1 * S))
            };
            let ((bi, ri), (bj, rj)) = (round_div(ni), round_div(nj));
            nx[i] = bi;
            nx[j] = bj;
            rows.push(PairRow {
                t,
                i,
                j,
                active,
                m: g.m,
                a: [ai, aj],
                b: [nx[i], nx[j]],
                r: [ri, rj],
            });
        }
        st = nx;
    }
    (rows, st)
}

pub(crate) fn fi<T: Field>(x: i64) -> T {
    if x >= 0 {
        T::from_u64(x as u64)
    } else {
        -T::from_u64((-x) as u64)
    }
}

pub(crate) fn limbs(x: u64) -> (u64, u64) {
    (x & 0xffff, x >> 16)
}

/// Test-only tampering of the executed rows (main trace), applied after honest execution.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) enum Tamper {
    #[default]
    None,
    /// Shift one gate output by one (the row equation breaks).
    GateOutput,
    /// Change one gate input and recompute that row's outputs (only `mem` can catch it).
    ReadMismatch,
    /// b − 1, r + S on one row, carried forward (only `range` can catch it).
    Remainder,
    /// The digest table hashes a different final state than the gate table produced; the
    /// output digest is that other state's (only `fin` can catch it).
    DigestSwap,
}

pub(crate) fn apply_tamper(tamper: Tamper, rows: &mut [PairRow], fin: &mut [C], steps: usize) {
    match tamper {
        Tamper::None => {}
        Tamper::GateOutput => {
            let k = rows.iter().position(|r| r.t + 2 == steps).unwrap();
            rows[k].b[0].0 += 1;
        }
        Tamper::ReadMismatch => {
            let k = rows
                .iter()
                .position(|r| r.t + 1 == steps && r.active)
                .unwrap();
            rows[k].a[0].0 += 1000;
            let pr = rows[k].clone();
            let (x, y, z, w) = (
                cm(pr.m[0], pr.a[0]),
                cm(pr.m[1], pr.a[1]),
                cm(pr.m[2], pr.a[0]),
                cm(pr.m[3], pr.a[1]),
            );
            let outs = [(x.0 + y.0, x.1 + y.1), (z.0 + w.0, z.1 + w.1)];
            let idx = [pr.i, pr.j];
            for q in 0..2 {
                (rows[k].b[q], rows[k].r[q]) = round_div(outs[q]);
                fin[idx[q]] = rows[k].b[q];
            }
        }
        Tamper::DigestSwap => {}
        Tamper::Remainder => {
            let k = rows
                .iter()
                .position(|r| r.t + 1 == steps && r.active)
                .unwrap();
            rows[k].b[0].0 -= 1;
            rows[k].r[0].0 += S;
            fin[rows[k].i].0 -= 1;
        }
    }
}

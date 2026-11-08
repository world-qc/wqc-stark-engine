//! Deterministic fixed-point execution of a circuit on a dense state vector.
//!
//! Amplitudes are integers in units of `1/S`. Each gate output is `floor(Σ m·a / S)` with
//! remainder `r ∈ [0, S)`; the gate table proves `b·S + r = Σ m·a` and range-checks `b`, `r`.

use p3_field::Field;

pub const LOG_S: u32 = 24;
pub const S: i64 = 1 << LOG_S;
pub(crate) const B_OFFSET: i64 = 2 * S;

#[derive(Clone, Debug)]
pub struct Gate {
    pub target: usize,
    pub controls: Vec<usize>,
    pub m: [(i64, i64); 4],
}

pub(crate) fn q(x: f64) -> i64 {
    (x * S as f64).round() as i64
}

impl Gate {
    fn from_f64(target: usize, controls: Vec<usize>, m: [(f64, f64); 4]) -> Self {
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
        let (c, s) = ((theta / 2.0).cos(), (theta / 2.0).sin());
        Self::from_f64(t, vec![], [(c, 0.0), (-s, 0.0), (s, 0.0), (c, 0.0)])
    }
    pub fn rz(t: usize, theta: f64) -> Self {
        let (c, s) = ((theta / 2.0).cos(), (theta / 2.0).sin());
        Self::from_f64(t, vec![], [(c, -s), (0.0, 0.0), (0.0, 0.0), (c, s)])
    }
    pub fn t(t: usize) -> Self {
        let s = std::f64::consts::FRAC_1_SQRT_2;
        Self::from_f64(t, vec![], [(1.0, 0.0), (0.0, 0.0), (0.0, 0.0), (s, s)])
    }
}

pub type C = (i64, i64);

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
            let fl = |v: C| (v.0.div_euclid(S), v.1.div_euclid(S));
            let rm = |v: C| (v.0.rem_euclid(S), v.1.rem_euclid(S));
            nx[i] = fl(ni);
            nx[j] = fl(nj);
            rows.push(PairRow {
                t,
                i,
                j,
                active,
                m: g.m,
                a: [ai, aj],
                b: [nx[i], nx[j]],
                r: [rm(ni), rm(nj)],
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
                rows[k].b[q] = (outs[q].0.div_euclid(S), outs[q].1.div_euclid(S));
                rows[k].r[q] = (outs[q].0.rem_euclid(S), outs[q].1.rem_euclid(S));
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

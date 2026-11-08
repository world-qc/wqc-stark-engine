//! The leaf's tables: gate, boundary, range, digest and permutation AIRs.
//!
//! Every AIR is rebuilt from its committed preprocessed columns alone, as the recursive
//! verifier needs.

use std::borrow::Borrow;

use crate::digest::*;
use crate::exec::*;
use crate::{Cfg, F};
use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_circuit_prover::BatchAir;
use p3_field::PrimeCharacteristicRing;
use p3_lookup::{Count, InteractionBuilder};
use p3_matrix::dense::RowMajorMatrix;

pub(crate) const LOG_RANGE: usize = 16;
pub(crate) const R_HI_SHIFT: u64 = 1 << 8;
pub(crate) const B_HI_SHIFT: u64 = 1 << 6;
pub(crate) const MEM: &str = "wqc_mem";
pub(crate) const RANGE: &str = "wqc_range";
pub(crate) const FIN: &str = "wqc_fin";
pub(crate) const PERM: &str = "wqc_perm";
pub(crate) const GP: usize = 13; // gate preprocessed: real, t, i, j, active, m[8]
pub(crate) const BP: usize = 4; // boundary preprocessed: real, idx, init_re, last_t
pub(crate) const DP: usize = 3 + 2 * DIGEST_LEN; // digest preprocessed: real, is_last, idx0, (out_idx, out_mult) × 4
pub(crate) const PP: usize = 1; // perm preprocessed: real

pub(crate) fn padded_rows(real: usize, min_height: usize) -> usize {
    real.max(1)
        .next_power_of_two()
        .max(min_height.next_power_of_two())
}

pub(crate) fn prep_matrix(prep: &[F], width: usize, min_height: usize) -> RowMajorMatrix<F> {
    let h = padded_rows(prep.len() / width, min_height);
    let mut v = prep.to_vec();
    v.resize(h * width, F::ZERO);
    RowMajorMatrix::new(v, width)
}

pub(crate) const G_A: usize = 0;
pub(crate) const G_B: usize = 4;
pub(crate) const G_R: usize = 8;
pub(crate) const G_RL: usize = 12;
pub(crate) const G_BL: usize = 20;
pub(crate) const G_WIDTH: usize = 28;

pub(crate) fn range_queries(rows: &[PairRow]) -> Vec<u64> {
    let mut q = Vec::with_capacity(rows.len() * 24);
    for pr in rows {
        for x in [pr.b[0].0, pr.b[0].1, pr.b[1].0, pr.b[1].1] {
            let (lo, hi) = limbs((x + B_OFFSET) as u64);
            q.extend([lo, hi, hi * B_HI_SHIFT]);
        }
        for x in [pr.r[0].0, pr.r[0].1, pr.r[1].0, pr.r[1].1] {
            let (lo, hi) = limbs(x as u64);
            q.extend([lo, hi, hi * R_HI_SHIFT]);
        }
    }
    q
}

#[derive(Clone)]
pub struct GateTableAir {
    pub prep: Vec<F>,
    pub min_height: usize,
}

impl GateTableAir {
    pub(crate) fn rows(&self) -> usize {
        padded_rows(self.prep.len() / GP, self.min_height)
    }
    pub(crate) fn main(&self, rows: &[PairRow]) -> RowMajorMatrix<F> {
        let h = self.rows();
        let mut v = vec![F::ZERO; h * G_WIDTH];
        let comps = |x: [C; 2]| [x[0].0, x[0].1, x[1].0, x[1].1];
        for k in 0..h {
            let row = &mut v[k * G_WIDTH..(k + 1) * G_WIDTH];
            let (a, b, r) = match rows.get(k) {
                Some(pr) => (comps(pr.a), comps(pr.b), comps(pr.r)),
                None => ([0; 4], [0; 4], [0; 4]),
            };
            for c in 0..4 {
                row[G_A + c] = fi(a[c]);
                row[G_B + c] = fi(b[c]);
                row[G_R + c] = fi(r[c]);
                let (lo, hi) = limbs((b[c] + B_OFFSET) as u64);
                row[G_BL + 2 * c] = F::from_u64(lo);
                row[G_BL + 2 * c + 1] = F::from_u64(hi);
                let (lo, hi) = limbs(r[c] as u64);
                row[G_RL + 2 * c] = F::from_u64(lo);
                row[G_RL + 2 * c + 1] = F::from_u64(hi);
            }
        }
        RowMajorMatrix::new(v, G_WIDTH)
    }
}

impl BaseAir<F> for GateTableAir {
    fn width(&self) -> usize {
        G_WIDTH
    }
    fn preprocessed_width(&self) -> usize {
        GP
    }
    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        Some(prep_matrix(&self.prep, GP, self.min_height))
    }
    fn main_next_row_columns(&self) -> Vec<usize> {
        vec![]
    }
    fn preprocessed_next_row_columns(&self) -> Vec<usize> {
        vec![]
    }
}

impl<AB: AirBuilder<F = F> + InteractionBuilder> Air<AB> for GateTableAir {
    fn eval(&self, builder: &mut AB) {
        let p: Vec<AB::Expr> = builder
            .preprocessed()
            .current_slice()
            .iter()
            .map(|&x| x.into())
            .collect();
        let cur: Vec<AB::Expr> = builder
            .main()
            .current_slice()
            .iter()
            .map(|&x| x.into())
            .collect();
        let s: AB::Expr = F::from_u64(S as u64).into();
        let one = AB::Expr::ONE;
        let (real, t, i, j, active) = (
            p[0].clone(),
            p[1].clone(),
            p[2].clone(),
            p[3].clone(),
            p[4].clone(),
        );
        let m = |e: usize| (p[5 + 2 * e].clone(), p[6 + 2 * e].clone());
        let a = |k: usize| (cur[G_A + 2 * k].clone(), cur[G_A + 2 * k + 1].clone());
        let b = |k: usize| (cur[G_B + 2 * k].clone(), cur[G_B + 2 * k + 1].clone());
        let r = |k: usize| (cur[G_R + 2 * k].clone(), cur[G_R + 2 * k + 1].clone());

        let pow16: AB::Expr = F::from_u64(1 << 16).into();
        for c in 0..4 {
            for (base, limb, shift, offset) in [
                (G_R, G_RL, R_HI_SHIFT, 0u64),
                (G_B, G_BL, B_HI_SHIFT, B_OFFSET as u64),
            ] {
                let (lo, hi) = (cur[limb + 2 * c].clone(), cur[limb + 2 * c + 1].clone());
                builder.assert_eq(
                    cur[base + c].clone() + F::from_u64(offset),
                    lo.clone() + hi.clone() * pow16.clone(),
                );
                // Padding rows (real = 0) make no queries; their row equation holds with zeros.
                for qv in [lo, hi.clone(), hi * F::from_u64(shift)] {
                    builder.push_interaction(RANGE, [qv], Count::bounded(-real.clone(), 1));
                }
            }
        }

        let cmul = |m: (AB::Expr, AB::Expr), x: (AB::Expr, AB::Expr)| {
            (
                m.0.clone() * x.0.clone() - m.1.clone() * x.1.clone(),
                m.0 * x.1 + m.1 * x.0,
            )
        };
        let (x, y, z, w) = (
            cmul(m(0), a(0)),
            cmul(m(1), a(1)),
            cmul(m(2), a(0)),
            cmul(m(3), a(1)),
        );
        let out = [(x.0 + y.0, x.1 + y.1), (z.0 + w.0, z.1 + w.1)];
        for (k, out) in out.into_iter().enumerate() {
            let id = a(k);
            let want_re =
                active.clone() * out.0 + (one.clone() - active.clone()) * s.clone() * id.0;
            let want_im =
                active.clone() * out.1 + (one.clone() - active.clone()) * s.clone() * id.1;
            builder.assert_eq(b(k).0 * s.clone() + r(k).0, want_re);
            builder.assert_eq(b(k).1 * s.clone() + r(k).1, want_im);
        }

        let t1 = t.clone() + one;
        for (k, idx) in [(0, i), (1, j)] {
            builder.push_interaction(
                MEM,
                [t.clone(), idx.clone(), a(k).0, a(k).1],
                Count::bounded(-real.clone(), 1),
            );
            builder.push_interaction(
                MEM,
                [t1.clone(), idx, b(k).0, b(k).1],
                Count::bounded(real.clone(), 1),
            );
        }
    }
}

impl BatchAir<Cfg> for GateTableAir {}

#[derive(Clone)]
pub struct BoundaryTableAir {
    pub prep: Vec<F>,
    pub min_height: usize,
}

impl BoundaryTableAir {
    pub(crate) fn rows(&self) -> usize {
        padded_rows(self.prep.len() / BP, self.min_height)
    }
    pub(crate) fn main(&self, fin: &[C]) -> RowMajorMatrix<F> {
        let mut v = vec![F::ZERO; self.rows() * 2];
        for (k, x) in fin.iter().enumerate() {
            v[2 * k] = fi(x.0);
            v[2 * k + 1] = fi(x.1);
        }
        RowMajorMatrix::new(v, 2)
    }
}

impl BaseAir<F> for BoundaryTableAir {
    fn width(&self) -> usize {
        2
    }
    fn preprocessed_width(&self) -> usize {
        BP
    }
    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        Some(prep_matrix(&self.prep, BP, self.min_height))
    }
    fn main_next_row_columns(&self) -> Vec<usize> {
        vec![]
    }
    fn preprocessed_next_row_columns(&self) -> Vec<usize> {
        vec![]
    }
}

impl<AB: AirBuilder<F = F> + InteractionBuilder> Air<AB> for BoundaryTableAir {
    fn eval(&self, builder: &mut AB) {
        let p: Vec<AB::Expr> = builder
            .preprocessed()
            .current_slice()
            .iter()
            .map(|&x| x.into())
            .collect();
        let cur: Vec<AB::Expr> = builder
            .main()
            .current_slice()
            .iter()
            .map(|&x| x.into())
            .collect();
        let (real, idx, init, last) = (p[0].clone(), p[1].clone(), p[2].clone(), p[3].clone());
        let zero = AB::Expr::ZERO;
        builder.push_interaction(
            MEM,
            [zero.clone(), idx.clone(), init, zero],
            Count::bounded(real.clone(), 1),
        );
        builder.push_interaction(
            MEM,
            [last, idx.clone(), cur[0].clone(), cur[1].clone()],
            Count::bounded(-real.clone(), 1),
        );
        builder.push_interaction(
            FIN,
            [idx, cur[0].clone(), cur[1].clone()],
            Count::bounded(real, 1),
        );
    }
}

impl BatchAir<Cfg> for BoundaryTableAir {}

#[derive(Clone)]
pub struct RangeTableAir {
    pub prep: Vec<F>,
    pub min_height: usize,
}

impl RangeTableAir {
    pub(crate) fn main(&self, queries: &[u64]) -> RowMajorMatrix<F> {
        let mut mult = vec![0u64; padded_rows(self.prep.len(), self.min_height)];
        // A query outside the table cannot be counted; a forged trace leaves it unbalanced.
        for &q in queries {
            if (q as usize) < (1 << LOG_RANGE) {
                mult[q as usize] += 1;
            }
        }
        RowMajorMatrix::new(mult.into_iter().map(F::from_u64).collect(), 1)
    }
}

impl BaseAir<F> for RangeTableAir {
    fn width(&self) -> usize {
        1
    }
    fn preprocessed_width(&self) -> usize {
        1
    }
    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        Some(prep_matrix(&self.prep, 1, self.min_height))
    }
    fn main_next_row_columns(&self) -> Vec<usize> {
        vec![]
    }
    fn preprocessed_next_row_columns(&self) -> Vec<usize> {
        vec![]
    }
}

impl<AB: AirBuilder<F = F> + InteractionBuilder> Air<AB> for RangeTableAir {
    fn eval(&self, builder: &mut AB) {
        let v: AB::Expr = builder.preprocessed().current_slice()[0].into();
        let mult: AB::Expr = builder.main().current_slice()[0].into();
        builder.push_interaction(RANGE, [v], Count::provided(mult));
    }
}

impl BatchAir<Cfg> for RangeTableAir {}

pub(crate) const D_IN: usize = 0;
pub(crate) const D_OUT: usize = PW;
pub(crate) const D_BLK: usize = 2 * PW;
pub(crate) const D_WIDTH: usize = 2 * PW + RATE;

#[derive(Clone)]
pub struct DigestTableAir {
    pub prep: Vec<F>,
    pub min_height: usize,
}

impl DigestTableAir {
    pub(crate) fn rows(&self) -> usize {
        padded_rows(self.prep.len() / DP, self.min_height)
    }
    pub(crate) fn main(
        &self,
        hashed: &[C],
        ins: &[[F; PW]],
        outs: &[[F; PW]],
    ) -> RowMajorMatrix<F> {
        let mut v = vec![F::ZERO; self.rows() * D_WIDTH];
        for k in 0..ins.len() {
            let row = &mut v[k * D_WIDTH..(k + 1) * D_WIDTH];
            row[D_IN..D_IN + PW].copy_from_slice(&ins[k]);
            row[D_OUT..D_OUT + PW].copy_from_slice(&outs[k]);
            let block = [
                hashed[2 * k].0,
                hashed[2 * k].1,
                hashed[2 * k + 1].0,
                hashed[2 * k + 1].1,
            ];
            for c in 0..RATE {
                row[D_BLK + c] = fi(block[c]);
            }
        }
        RowMajorMatrix::new(v, D_WIDTH)
    }
}

impl BaseAir<F> for DigestTableAir {
    fn width(&self) -> usize {
        D_WIDTH
    }
    fn preprocessed_width(&self) -> usize {
        DP
    }
    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        Some(prep_matrix(&self.prep, DP, self.min_height))
    }
    fn preprocessed_next_row_columns(&self) -> Vec<usize> {
        vec![0]
    }
}

impl<AB: AirBuilder<F = F> + InteractionBuilder> Air<AB> for DigestTableAir {
    fn eval(&self, builder: &mut AB) {
        let prep = builder.preprocessed();
        let p: Vec<AB::Expr> = prep.current_slice().iter().map(|&x| x.into()).collect();
        let next_real: AB::Expr = prep.next_slice()[0].into();
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let nxt: Vec<AB::Expr> = main.next_slice().iter().map(|&x| x.into()).collect();
        let (real, idx0) = (p[0].clone(), p[2].clone());
        for c in 0..PW {
            let blk = if c < RATE {
                cur[D_BLK + c].clone()
            } else {
                AB::Expr::ZERO
            };
            let first = builder.is_first_row();
            builder.assert_zero(first * (cur[D_IN + c].clone() - blk));
            let next_blk = if c < RATE {
                nxt[D_BLK + c].clone()
            } else {
                AB::Expr::ZERO
            };
            let transition = builder.is_transition();
            builder.assert_zero(
                transition
                    * next_real.clone()
                    * (nxt[D_IN + c].clone() - cur[D_OUT + c].clone() - next_blk),
            );
        }
        let perm: Vec<AB::Expr> = (0..2 * PW).map(|c| cur[c].clone()).collect();
        builder.push_interaction(PERM, perm, Count::bounded(-real.clone(), 1));
        builder.push_interaction(
            FIN,
            [idx0.clone(), cur[D_BLK].clone(), cur[D_BLK + 1].clone()],
            Count::bounded(-real.clone(), 1),
        );
        builder.push_interaction(
            FIN,
            [
                idx0 + AB::Expr::ONE,
                cur[D_BLK + 2].clone(),
                cur[D_BLK + 3].clone(),
            ],
            Count::bounded(-real, 1),
        );
        // The last row creates the digest witnesses on the circuit's witness bus.
        for c in 0..DIGEST_LEN {
            builder.push_interaction(
                "WitnessChecks",
                [p[3 + 2 * c].clone(), cur[D_OUT + c].clone()],
                Count::bounded(p[4 + 2 * c].clone(), 1),
            );
        }
    }
}

impl BatchAir<Cfg> for DigestTableAir {}

/// Poseidon2 permutation table: provides (input, output) on `wqc_perm` per real row.
#[derive(Clone)]
pub struct PermTableAir {
    pub prep: Vec<F>,
    pub min_height: usize,
    inner: P2Air,
}

impl PermTableAir {
    pub fn new(prep: Vec<F>, min_height: usize) -> Self {
        Self {
            prep,
            min_height,
            inner: P2Air::new(round_constants()),
        }
    }
    pub(crate) fn rows(&self) -> usize {
        padded_rows(self.prep.len() / PP, self.min_height)
    }
    pub(crate) fn main(&self, ins: &[[F; PW]]) -> RowMajorMatrix<F> {
        let mut inputs = ins.to_vec();
        inputs.resize(self.rows(), [F::ZERO; PW]);
        perm_trace(inputs)
    }
}

impl BaseAir<F> for PermTableAir {
    fn width(&self) -> usize {
        <P2Air as BaseAir<F>>::width(&self.inner)
    }
    fn preprocessed_width(&self) -> usize {
        PP
    }
    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        Some(prep_matrix(&self.prep, PP, self.min_height))
    }
    fn main_next_row_columns(&self) -> Vec<usize> {
        <P2Air as BaseAir<F>>::main_next_row_columns(&self.inner)
    }
    fn preprocessed_next_row_columns(&self) -> Vec<usize> {
        vec![]
    }
}

impl<AB: AirBuilder<F = F> + InteractionBuilder> Air<AB> for PermTableAir {
    fn eval(&self, builder: &mut AB) {
        self.inner.eval(builder);
        let real: AB::Expr = builder.preprocessed().current_slice()[0].into();
        let main = builder.main();
        let cols: &P2Cols<AB::Var> = main.current_slice().borrow();
        let fields: Vec<AB::Expr> = cols
            .inputs
            .iter()
            .chain(cols.ending_full_rounds[HALF - 1].post.iter())
            .map(|&x| x.into())
            .collect();
        builder.push_interaction(PERM, fields, Count::bounded(real, 1));
    }
}

impl BatchAir<Cfg> for PermTableAir {}

//! The sampling tables (see [`crate::born`]): the weight table over basis states, the draw
//! table, the sampling permutations, and the counts with their digest.

use crate::born::*;
use crate::digest::*;
use crate::exec::*;
use crate::tables::*;
use crate::{Cfg, F};
use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_circuit_prover::BatchAir;
use p3_field::{Field, PrimeCharacteristicRing};
use p3_lookup::{Count, InteractionBuilder};
use p3_matrix::dense::RowMajorMatrix;

pub(crate) const BORN: &str = "wqc_born";
pub(crate) const OUT: &str = "wqc_out";
pub(crate) const PRF: &str = "wqc_prf";

/// Weight table preprocessed: real, basis index, outcome, is_last.
pub(crate) const WP: usize = 4;
const W_RE: usize = 0;
const W_IM: usize = 1;
const W_CUM: usize = 2;
const W_NXT: usize = 3;
const W_MULT: usize = 4;
const W_REJ: usize = 5;
const W_WIDTH: usize = 6;

/// Draw table preprocessed: real, draw index, shots, is_first, then on the first row the
/// witness indices of seed_lo, seed_hi and shots.
pub(crate) const RP: usize = 7;
const R_SEED: usize = 0;
const R_R: usize = 2;
const R_L: usize = 3; // l0, l1, l2 (16 bits), l3lo (9 bits), l3hi (7 bits)
const R_W: usize = 8;
const R_B: usize = 9;
const R_LO: usize = 10;
const R_HI: usize = 11;
const R_ACC: usize = 12;
const R_D: usize = 13; // u − lo: three 16-bit limbs and a 9-bit one
const R_E: usize = 17; // hi − 1 − u, likewise
const R_LIVE: usize = 21;
const R_CNT: usize = 22;
const R_WIDTH: usize = 23;

/// Sampling permutation table preprocessed: real, permutation index.
pub(crate) const FP: usize = 2;
const F_WIDTH: usize = 2 * PW;

/// Counts table preprocessed: real, first register value of the block, is_last, then
/// (output witness index, multiplicity) per digest word.
pub(crate) const CP: usize = 3 + 2 * DIGEST_LEN;
const C_CNT: usize = 0;
const C_IN: usize = RATE;
const C_OUT: usize = RATE + PW;
const C_WIDTH: usize = RATE + 2 * PW;

const TOP_BITS: u32 = U_BITS - 48; // 9: the top limb of a 57-bit value

fn exprs<AB: AirBuilder>(s: &[AB::Var]) -> Vec<AB::Expr> {
    s.iter().map(|&x| x.into()).collect()
}

/// `x` from limbs of 16, 16, 16 and `TOP_BITS` bits, and the range queries proving the sizes.
fn limbs57(x: u64) -> [u64; 4] {
    [x & 0xffff, (x >> 16) & 0xffff, (x >> 32) & 0xffff, x >> 48]
}
fn limb_queries(l: [u64; 4], q: &mut Vec<u64>) {
    q.extend([l[0], l[1], l[2], l[3], l[3] << (16 - TOP_BITS)]);
}

pub(crate) fn draw_range_queries(draws: &[Draw]) -> Vec<u64> {
    let mut q = Vec::with_capacity(draws.len() * 17);
    for d in draws {
        let r = limbs_r(d.r);
        q.extend([r[0], r[1], r[2], r[3], r[3] << (16 - TOP_BITS)]);
        q.extend([r[4], r[4] << TOP_BITS]);
        let (dd, ee) = if d.live {
            (
                d.u.wrapping_sub(d.lo),
                d.hi.wrapping_sub(1).wrapping_sub(d.u),
            )
        } else {
            (0, 0)
        };
        limb_queries(limbs57(dd), &mut q);
        limb_queries(limbs57(ee), &mut q);
    }
    q
}

/// `r` as l0, l1, l2 (16 bits), l3lo (`TOP_BITS`), l3hi (7 bits).
fn limbs_r(r: u64) -> [u64; 5] {
    let l3 = r >> 48;
    [
        r & 0xffff,
        (r >> 16) & 0xffff,
        (r >> 32) & 0xffff,
        l3 & ((1 << TOP_BITS) - 1),
        l3 >> TOP_BITS,
    ]
}

fn pow2<E: PrimeCharacteristicRing>(k: u32) -> E {
    E::from_u64(1u64 << k)
}

fn limb_sum<E: PrimeCharacteristicRing + Clone>(l: &[E]) -> E {
    l[0].clone()
        + l[1].clone() * pow2::<E>(16)
        + l[2].clone() * pow2::<E>(32)
        + l[3].clone() * pow2::<E>(48)
}

/// Weight table: one row per basis state, in index order, with the running sum of weights.
#[derive(Clone)]
pub struct WeightTableAir {
    pub prep: Vec<F>,
    pub min_height: usize,
}

impl WeightTableAir {
    pub(crate) fn rows(&self) -> usize {
        padded_rows(self.prep.len() / WP, self.min_height)
    }
    pub(crate) fn main(&self, fin: &[C], run: &BornRun) -> RowMajorMatrix<F> {
        let mut v = vec![F::ZERO; self.rows() * W_WIDTH];
        for (b, &(re, im)) in fin.iter().enumerate() {
            let row = &mut v[b * W_WIDTH..(b + 1) * W_WIDTH];
            row[W_RE] = fi(re);
            row[W_IM] = fi(im);
            row[W_CUM] = F::from_u64(run.cum[b]);
            row[W_NXT] = F::from_u64(run.cum[b + 1]);
            row[W_MULT] = F::from_u64(run.hits[b]);
            if b + 1 == fin.len() {
                row[W_REJ] = F::from_u64(run.rejects);
            }
        }
        RowMajorMatrix::new(v, W_WIDTH)
    }
}

impl BaseAir<F> for WeightTableAir {
    fn width(&self) -> usize {
        W_WIDTH
    }
    fn preprocessed_width(&self) -> usize {
        WP
    }
    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        Some(prep_matrix(&self.prep, WP, self.min_height))
    }
    fn main_next_row_columns(&self) -> Vec<usize> {
        vec![W_CUM]
    }
    fn preprocessed_next_row_columns(&self) -> Vec<usize> {
        vec![0]
    }
}

impl<AB: AirBuilder<F = F> + InteractionBuilder> Air<AB> for WeightTableAir {
    fn eval(&self, builder: &mut AB) {
        let prep = builder.preprocessed();
        let p = exprs::<AB>(prep.current_slice());
        let next_real: AB::Expr = prep.next_slice()[0].into();
        let main = builder.main();
        let cur = exprs::<AB>(main.current_slice());
        let next_cum: AB::Expr = main.next_slice()[W_CUM].into();
        let (real, b, outcome, last) = (p[0].clone(), p[1].clone(), p[2].clone(), p[3].clone());
        let (re, im) = (cur[W_RE].clone(), cur[W_IM].clone());
        let (cum, nxt) = (cur[W_CUM].clone(), cur[W_NXT].clone());

        builder.when_first_row().assert_zero(cum.clone());
        builder.assert_eq(
            nxt.clone(),
            cum.clone() + re.clone() * re.clone() + im.clone() * im.clone(),
        );
        builder
            .when_transition()
            .assert_zero(next_real * (next_cum - nxt.clone()));

        // The final logical amplitude of basis state b, from the boundary table.
        builder.push_interaction(FIN, [b.clone(), re, im], Count::bounded(-real.clone(), 1));
        // The interval [C_{b−1}, C_b) a draw lands in, and the register it reports.
        let mult = real * cur[W_MULT].clone();
        builder.push_interaction(
            BORN,
            [b.clone(), cum, nxt.clone(), AB::Expr::ONE],
            Count::provided(mult.clone()),
        );
        builder.push_interaction(OUT, [outcome], Count::provided(mult));
        // The last row also provides the rejection interval [T, 2^57), index 2^n.
        builder.push_interaction(
            BORN,
            [
                b + AB::Expr::ONE,
                nxt,
                pow2::<AB::Expr>(U_BITS),
                AB::Expr::ZERO,
            ],
            Count::provided(last * cur[W_REJ].clone()),
        );
    }
}

impl BatchAir<Cfg> for WeightTableAir {}

/// Draw table: one row per draw, in draw order.
#[derive(Clone)]
pub struct DrawTableAir {
    pub prep: Vec<F>,
    pub min_height: usize,
}

impl DrawTableAir {
    pub(crate) fn rows(&self) -> usize {
        padded_rows(self.prep.len() / RP, self.min_height)
    }
    pub(crate) fn main(&self, seed: u64, run: &BornRun) -> RowMajorMatrix<F> {
        let h = self.rows();
        let mut v = vec![F::ZERO; h * R_WIDTH];
        let [lo, hi] = seed_words(seed);
        let shots = run.draws.iter().filter(|d| d.live && d.accepted).count() as u64;
        for k in 0..h {
            let row = &mut v[k * R_WIDTH..(k + 1) * R_WIDTH];
            row[R_SEED] = F::from_u64(lo);
            row[R_SEED + 1] = F::from_u64(hi);
            let Some(d) = run.draws.get(k) else {
                row[R_CNT] = F::from_u64(shots);
                continue;
            };
            row[R_R] = F::from_u64(d.r);
            for (c, l) in limbs_r(d.r).into_iter().enumerate() {
                row[R_L + c] = F::from_u64(l);
            }
            let hi32 = F::from_u64(d.r >> 32) - F::from_u64(0xffff_ffff);
            row[R_W] = hi32.try_inverse().unwrap_or(F::ZERO);
            row[R_CNT] = F::from_u64(d.before);
            if !d.live {
                continue;
            }
            row[R_LIVE] = F::ONE;
            row[R_B] = F::from_usize(d.b);
            row[R_LO] = F::from_u64(d.lo);
            row[R_HI] = F::from_u64(d.hi);
            row[R_ACC] = F::from_bool(d.accepted);
            // Wrapping only for forged draws, which the range checks then reject.
            for (c, l) in limbs57(d.u.wrapping_sub(d.lo)).into_iter().enumerate() {
                row[R_D + c] = F::from_u64(l);
            }
            for (c, l) in limbs57(d.hi.wrapping_sub(1).wrapping_sub(d.u))
                .into_iter()
                .enumerate()
            {
                row[R_E + c] = F::from_u64(l);
            }
        }
        RowMajorMatrix::new(v, R_WIDTH)
    }
}

impl BaseAir<F> for DrawTableAir {
    fn width(&self) -> usize {
        R_WIDTH
    }
    fn preprocessed_width(&self) -> usize {
        RP
    }
    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        Some(prep_matrix(&self.prep, RP, self.min_height))
    }
    fn main_next_row_columns(&self) -> Vec<usize> {
        vec![R_SEED, R_SEED + 1, R_LIVE, R_CNT]
    }
    fn preprocessed_next_row_columns(&self) -> Vec<usize> {
        vec![]
    }
}

impl<AB: AirBuilder<F = F> + InteractionBuilder> Air<AB> for DrawTableAir {
    fn eval(&self, builder: &mut AB) {
        let p = exprs::<AB>(builder.preprocessed().current_slice());
        let main = builder.main();
        let cur = exprs::<AB>(main.current_slice());
        let nxt = exprs::<AB>(main.next_slice());
        let (real, j, shots, first) = (p[0].clone(), p[1].clone(), p[2].clone(), p[3].clone());
        let one = AB::Expr::ONE;
        let l = |c: usize| cur[R_L + c].clone();

        // r = u + l3hi·2^57, u its low 57 bits; canonical: if the high 32 bits are all ones
        // the low 32 are zero (w is the inverse of hi32 − (2^32 − 1) when that is nonzero).
        let u = limb_sum(&[l(0), l(1), l(2), l(3)]);
        builder.assert_eq(
            cur[R_R].clone(),
            u.clone() + l(4) * pow2::<AB::Expr>(U_BITS),
        );
        let hi32 = l(2) + (l(3) + l(4) * pow2::<AB::Expr>(TOP_BITS)) * pow2::<AB::Expr>(16);
        let lo32 = l(0) + l(1) * pow2::<AB::Expr>(16);
        let t = hi32 - AB::Expr::from_u64(0xffff_ffff);
        builder.assert_zero(lo32 * (one.clone() - t * cur[R_W].clone()));

        let range = |builder: &mut AB, x: AB::Expr| {
            builder.push_interaction(RANGE, [x], Count::bounded(-real.clone(), 1));
        };
        for c in 0..3 {
            range(builder, l(c));
        }
        range(builder, l(3));
        range(builder, l(3) * pow2::<AB::Expr>(16 - TOP_BITS));
        range(builder, l(4));
        range(builder, l(4) * pow2::<AB::Expr>(TOP_BITS));
        for base in [R_D, R_E] {
            for c in 0..4 {
                range(builder, cur[base + c].clone());
            }
            range(
                builder,
                cur[base + 3].clone() * pow2::<AB::Expr>(16 - TOP_BITS),
            );
        }

        // A live draw lands in [lo, hi): u − lo and hi − 1 − u are below 2^57.
        let live = cur[R_LIVE].clone();
        let (lo, hi) = (cur[R_LO].clone(), cur[R_HI].clone());
        let d = limb_sum(&cur[R_D..R_D + 4]);
        let e = limb_sum(&cur[R_E..R_E + 4]);
        builder.assert_zero(live.clone() * (u.clone() - lo.clone() - d));
        builder.assert_zero(live.clone() * (hi.clone() - one.clone() - u - e));
        builder.assert_bool(live.clone());
        builder.assert_zero(live.clone() * (one.clone() - real.clone()));
        builder.push_interaction(
            BORN,
            [cur[R_B].clone(), lo, hi, cur[R_ACC].clone()],
            Count::bounded(-live.clone(), 1),
        );

        // The draw's word of the sampling permutation.
        builder.push_interaction(
            PRF,
            [
                cur[R_SEED].clone(),
                cur[R_SEED + 1].clone(),
                j,
                cur[R_R].clone(),
            ],
            Count::bounded(-real.clone(), 1),
        );

        // Draws are live until `shots` are accepted, then dead to the end.
        let cnt = cur[R_CNT].clone();
        let cnt_after = cnt.clone() + live.clone() * cur[R_ACC].clone();
        builder.when_first_row().assert_zero(cnt.clone());
        builder.when_first_row().assert_one(live.clone());
        let mut tr = builder.when_transition();
        tr.assert_eq(nxt[R_CNT].clone(), cnt_after.clone());
        tr.assert_eq(nxt[R_SEED].clone(), cur[R_SEED].clone());
        tr.assert_eq(nxt[R_SEED + 1].clone(), cur[R_SEED + 1].clone());
        tr.assert_zero((one.clone() - live.clone()) * nxt[R_LIVE].clone());
        tr.assert_zero((live.clone() - nxt[R_LIVE].clone()) * (nxt[R_CNT].clone() - shots.clone()));
        builder
            .when_last_row()
            .assert_zero(live * (cnt_after - shots.clone()));

        // The first row reads the seed and the shot count from the statement.
        for (c, value) in [cur[R_SEED].clone(), cur[R_SEED + 1].clone(), shots]
            .into_iter()
            .enumerate()
        {
            builder.push_interaction(
                "WitnessChecks",
                [p[4 + c].clone(), value],
                Count::bounded(-first.clone(), 1),
            );
        }
    }
}

impl BatchAir<Cfg> for DrawTableAir {}

/// Sampling permutations: row k provides draws 4k … 4k+3 under the seed in its input.
#[derive(Clone)]
pub struct PrfTableAir {
    pub prep: Vec<F>,
    pub min_height: usize,
}

impl PrfTableAir {
    pub(crate) fn rows(&self) -> usize {
        padded_rows(self.prep.len() / FP, self.min_height)
    }
    pub(crate) fn main(&self, run: &BornRun) -> RowMajorMatrix<F> {
        let mut v = vec![F::ZERO; self.rows() * F_WIDTH];
        for (k, (x, y)) in run.prf_in.iter().zip(&run.prf_out).enumerate() {
            v[k * F_WIDTH..k * F_WIDTH + PW].copy_from_slice(x);
            v[k * F_WIDTH + PW..(k + 1) * F_WIDTH].copy_from_slice(y);
        }
        RowMajorMatrix::new(v, F_WIDTH)
    }
}

impl BaseAir<F> for PrfTableAir {
    fn width(&self) -> usize {
        F_WIDTH
    }
    fn preprocessed_width(&self) -> usize {
        FP
    }
    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        Some(prep_matrix(&self.prep, FP, self.min_height))
    }
    fn main_next_row_columns(&self) -> Vec<usize> {
        vec![]
    }
    fn preprocessed_next_row_columns(&self) -> Vec<usize> {
        vec![]
    }
}

impl<AB: AirBuilder<F = F> + InteractionBuilder> Air<AB> for PrfTableAir {
    fn eval(&self, builder: &mut AB) {
        let p = exprs::<AB>(builder.preprocessed().current_slice());
        let cur = exprs::<AB>(builder.main().current_slice());
        let (real, k) = (p[0].clone(), p[1].clone());
        builder.assert_zero(real.clone() * (cur[2].clone() - k.clone()));
        for (c, x) in cur.iter().enumerate().take(PW).skip(3) {
            let want = if c == RATE {
                AB::Expr::from_u64(PRF_TAG)
            } else {
                AB::Expr::ZERO
            };
            builder.assert_zero(real.clone() * (x.clone() - want));
        }
        builder.push_interaction(PERM, cur.clone(), Count::bounded(-real.clone(), 1));
        for c in 0..RATE {
            builder.push_interaction(
                PRF,
                [
                    cur[0].clone(),
                    cur[1].clone(),
                    k.clone() * AB::Expr::from_usize(RATE) + AB::Expr::from_usize(c),
                    cur[PW + c].clone(),
                ],
                Count::provided(real.clone()),
            );
        }
    }
}

impl BatchAir<Cfg> for PrfTableAir {}

/// Counts table: four register values per row, sponged into the counts digest.
#[derive(Clone)]
pub struct CountTableAir {
    pub prep: Vec<F>,
    pub min_height: usize,
}

impl CountTableAir {
    pub(crate) fn rows(&self) -> usize {
        padded_rows(self.prep.len() / CP, self.min_height)
    }
    pub(crate) fn main(
        &self,
        counts: &[u64],
        ins: &[[F; PW]],
        outs: &[[F; PW]],
    ) -> RowMajorMatrix<F> {
        let mut v = vec![F::ZERO; self.rows() * C_WIDTH];
        for k in 0..ins.len() {
            let row = &mut v[k * C_WIDTH..(k + 1) * C_WIDTH];
            for c in 0..RATE {
                row[C_CNT + c] = F::from_u64(counts[RATE * k + c]);
            }
            row[C_IN..C_IN + PW].copy_from_slice(&ins[k]);
            row[C_OUT..C_OUT + PW].copy_from_slice(&outs[k]);
        }
        RowMajorMatrix::new(v, C_WIDTH)
    }
}

impl BaseAir<F> for CountTableAir {
    fn width(&self) -> usize {
        C_WIDTH
    }
    fn preprocessed_width(&self) -> usize {
        CP
    }
    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        Some(prep_matrix(&self.prep, CP, self.min_height))
    }
    fn main_next_row_columns(&self) -> Vec<usize> {
        (C_CNT..C_IN + PW).collect()
    }
    fn preprocessed_next_row_columns(&self) -> Vec<usize> {
        vec![0]
    }
}

impl<AB: AirBuilder<F = F> + InteractionBuilder> Air<AB> for CountTableAir {
    fn eval(&self, builder: &mut AB) {
        let prep = builder.preprocessed();
        let p = exprs::<AB>(prep.current_slice());
        let next_real: AB::Expr = prep.next_slice()[0].into();
        let main = builder.main();
        let cur = exprs::<AB>(main.current_slice());
        let nxt = exprs::<AB>(main.next_slice());
        let (real, k0) = (p[0].clone(), p[1].clone());
        for c in 0..PW {
            let (blk, next_blk) = if c < RATE {
                (cur[C_CNT + c].clone(), nxt[C_CNT + c].clone())
            } else {
                (AB::Expr::ZERO, AB::Expr::ZERO)
            };
            builder
                .when_first_row()
                .assert_eq(cur[C_IN + c].clone(), blk);
            builder.when_transition().assert_zero(
                next_real.clone() * (nxt[C_IN + c].clone() - cur[C_OUT + c].clone() - next_blk),
            );
        }
        let perm: Vec<AB::Expr> = cur[C_IN..C_IN + 2 * PW].to_vec();
        builder.push_interaction(PERM, perm, Count::bounded(-real.clone(), 1));
        // Register k0 + c was reported count_c times.
        for c in 0..RATE {
            builder.push_interaction(
                OUT,
                [k0.clone() + AB::Expr::from_usize(c)],
                Count::provided(-(real.clone() * cur[C_CNT + c].clone())),
            );
        }
        // The last row creates the counts digest witnesses.
        for c in 0..DIGEST_LEN {
            builder.push_interaction(
                "WitnessChecks",
                [p[3 + 2 * c].clone(), cur[C_OUT + c].clone()],
                Count::bounded(p[4 + 2 * c].clone(), 1),
            );
        }
    }
}

impl BatchAir<Cfg> for CountTableAir {}

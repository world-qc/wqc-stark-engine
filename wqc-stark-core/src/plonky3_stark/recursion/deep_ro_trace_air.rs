//! R3-M3c2: in-circuit DEEP + λ for AggregationAir trace openings (`DeepRoTraceAir`).
//!
//! One STARK proves `deep(ζ) + α^{132}·deep(ζ_next) − λ·v_n` for width-66 openings.
//! Horner running `pow`/`acc` live in publics (degree ≤ 2).

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::dense::RowMajorMatrix;
use p3_mersenne_31::Mersenne31;
use p3_uni_stark::{prove, verify};

use crate::air::pad_air_matrix_for_uni_stark;
use crate::plonky3_stark::aggregation_air::AGG_WIDTH;
use crate::plonky3_stark::config::{devnet_circle_config, Challenge, Val, WqcStarkConfig};

use super::deep_ro_native::deep_ro_trace_witness;
use super::ef_limbs::{
    ef_add_limbs, ef_assert_eq, ef_mul_limbs, ef_scale_by_base, ef_square_limbs, ef_sub_limbs,
};
use super::fri_fold_native::{challenge_to_limbs, limbs_to_challenge};

const W: usize = AGG_WIDTH; // 66

/// Public layout length for W=66 trace DeepRo.
///
/// sx,sy | at[6] | atn[6] | alpha[3] | px[66] | pz_local[198] | pz_next[198]
/// | alpha2..64[18] | alpha66[3] | alpha132[3]
/// | deep0 (re/im/numer/denom/linear/out_pre)[18] | pow0[198] | acc0[198]
/// | deep1 […][18] | pow1[198] | acc1[198]
/// | combined[3] | lambda[3] | v_n | out[3]
pub const DEEP_RO_TRACE_NUM_PUBLIC: usize = 2
    + 6
    + 6
    + 3
    + W
    + W * 3
    + W * 3
    + 18
    + 3
    + 3
    + 18
    + W * 3
    + W * 3
    + 18
    + W * 3
    + W * 3
    + 3
    + 3
    + 1
    + 3; // 1341

pub const DEEP_RO_TRACE_WIDTH: usize = 1;

#[derive(Copy, Clone, Debug)]
pub struct DeepRoTraceAir;

impl<F: Field> BaseAir<F> for DeepRoTraceAir {
    fn width(&self) -> usize {
        DEEP_RO_TRACE_WIDTH
    }

    fn max_constraint_degree(&self) -> Option<usize> {
        Some(2)
    }

    fn num_public_values(&self) -> usize {
        DEEP_RO_TRACE_NUM_PUBLIC
    }
}

fn ef3<AB: AirBuilder>(pv: &[AB::Expr], off: usize) -> [AB::Expr; 3] {
    [pv[off].clone(), pv[off + 1].clone(), pv[off + 2].clone()]
}

#[allow(clippy::too_many_arguments)]
fn constrain_vp_numer_denom<AB: AirBuilder>(
    builder: &mut AB,
    sx: AB::Expr,
    sy: AB::Expr,
    at_x: &[AB::Expr; 3],
    at_y: &[AB::Expr; 3],
    alpha_pow_w: &[AB::Expr; 3],
    re: &[AB::Expr; 3],
    im: &[AB::Expr; 3],
    numer: &[AB::Expr; 3],
    denom: &[AB::Expr; 3],
) where
    AB::F: Field + PrimeCharacteristicRing,
{
    let one = AB::Expr::ONE;
    let zero = AB::Expr::ZERO;
    let at_x_sx = ef_scale_by_base::<AB>(at_x, sx.clone());
    let at_y_sy = ef_scale_by_base::<AB>(at_y, sy.clone());
    let diff_x = ef_add_limbs::<AB>(&at_x_sx, &at_y_sy);
    let at_x_sy = ef_scale_by_base::<AB>(at_x, sy);
    let at_y_sx = ef_scale_by_base::<AB>(at_y, sx);
    let diff_y = ef_sub_limbs::<AB>(&at_x_sy, &at_y_sx);
    let re_exp = [
        one - diff_x[0].clone(),
        zero.clone() - diff_x[1].clone(),
        zero.clone() - diff_x[2].clone(),
    ];
    ef_assert_eq(builder, &re_exp, re);
    let im_exp = [
        zero.clone() - diff_y[0].clone(),
        zero.clone() - diff_y[1].clone(),
        zero.clone() - diff_y[2].clone(),
    ];
    ef_assert_eq(builder, &im_exp, im);

    let a_im = ef_mul_limbs::<AB>(alpha_pow_w, im);
    let numer_exp = ef_sub_limbs::<AB>(re, &a_im);
    ef_assert_eq(builder, &numer_exp, numer);

    let re2 = ef_square_limbs::<AB>(re);
    let im2 = ef_square_limbs::<AB>(im);
    let denom_exp = ef_add_limbs::<AB>(&re2, &im2);
    ef_assert_eq(builder, &denom_exp, denom);
}

#[allow(clippy::too_many_arguments)]
fn constrain_horner<AB: AirBuilder>(
    builder: &mut AB,
    alpha: &[AB::Expr; 3],
    px_off: usize,
    pz_off: usize,
    pow_off: usize,
    acc_off: usize,
    linear: &[AB::Expr; 3],
    pv: &[AB::Expr],
) where
    AB::F: Field + PrimeCharacteristicRing,
{
    let zero = AB::Expr::ZERO;
    let one = AB::Expr::ONE;

    // pow[0] = 1
    let pow0 = ef3::<AB>(pv, pow_off);
    ef_assert_eq(builder, &pow0, &[one.clone(), zero.clone(), zero.clone()]);

    // acc[0] = c[0]
    let px0 = pv[px_off].clone();
    let pz0 = ef3::<AB>(pv, pz_off);
    let c0 = [
        px0 - pz0[0].clone(),
        zero.clone() - pz0[1].clone(),
        zero.clone() - pz0[2].clone(),
    ];
    let acc0 = ef3::<AB>(pv, acc_off);
    ef_assert_eq(builder, &acc0, &c0);

    for i in 0..W - 1 {
        let pow_i = ef3::<AB>(pv, pow_off + i * 3);
        let pow_n = ef3::<AB>(pv, pow_off + (i + 1) * 3);
        let pow_exp = ef_mul_limbs::<AB>(&pow_i, alpha);
        ef_assert_eq(builder, &pow_exp, &pow_n);

        let px = pv[px_off + i + 1].clone();
        let pz = ef3::<AB>(pv, pz_off + (i + 1) * 3);
        let c = [
            px - pz[0].clone(),
            zero.clone() - pz[1].clone(),
            zero.clone() - pz[2].clone(),
        ];
        let term = ef_mul_limbs::<AB>(&pow_n, &c);
        let acc_i = ef3::<AB>(pv, acc_off + i * 3);
        let acc_n = ef3::<AB>(pv, acc_off + (i + 1) * 3);
        let acc_exp = ef_add_limbs::<AB>(&acc_i, &term);
        ef_assert_eq(builder, &acc_exp, &acc_n);
    }

    let acc_last = ef3::<AB>(pv, acc_off + (W - 1) * 3);
    ef_assert_eq(builder, &acc_last, linear);
}

impl<AB: AirBuilder> Air<AB> for DeepRoTraceAir
where
    AB::F: Field + PrimeCharacteristicRing,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let curr: Vec<AB::Var> = main.current_slice().to_vec();
        let next: Vec<AB::Var> = main.next_slice().to_vec();
        let one = AB::Expr::ONE;

        let ok: AB::Expr = curr[0].into();
        builder.assert_zero(ok.clone() * (ok.clone() - one.clone()));
        builder.assert_zero(ok.clone() - one.clone());
        builder
            .when_transition()
            .assert_zero(next[0].into() - curr[0].into());

        let pv: Vec<AB::Expr> = builder
            .public_values()
            .iter()
            .map(|v| (*v).into())
            .collect();
        debug_assert_eq!(pv.len(), DEEP_RO_TRACE_NUM_PUBLIC);

        let sx = pv[0].clone();
        let sy = pv[1].clone();
        let at_x = ef3::<AB>(&pv, 2);
        let at_y = ef3::<AB>(&pv, 5);
        let atn_x = ef3::<AB>(&pv, 8);
        let atn_y = ef3::<AB>(&pv, 11);
        let alpha = ef3::<AB>(&pv, 14);
        const OFF_PX: usize = 17;
        const OFF_PZ_LOCAL: usize = 17 + W;
        const OFF_PZ_NEXT: usize = 17 + W + W * 3;
        const OFF_A2: usize = 17 + W + W * 3 + W * 3; // 479
        let alpha2 = ef3::<AB>(&pv, OFF_A2);
        let alpha4 = ef3::<AB>(&pv, OFF_A2 + 3);
        let alpha8 = ef3::<AB>(&pv, OFF_A2 + 6);
        let alpha16 = ef3::<AB>(&pv, OFF_A2 + 9);
        let alpha32 = ef3::<AB>(&pv, OFF_A2 + 12);
        let alpha64 = ef3::<AB>(&pv, OFF_A2 + 15);
        let alpha66 = ef3::<AB>(&pv, OFF_A2 + 18);
        let alpha132 = ef3::<AB>(&pv, OFF_A2 + 21);
        const OFF_D0: usize = OFF_A2 + 24; // 503
        let re0 = ef3::<AB>(&pv, OFF_D0);
        let im0 = ef3::<AB>(&pv, OFF_D0 + 3);
        let numer0 = ef3::<AB>(&pv, OFF_D0 + 6);
        let denom0 = ef3::<AB>(&pv, OFF_D0 + 9);
        let linear0 = ef3::<AB>(&pv, OFF_D0 + 12);
        let out_pre0 = ef3::<AB>(&pv, OFF_D0 + 15);
        const OFF_POW0: usize = OFF_D0 + 18;
        const OFF_ACC0: usize = OFF_POW0 + W * 3;
        const OFF_D1: usize = OFF_ACC0 + W * 3;
        let re1 = ef3::<AB>(&pv, OFF_D1);
        let im1 = ef3::<AB>(&pv, OFF_D1 + 3);
        let numer1 = ef3::<AB>(&pv, OFF_D1 + 6);
        let denom1 = ef3::<AB>(&pv, OFF_D1 + 9);
        let linear1 = ef3::<AB>(&pv, OFF_D1 + 12);
        let out_pre1 = ef3::<AB>(&pv, OFF_D1 + 15);
        const OFF_POW1: usize = OFF_D1 + 18;
        const OFF_ACC1: usize = OFF_POW1 + W * 3;
        const OFF_COMBINED: usize = OFF_ACC1 + W * 3;
        let combined = ef3::<AB>(&pv, OFF_COMBINED);
        let lambda = ef3::<AB>(&pv, OFF_COMBINED + 3);
        let v_n = pv[OFF_COMBINED + 6].clone();
        let out = ef3::<AB>(&pv, OFF_COMBINED + 7);

        // α squaring → α^66 → α^132
        let a2_exp = ef_mul_limbs::<AB>(&alpha, &alpha);
        ef_assert_eq(builder, &a2_exp, &alpha2);
        let a4_exp = ef_mul_limbs::<AB>(&alpha2, &alpha2);
        ef_assert_eq(builder, &a4_exp, &alpha4);
        let a8_exp = ef_mul_limbs::<AB>(&alpha4, &alpha4);
        ef_assert_eq(builder, &a8_exp, &alpha8);
        let a16_exp = ef_mul_limbs::<AB>(&alpha8, &alpha8);
        ef_assert_eq(builder, &a16_exp, &alpha16);
        let a32_exp = ef_mul_limbs::<AB>(&alpha16, &alpha16);
        ef_assert_eq(builder, &a32_exp, &alpha32);
        let a64_exp = ef_mul_limbs::<AB>(&alpha32, &alpha32);
        ef_assert_eq(builder, &a64_exp, &alpha64);
        let a66_exp = ef_mul_limbs::<AB>(&alpha64, &alpha2);
        ef_assert_eq(builder, &a66_exp, &alpha66);
        let a132_exp = ef_mul_limbs::<AB>(&alpha66, &alpha66);
        ef_assert_eq(builder, &a132_exp, &alpha132);

        constrain_vp_numer_denom(
            builder,
            sx.clone(),
            sy.clone(),
            &at_x,
            &at_y,
            &alpha66,
            &re0,
            &im0,
            &numer0,
            &denom0,
        );
        constrain_vp_numer_denom(
            builder, sx, sy, &atn_x, &atn_y, &alpha66, &re1, &im1, &numer1, &denom1,
        );

        constrain_horner(
            builder,
            &alpha,
            OFF_PX,
            OFF_PZ_LOCAL,
            OFF_POW0,
            OFF_ACC0,
            &linear0,
            &pv,
        );
        constrain_horner(
            builder,
            &alpha,
            OFF_PX,
            OFF_PZ_NEXT,
            OFF_POW1,
            OFF_ACC1,
            &linear1,
            &pv,
        );

        let lhs0 = ef_mul_limbs::<AB>(&out_pre0, &denom0);
        let rhs0 = ef_mul_limbs::<AB>(&numer0, &linear0);
        ef_assert_eq(builder, &lhs0, &rhs0);
        let lhs1 = ef_mul_limbs::<AB>(&out_pre1, &denom1);
        let rhs1 = ef_mul_limbs::<AB>(&numer1, &linear1);
        ef_assert_eq(builder, &lhs1, &rhs1);

        let a132_d1 = ef_mul_limbs::<AB>(&alpha132, &out_pre1);
        let combined_exp = ef_add_limbs::<AB>(&out_pre0, &a132_d1);
        ef_assert_eq(builder, &combined_exp, &combined);

        let lam_vn = ef_scale_by_base::<AB>(&lambda, v_n);
        let out_exp = ef_sub_limbs::<AB>(&combined, &lam_vn);
        ef_assert_eq(builder, &out_exp, &out);
    }
}

fn push_ef(pv: &mut Vec<Mersenne31>, c: Challenge) {
    pv.extend_from_slice(&challenge_to_limbs(c));
}

fn push_horner_blocks(
    pv: &mut Vec<Mersenne31>,
    alpha: Challenge,
    px: &[Val; W],
    pz: &[Challenge; W],
) {
    let mut pow = Challenge::ONE;
    let mut acc = Challenge::ZERO;
    let mut pows = Vec::with_capacity(W);
    let mut accs = Vec::with_capacity(W);
    for i in 0..W {
        if i > 0 {
            pow *= alpha;
        }
        let c = Challenge::from(px[i]) - pz[i];
        acc += pow * c;
        pows.push(pow);
        accs.push(acc);
    }
    for p in &pows {
        push_ef(pv, *p);
    }
    for a in &accs {
        push_ef(pv, *a);
    }
}

fn push_deep_partial(
    pv: &mut Vec<Mersenne31>,
    re: Challenge,
    im: Challenge,
    numer: Challenge,
    denom: Challenge,
    linear: Challenge,
    out_pre: Challenge,
) {
    push_ef(pv, re);
    push_ef(pv, im);
    push_ef(pv, numer);
    push_ef(pv, denom);
    push_ef(pv, linear);
    push_ef(pv, out_pre);
}

#[allow(clippy::too_many_arguments)]
fn build_public_values(
    sx: Val,
    sy: Val,
    alpha: Challenge,
    px: &[Val; W],
    pz_local: &[Challenge; W],
    pz_next: &[Challenge; W],
    lambda: Challenge,
    log_n: usize,
    zeta: Challenge,
    zeta_next: Challenge,
) -> (Vec<Mersenne31>, Challenge) {
    let w = deep_ro_trace_witness(
        alpha, sx, sy, zeta, zeta_next, px, pz_local, pz_next, lambda, log_n,
    );
    let mut pv = Vec::with_capacity(DEEP_RO_TRACE_NUM_PUBLIC);
    pv.push(sx);
    pv.push(sy);
    push_ef(&mut pv, w.at_x);
    push_ef(&mut pv, w.at_y);
    push_ef(&mut pv, w.atn_x);
    push_ef(&mut pv, w.atn_y);
    push_ef(&mut pv, alpha);
    pv.extend_from_slice(px);
    for pz in pz_local {
        push_ef(&mut pv, *pz);
    }
    for pz in pz_next {
        push_ef(&mut pv, *pz);
    }
    push_ef(&mut pv, w.alpha2);
    push_ef(&mut pv, w.alpha4);
    push_ef(&mut pv, w.alpha8);
    push_ef(&mut pv, w.alpha16);
    push_ef(&mut pv, w.alpha32);
    push_ef(&mut pv, w.alpha64);
    push_ef(&mut pv, w.alpha66);
    push_ef(&mut pv, w.alpha132);
    push_deep_partial(
        &mut pv,
        w.deep0.re,
        w.deep0.im,
        w.deep0.numer,
        w.deep0.denom,
        w.deep0.linear,
        w.deep0.out_pre,
    );
    push_horner_blocks(&mut pv, alpha, px, pz_local);
    push_deep_partial(
        &mut pv,
        w.deep1.re,
        w.deep1.im,
        w.deep1.numer,
        w.deep1.denom,
        w.deep1.linear,
        w.deep1.out_pre,
    );
    push_horner_blocks(&mut pv, alpha, px, pz_next);
    push_ef(&mut pv, w.combined);
    push_ef(&mut pv, lambda);
    pv.push(w.v_n);
    push_ef(&mut pv, w.out);
    debug_assert_eq!(pv.len(), DEEP_RO_TRACE_NUM_PUBLIC);
    (pv, w.out)
}

fn build_matrix() -> RowMajorMatrix<Mersenne31> {
    let values = vec![Mersenne31::ONE, Mersenne31::ONE];
    RowMajorMatrix::new(values, DEEP_RO_TRACE_WIDTH)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeepRoTraceStepProof {
    pub sx: Mersenne31,
    pub sy: Mersenne31,
    pub alpha_limbs: [Mersenne31; 3],
    pub px: [Mersenne31; W],
    pub pz_local_limbs: [[Mersenne31; 3]; W],
    pub pz_next_limbs: [[Mersenne31; 3]; W],
    pub lambda_limbs: [Mersenne31; 3],
    pub v_n: Mersenne31,
    pub out_limbs: [Mersenne31; 3],
    /// Host-bound metadata (not constrained by AIR; used for bind).
    pub log_n: u32,
    pub zeta_limbs: [Mersenne31; 3],
    pub zeta_next_limbs: [Mersenne31; 3],
    pub deep_stark: Vec<u8>,
}

#[allow(clippy::too_many_arguments)]
pub fn generate_deep_ro_trace_proof(
    sx: Val,
    sy: Val,
    alpha: Challenge,
    px: &[Val; W],
    pz_local: &[Challenge; W],
    pz_next: &[Challenge; W],
    lambda: Challenge,
    log_n: usize,
    zeta: Challenge,
    zeta_next: Challenge,
) -> Result<DeepRoTraceStepProof, String> {
    if log_n == 0 || log_n > 16 {
        return Err("log_n out of range".into());
    }
    let (pv, out) = build_public_values(
        sx, sy, alpha, px, pz_local, pz_next, lambda, log_n, zeta, zeta_next,
    );
    let matrix = pad_air_matrix_for_uni_stark(build_matrix());
    p3_air::check_constraints(&DeepRoTraceAir, &matrix, &pv);
    let config = devnet_circle_config();
    let proof = prove(&config, &DeepRoTraceAir, matrix, &pv);
    let deep_stark =
        postcard::to_allocvec(&proof).map_err(|e| format!("postcard encode deep_ro_trace: {e}"))?;
    let mut pz_local_limbs = [[Mersenne31::ZERO; 3]; W];
    let mut pz_next_limbs = [[Mersenne31::ZERO; 3]; W];
    for i in 0..W {
        pz_local_limbs[i] = challenge_to_limbs(pz_local[i]);
        pz_next_limbs[i] = challenge_to_limbs(pz_next[i]);
    }
    Ok(DeepRoTraceStepProof {
        sx,
        sy,
        alpha_limbs: challenge_to_limbs(alpha),
        px: *px,
        pz_local_limbs,
        pz_next_limbs,
        lambda_limbs: challenge_to_limbs(lambda),
        v_n: pv[DEEP_RO_TRACE_NUM_PUBLIC - 4],
        out_limbs: challenge_to_limbs(out),
        log_n: log_n as u32,
        zeta_limbs: challenge_to_limbs(zeta),
        zeta_next_limbs: challenge_to_limbs(zeta_next),
        deep_stark,
    })
}

pub fn verify_deep_ro_trace_proof(proof: &DeepRoTraceStepProof) -> bool {
    let alpha = limbs_to_challenge(proof.alpha_limbs);
    let mut pz_local = [Challenge::ZERO; W];
    let mut pz_next = [Challenge::ZERO; W];
    for i in 0..W {
        pz_local[i] = limbs_to_challenge(proof.pz_local_limbs[i]);
        pz_next[i] = limbs_to_challenge(proof.pz_next_limbs[i]);
    }
    let lambda = limbs_to_challenge(proof.lambda_limbs);
    let zeta = limbs_to_challenge(proof.zeta_limbs);
    let zeta_next = limbs_to_challenge(proof.zeta_next_limbs);
    let out = limbs_to_challenge(proof.out_limbs);
    let (pv, expect_out) = build_public_values(
        proof.sx,
        proof.sy,
        alpha,
        &proof.px,
        &pz_local,
        &pz_next,
        lambda,
        proof.log_n as usize,
        zeta,
        zeta_next,
    );
    if out != expect_out {
        eprintln!("[DeepRoTrace] Failed: native out mismatch");
        return false;
    }
    if proof.v_n != pv[DEEP_RO_TRACE_NUM_PUBLIC - 4] {
        eprintln!("[DeepRoTrace] Failed: v_n mismatch");
        return false;
    }
    let stark: p3_uni_stark::Proof<WqcStarkConfig> = match postcard::from_bytes(&proof.deep_stark) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("[DeepRoTrace] postcard: {e}");
            return false;
        }
    };
    let config = devnet_circle_config();
    match verify(&config, &DeepRoTraceAir, &stark, &pv) {
        Ok(()) => true,
        Err(e) => {
            eprintln!("[DeepRoTrace] STARK: {e:?}");
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{Rng, SeedableRng};

    #[test]
    fn deep_ro_trace_stark_roundtrip() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(77);
        let alpha = Challenge::new([
            Val::from_u32(rng.gen()),
            Val::from_u32(rng.gen()),
            Val::from_u32(rng.gen()),
        ]);
        let zeta = Challenge::new([
            Val::from_u32(rng.gen()),
            Val::from_u32(rng.gen()),
            Val::from_u32(rng.gen()),
        ]);
        let zeta_next = Challenge::new([
            Val::from_u32(rng.gen()),
            Val::from_u32(rng.gen()),
            Val::from_u32(rng.gen()),
        ]);
        let sx = Val::from_u32(3);
        let sy = Val::from_u32(5);
        let mut px = [Val::ZERO; W];
        let mut pz_local = [Challenge::ZERO; W];
        let mut pz_next = [Challenge::ZERO; W];
        for i in 0..W {
            px[i] = Val::from_u32(rng.gen::<u32>() % 50);
            pz_local[i] = Challenge::from(Val::from_u32(rng.gen::<u32>() % 50));
            pz_next[i] = Challenge::from(Val::from_u32(rng.gen::<u32>() % 50));
        }
        let lambda = Challenge::new([Val::from_u32(1), Val::from_u32(2), Val::from_u32(3)]);
        let proof = generate_deep_ro_trace_proof(
            sx, sy, alpha, &px, &pz_local, &pz_next, lambda, 3, zeta, zeta_next,
        )
        .expect("prove");
        assert!(verify_deep_ro_trace_proof(&proof));
    }
}

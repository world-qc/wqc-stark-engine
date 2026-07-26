//! R3-M3c1: in-circuit DEEP + λ for width-3 (EF) openings (`DeepRoAir`).
//!
//! Publics constrain DEEP row reduction and λ correction without division:
//! `out_pre * denom = numer * linear`, then `out = out_pre - λ · v_n`.

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::dense::RowMajorMatrix;
use p3_mersenne_31::Mersenne31;
use p3_uni_stark::{prove, verify};

use crate::air::pad_air_matrix_for_uni_stark;
use crate::plonky3_stark::config::{devnet_circle_config, Challenge, Val, WqcStarkConfig};

use super::deep_ro_native::deep_ro_w3_witness;
use super::ef_limbs::{
    ef_add_limbs, ef_assert_eq, ef_mul_limbs, ef_scale_by_base, ef_square_limbs, ef_sub_limbs,
};
use super::fri_fold_native::{challenge_to_limbs, limbs_to_challenge};

/// Public layout length for W=3 DeepRo.
///
/// sx,sy | at_x[3] at_y[3] | alpha[3] | px[3] | pz[9] | alpha2[3] alpha3[3]
/// | re[3] im[3] | numer[3] denom[3] | linear[3] | out_pre[3] | lambda[3] | v_n | out[3]
pub const DEEP_RO_NUM_PUBLIC: usize = 2 + 6 + 3 + 3 + 9 + 6 + 6 + 6 + 3 + 3 + 3 + 1 + 3; // 54

pub const DEEP_RO_WIDTH: usize = 1;

#[derive(Copy, Clone, Debug)]
pub struct DeepRoAir;

impl<F: Field> BaseAir<F> for DeepRoAir {
    fn width(&self) -> usize {
        DEEP_RO_WIDTH
    }

    fn max_constraint_degree(&self) -> Option<usize> {
        Some(2)
    }

    fn num_public_values(&self) -> usize {
        DEEP_RO_NUM_PUBLIC
    }
}

impl<AB: AirBuilder> Air<AB> for DeepRoAir
where
    AB::F: Field + PrimeCharacteristicRing,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let curr: Vec<AB::Var> = main.current_slice().to_vec();
        let next: Vec<AB::Var> = main.next_slice().to_vec();
        let one = AB::Expr::ONE;
        let zero = AB::Expr::ZERO;

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

        let sx = pv[0].clone();
        let sy = pv[1].clone();
        let at_x = [pv[2].clone(), pv[3].clone(), pv[4].clone()];
        let at_y = [pv[5].clone(), pv[6].clone(), pv[7].clone()];
        let alpha = [pv[8].clone(), pv[9].clone(), pv[10].clone()];
        let px0 = pv[11].clone();
        let px1 = pv[12].clone();
        let px2 = pv[13].clone();
        let pz0 = [pv[14].clone(), pv[15].clone(), pv[16].clone()];
        let pz1 = [pv[17].clone(), pv[18].clone(), pv[19].clone()];
        let pz2 = [pv[20].clone(), pv[21].clone(), pv[22].clone()];
        let alpha2 = [pv[23].clone(), pv[24].clone(), pv[25].clone()];
        let alpha3 = [pv[26].clone(), pv[27].clone(), pv[28].clone()];
        let re = [pv[29].clone(), pv[30].clone(), pv[31].clone()];
        let im = [pv[32].clone(), pv[33].clone(), pv[34].clone()];
        let numer = [pv[35].clone(), pv[36].clone(), pv[37].clone()];
        let denom = [pv[38].clone(), pv[39].clone(), pv[40].clone()];
        let linear = [pv[41].clone(), pv[42].clone(), pv[43].clone()];
        let out_pre = [pv[44].clone(), pv[45].clone(), pv[46].clone()];
        let lambda = [pv[47].clone(), pv[48].clone(), pv[49].clone()];
        let v_n = pv[50].clone();
        let out = [pv[51].clone(), pv[52].clone(), pv[53].clone()];

        let alpha2_exp = ef_mul_limbs::<AB>(&alpha, &alpha);
        ef_assert_eq(builder, &alpha2_exp, &alpha2);
        let alpha3_exp = ef_mul_limbs::<AB>(&alpha2, &alpha);
        ef_assert_eq(builder, &alpha3_exp, &alpha3);

        // v_p: diff_x = at_x*sx + at_y*sy; diff_y = at_x*sy - at_y*sx
        // re = (1,0,0) - diff_x; im = -diff_y
        let at_x_sx = ef_scale_by_base::<AB>(&at_x, sx.clone());
        let at_y_sy = ef_scale_by_base::<AB>(&at_y, sy.clone());
        let diff_x = ef_add_limbs::<AB>(&at_x_sx, &at_y_sy);
        let at_x_sy = ef_scale_by_base::<AB>(&at_x, sy);
        let at_y_sx = ef_scale_by_base::<AB>(&at_y, sx);
        let diff_y = ef_sub_limbs::<AB>(&at_x_sy, &at_y_sx);
        let re_exp = [
            one - diff_x[0].clone(),
            zero.clone() - diff_x[1].clone(),
            zero.clone() - diff_x[2].clone(),
        ];
        ef_assert_eq(builder, &re_exp, &re);
        let im_exp = [
            zero.clone() - diff_y[0].clone(),
            zero.clone() - diff_y[1].clone(),
            zero.clone() - diff_y[2].clone(),
        ];
        ef_assert_eq(builder, &im_exp, &im);

        let a3_im = ef_mul_limbs::<AB>(&alpha3, &im);
        let numer_exp = ef_sub_limbs::<AB>(&re, &a3_im);
        ef_assert_eq(builder, &numer_exp, &numer);

        let re2 = ef_square_limbs::<AB>(&re);
        let im2 = ef_square_limbs::<AB>(&im);
        let denom_exp = ef_add_limbs::<AB>(&re2, &im2);
        ef_assert_eq(builder, &denom_exp, &denom);

        let c0 = [
            px0 - pz0[0].clone(),
            zero.clone() - pz0[1].clone(),
            zero.clone() - pz0[2].clone(),
        ];
        let c1 = [
            px1 - pz1[0].clone(),
            zero.clone() - pz1[1].clone(),
            zero.clone() - pz1[2].clone(),
        ];
        let c2 = [
            px2 - pz2[0].clone(),
            zero.clone() - pz2[1].clone(),
            zero - pz2[2].clone(),
        ];
        let a_c1 = ef_mul_limbs::<AB>(&alpha, &c1);
        let a2_c2 = ef_mul_limbs::<AB>(&alpha2, &c2);
        let lin01 = ef_add_limbs::<AB>(&c0, &a_c1);
        let linear_exp = ef_add_limbs::<AB>(&lin01, &a2_c2);
        ef_assert_eq(builder, &linear_exp, &linear);

        let lhs = ef_mul_limbs::<AB>(&out_pre, &denom);
        let rhs = ef_mul_limbs::<AB>(&numer, &linear);
        ef_assert_eq(builder, &lhs, &rhs);

        let lam_vn = ef_scale_by_base::<AB>(&lambda, v_n);
        let out_exp = ef_sub_limbs::<AB>(&out_pre, &lam_vn);
        ef_assert_eq(builder, &out_exp, &out);
    }
}

#[allow(clippy::too_many_arguments)]
fn build_public_values(
    sx: Val,
    sy: Val,
    alpha: Challenge,
    px: [Val; 3],
    pz: [Challenge; 3],
    lambda: Challenge,
    log_n: usize,
    zeta: Challenge,
) -> (Vec<Mersenne31>, Challenge) {
    let w = deep_ro_w3_witness(alpha, sx, sy, zeta, px, pz, lambda, log_n);
    let mut pv = Vec::with_capacity(DEEP_RO_NUM_PUBLIC);
    pv.push(sx);
    pv.push(sy);
    pv.extend_from_slice(&challenge_to_limbs(w.at_x));
    pv.extend_from_slice(&challenge_to_limbs(w.at_y));
    pv.extend_from_slice(&challenge_to_limbs(alpha));
    pv.extend_from_slice(&px);
    for pz_i in &pz {
        pv.extend_from_slice(&challenge_to_limbs(*pz_i));
    }
    pv.extend_from_slice(&challenge_to_limbs(w.alpha2));
    pv.extend_from_slice(&challenge_to_limbs(w.alpha3));
    pv.extend_from_slice(&challenge_to_limbs(w.re));
    pv.extend_from_slice(&challenge_to_limbs(w.im));
    pv.extend_from_slice(&challenge_to_limbs(w.numer));
    pv.extend_from_slice(&challenge_to_limbs(w.denom));
    pv.extend_from_slice(&challenge_to_limbs(w.linear));
    pv.extend_from_slice(&challenge_to_limbs(w.out_pre));
    pv.extend_from_slice(&challenge_to_limbs(lambda));
    pv.push(w.v_n);
    pv.extend_from_slice(&challenge_to_limbs(w.out));
    debug_assert_eq!(pv.len(), DEEP_RO_NUM_PUBLIC);
    (pv, w.out)
}

fn build_matrix() -> RowMajorMatrix<Mersenne31> {
    let values = vec![Mersenne31::ONE, Mersenne31::ONE];
    RowMajorMatrix::new(values, DEEP_RO_WIDTH)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeepRoStepProof {
    pub sx: Mersenne31,
    pub sy: Mersenne31,
    pub alpha_limbs: [Mersenne31; 3],
    pub px: [Mersenne31; 3],
    pub pz_limbs: [[Mersenne31; 3]; 3],
    pub lambda_limbs: [Mersenne31; 3],
    pub v_n: Mersenne31,
    pub out_limbs: [Mersenne31; 3],
    /// Host-bound metadata (not constrained by AIR; used for bind).
    pub log_n: u32,
    pub zeta_limbs: [Mersenne31; 3],
    pub deep_stark: Vec<u8>,
}

#[allow(clippy::too_many_arguments)]
pub fn generate_deep_ro_proof(
    sx: Val,
    sy: Val,
    alpha: Challenge,
    px: [Val; 3],
    pz: [Challenge; 3],
    lambda: Challenge,
    log_n: usize,
    zeta: Challenge,
) -> Result<DeepRoStepProof, String> {
    if log_n == 0 || log_n > 16 {
        return Err("log_n out of range".into());
    }
    let (pv, out) = build_public_values(sx, sy, alpha, px, pz, lambda, log_n, zeta);
    let matrix = pad_air_matrix_for_uni_stark(build_matrix());
    p3_air::check_constraints(&DeepRoAir, &matrix, &pv);
    let config = devnet_circle_config();
    let proof = prove(&config, &DeepRoAir, matrix, &pv);
    let deep_stark = super::prove_workspace::encode_stark_and_drop(proof, "deep_ro")?;
    Ok(DeepRoStepProof {
        sx,
        sy,
        alpha_limbs: challenge_to_limbs(alpha),
        px,
        pz_limbs: [
            challenge_to_limbs(pz[0]),
            challenge_to_limbs(pz[1]),
            challenge_to_limbs(pz[2]),
        ],
        lambda_limbs: challenge_to_limbs(lambda),
        v_n: pv[50],
        out_limbs: challenge_to_limbs(out),
        log_n: log_n as u32,
        zeta_limbs: challenge_to_limbs(zeta),
        deep_stark,
    })
}

pub fn verify_deep_ro_proof(proof: &DeepRoStepProof) -> bool {
    let alpha = limbs_to_challenge(proof.alpha_limbs);
    let pz = [
        limbs_to_challenge(proof.pz_limbs[0]),
        limbs_to_challenge(proof.pz_limbs[1]),
        limbs_to_challenge(proof.pz_limbs[2]),
    ];
    let lambda = limbs_to_challenge(proof.lambda_limbs);
    let zeta = limbs_to_challenge(proof.zeta_limbs);
    let out = limbs_to_challenge(proof.out_limbs);
    let (pv, expect_out) = build_public_values(
        proof.sx,
        proof.sy,
        alpha,
        proof.px,
        pz,
        lambda,
        proof.log_n as usize,
        zeta,
    );
    if out != expect_out {
        eprintln!("[DeepRo] Failed: native out mismatch");
        return false;
    }
    if proof.v_n != pv[50] {
        eprintln!("[DeepRo] Failed: v_n mismatch");
        return false;
    }
    let stark: p3_uni_stark::Proof<WqcStarkConfig> = match postcard::from_bytes(&proof.deep_stark) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("[DeepRo] postcard: {e}");
            return false;
        }
    };
    let config = devnet_circle_config();
    match verify(&config, &DeepRoAir, &stark, &pv) {
        Ok(()) => true,
        Err(e) => {
            eprintln!("[DeepRo] STARK: {e:?}");
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{Rng, SeedableRng};

    #[test]
    fn deep_ro_stark_roundtrip() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(21);
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
        let sx = Val::from_u32(3);
        let sy = Val::from_u32(5);
        let px = [Val::from_u32(1), Val::from_u32(2), Val::from_u32(4)];
        let pz = [
            Challenge::new([Val::ONE, Val::ZERO, Val::ZERO]),
            Challenge::new([Val::ZERO, Val::ONE, Val::ZERO]),
            Challenge::new([Val::ZERO, Val::ZERO, Val::ONE]),
        ];
        let lambda = Challenge::new([Val::from_u32(7), Val::from_u32(8), Val::from_u32(9)]);
        let proof = generate_deep_ro_proof(sx, sy, alpha, px, pz, lambda, 2, zeta).expect("prove");
        assert!(verify_deep_ro_proof(&proof));
    }
}

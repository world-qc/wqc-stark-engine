//! R3-M3a: in-circuit Circle FRI `fold_x` (arity 2) over Challenge = EF\<M31, 3\>.
//!
//! Publics (all M31): index | log_folded_height | t_inv | beta[3] | v0[3] | v1[3] | out[3]
//! Trace: single stable statement row (width 1 dummy + live flag unused) — actually width 1
//! boolean `ok` fixed to 1. Constraints are purely on public values (degree 2).

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::dense::RowMajorMatrix;
use p3_mersenne_31::Mersenne31;
use p3_uni_stark::{prove, verify};

use crate::air::pad_air_matrix_for_uni_stark;
use crate::plonky3_stark::config::{devnet_circle_config, Challenge, WqcStarkConfig};

use super::fri_fold_native::{
    challenge_to_limbs, fold_x_row, fold_x_twiddle_inv, limbs_to_challenge,
};

/// Public layout length.
pub const FRI_FOLD_NUM_PUBLIC: usize = 1 + 1 + 1 + 3 + 3 + 3 + 3; // 15

/// Trace width: one stable boolean column.
pub const FRI_FOLD_WIDTH: usize = 1;

#[derive(Copy, Clone, Debug)]
pub struct FriFoldAir;

impl<F: Field> BaseAir<F> for FriFoldAir {
    fn width(&self) -> usize {
        FRI_FOLD_WIDTH
    }

    fn max_constraint_degree(&self) -> Option<usize> {
        Some(2)
    }

    fn num_public_values(&self) -> usize {
        FRI_FOLD_NUM_PUBLIC
    }
}

/// Extension mul of two EF elements (binomial X^3 − 5 over Mersenne31).
fn ef_mul_limbs<AB: AirBuilder>(a: &[AB::Expr; 3], b: &[AB::Expr; 3]) -> [AB::Expr; 3]
where
    AB::F: PrimeCharacteristicRing,
{
    let w: AB::Expr = AB::F::from_u32(5).into();
    let a0_b0 = a[0].clone() * b[0].clone();
    let a1_b1 = a[1].clone() * b[1].clone();
    let a2_b2 = a[2].clone() * b[2].clone();
    let c0 = a0_b0.clone()
        + ((a[1].clone() + a[2].clone()) * (b[1].clone() + b[2].clone())
            - a1_b1.clone()
            - a2_b2.clone())
            * w.clone();
    let c1 = (a[0].clone() + a[1].clone()) * (b[0].clone() + b[1].clone())
        - a0_b0.clone()
        - a1_b1.clone()
        + a2_b2.clone() * w;
    let c2 = (a[0].clone() + a[2].clone()) * (b[0].clone() + b[2].clone()) - a0_b0 - a2_b2 + a1_b1;
    [c0, c1, c2]
}

fn ef_add_limbs<AB: AirBuilder>(a: &[AB::Expr; 3], b: &[AB::Expr; 3]) -> [AB::Expr; 3] {
    [
        a[0].clone() + b[0].clone(),
        a[1].clone() + b[1].clone(),
        a[2].clone() + b[2].clone(),
    ]
}

fn ef_sub_limbs<AB: AirBuilder>(a: &[AB::Expr; 3], b: &[AB::Expr; 3]) -> [AB::Expr; 3] {
    [
        a[0].clone() - b[0].clone(),
        a[1].clone() - b[1].clone(),
        a[2].clone() - b[2].clone(),
    ]
}

fn ef_halve_limbs<AB: AirBuilder>(a: &[AB::Expr; 3]) -> [AB::Expr; 3]
where
    AB::F: Field + PrimeCharacteristicRing,
{
    // 2^{-1} = 2^{30} over Mersenne31.
    let inv2: AB::Expr = AB::F::from_u32(1u32 << 30).into();
    [
        a[0].clone() * inv2.clone(),
        a[1].clone() * inv2.clone(),
        a[2].clone() * inv2,
    ]
}

fn ef_scale_by_base<AB: AirBuilder>(a: &[AB::Expr; 3], s: AB::Expr) -> [AB::Expr; 3] {
    [
        a[0].clone() * s.clone(),
        a[1].clone() * s.clone(),
        a[2].clone() * s,
    ]
}

impl<AB: AirBuilder> Air<AB> for FriFoldAir
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

        // Layout: 0:index 1:log_h 2:t_inv 3..6:beta 6..9:v0 9..12:v1 12..15:out
        let t = pv[2].clone();
        let beta = [pv[3].clone(), pv[4].clone(), pv[5].clone()];
        let v0 = [pv[6].clone(), pv[7].clone(), pv[8].clone()];
        let v1 = [pv[9].clone(), pv[10].clone(), pv[11].clone()];
        let out = [pv[12].clone(), pv[13].clone(), pv[14].clone()];

        let sum = ef_add_limbs::<AB>(&v0, &v1);
        let diff = ef_sub_limbs::<AB>(&v0, &v1);
        let diff_t = ef_scale_by_base::<AB>(&diff, t);
        let beta_diff_t = ef_mul_limbs::<AB>(&beta, &diff_t);
        let sum_plus = ef_add_limbs::<AB>(&sum, &beta_diff_t);
        let expected = ef_halve_limbs::<AB>(&sum_plus);

        for i in 0..3 {
            builder.assert_zero(expected[i].clone() - out[i].clone());
        }
    }
}

fn build_public_values(
    index: u32,
    log_folded_height: u32,
    t_inv: Mersenne31,
    beta: Challenge,
    v0: Challenge,
    v1: Challenge,
    out: Challenge,
) -> Vec<Mersenne31> {
    let mut pv = Vec::with_capacity(FRI_FOLD_NUM_PUBLIC);
    pv.push(Mersenne31::from_u32(index));
    pv.push(Mersenne31::from_u32(log_folded_height));
    pv.push(t_inv);
    pv.extend_from_slice(&challenge_to_limbs(beta));
    pv.extend_from_slice(&challenge_to_limbs(v0));
    pv.extend_from_slice(&challenge_to_limbs(v1));
    pv.extend_from_slice(&challenge_to_limbs(out));
    pv
}

fn build_matrix() -> RowMajorMatrix<Mersenne31> {
    // Two rows of ok=1 (then padded).
    let values = vec![Mersenne31::ONE, Mersenne31::ONE];
    RowMajorMatrix::new(values, FRI_FOLD_WIDTH)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FriFoldStepProof {
    pub index: u32,
    pub log_folded_height: u32,
    pub t_inv: Mersenne31,
    pub beta_limbs: [Mersenne31; 3],
    pub v0_limbs: [Mersenne31; 3],
    pub v1_limbs: [Mersenne31; 3],
    pub out_limbs: [Mersenne31; 3],
    pub fold_stark: Vec<u8>,
}

pub fn generate_fri_fold_proof(
    index: usize,
    log_folded_height: usize,
    beta: Challenge,
    v0: Challenge,
    v1: Challenge,
) -> Result<FriFoldStepProof, String> {
    if log_folded_height == 0 || log_folded_height > 16 {
        return Err("log_folded_height out of range".into());
    }
    if index >= (1 << log_folded_height) {
        return Err("index out of range for log_folded_height".into());
    }
    let t_inv = fold_x_twiddle_inv(index, log_folded_height);
    let out = fold_x_row(index, log_folded_height, beta, v0, v1);
    let pv = build_public_values(
        index as u32,
        log_folded_height as u32,
        t_inv,
        beta,
        v0,
        v1,
        out,
    );
    let matrix = pad_air_matrix_for_uni_stark(build_matrix());
    p3_air::check_constraints(&FriFoldAir, &matrix, &pv);
    let config = devnet_circle_config();
    let proof = prove(&config, &FriFoldAir, matrix, &pv);
    let fold_stark =
        postcard::to_allocvec(&proof).map_err(|e| format!("postcard encode fri fold: {e}"))?;
    Ok(FriFoldStepProof {
        index: index as u32,
        log_folded_height: log_folded_height as u32,
        t_inv,
        beta_limbs: challenge_to_limbs(beta),
        v0_limbs: challenge_to_limbs(v0),
        v1_limbs: challenge_to_limbs(v1),
        out_limbs: challenge_to_limbs(out),
        fold_stark,
    })
}

pub fn verify_fri_fold_proof(proof: &FriFoldStepProof) -> bool {
    let beta = limbs_to_challenge(proof.beta_limbs);
    let v0 = limbs_to_challenge(proof.v0_limbs);
    let v1 = limbs_to_challenge(proof.v1_limbs);
    let out = limbs_to_challenge(proof.out_limbs);
    let expect_t = fold_x_twiddle_inv(proof.index as usize, proof.log_folded_height as usize);
    if proof.t_inv != expect_t {
        eprintln!("[FriFold] Failed: twiddle mismatch");
        return false;
    }
    let expect_out = fold_x_row(
        proof.index as usize,
        proof.log_folded_height as usize,
        beta,
        v0,
        v1,
    );
    if out != expect_out {
        eprintln!("[FriFold] Failed: native fold mismatch");
        return false;
    }
    let pv = build_public_values(
        proof.index,
        proof.log_folded_height,
        proof.t_inv,
        beta,
        v0,
        v1,
        out,
    );
    let stark: p3_uni_stark::Proof<WqcStarkConfig> = match postcard::from_bytes(&proof.fold_stark) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("[FriFold] postcard: {e}");
            return false;
        }
    };
    let config = devnet_circle_config();
    match verify(&config, &FriFoldAir, &stark, &pv) {
        Ok(()) => true,
        Err(e) => {
            eprintln!("[FriFold] STARK: {e:?}");
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_field::PrimeCharacteristicRing;
    use rand::{Rng, SeedableRng};

    #[test]
    fn fri_fold_stark_roundtrip() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(11);
        let log_h = 2usize;
        let index = 1usize;
        let beta = Challenge::new([
            Mersenne31::from_u32(rng.gen()),
            Mersenne31::from_u32(rng.gen()),
            Mersenne31::from_u32(rng.gen()),
        ]);
        let v0 = Challenge::new([
            Mersenne31::from_u32(rng.gen()),
            Mersenne31::from_u32(rng.gen()),
            Mersenne31::from_u32(rng.gen()),
        ]);
        let v1 = Challenge::new([
            Mersenne31::from_u32(rng.gen()),
            Mersenne31::from_u32(rng.gen()),
            Mersenne31::from_u32(rng.gen()),
        ]);
        let proof = generate_fri_fold_proof(index, log_h, beta, v0, v1).expect("prove");
        assert!(verify_fri_fold_proof(&proof));
    }
}

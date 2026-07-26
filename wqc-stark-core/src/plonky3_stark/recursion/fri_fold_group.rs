//! B5 FriFold group fold: many homogeneous fold steps → one outer uni-STARK.
//!
//! Replaces N per-step `FriFoldAir` proofs with a single group proof whose publics
//! pack every step's fold equation. Host still checks Y vs X twiddles separately.

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::dense::RowMajorMatrix;
use p3_mersenne_31::Mersenne31;
use p3_uni_stark::{prove, verify};

use crate::air::pad_air_matrix_for_uni_stark;
use crate::plonky3_stark::config::{devnet_circle_config, WqcStarkConfig};

use super::ef_limbs::{
    ef_add_limbs, ef_assert_eq, ef_halve_limbs, ef_mul_limbs, ef_scale_by_base, ef_sub_limbs,
};
use super::fri_fold_air::{
    verify_fri_fold_x_native, verify_fri_fold_y_native, FriFoldStepProof, FRI_FOLD_NUM_PUBLIC,
    FRI_FOLD_WIDTH,
};

/// Soft cap on steps packed into one group STARK (idle unitary ≈ 80–160).
pub const FRI_FOLD_GROUP_MAX_STEPS: usize = 256;

/// `0` = fold_y (first-layer), `1` = fold_x (commit-phase).
pub const FRI_FOLD_KIND_Y: u8 = 0;
pub const FRI_FOLD_KIND_X: u8 = 1;

/// One outer Plonky3 STARK covering `step_count` FriFold equations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FriFoldGroupProof {
    pub kind: u8,
    pub step_count: u32,
    /// Optional shared height for fold_x batches grouped by `log_folded_height`.
    /// `u32::MAX` means mixed / unspecified (fold_y groups).
    pub log_folded_height: u32,
    pub group_stark: Vec<u8>,
}

#[derive(Copy, Clone, Debug)]
pub struct FriFoldGroupAir {
    pub step_count: usize,
}

impl FriFoldGroupAir {
    pub fn num_public(step_count: usize) -> usize {
        1 + step_count * FRI_FOLD_NUM_PUBLIC
    }

    fn pv_stride() -> usize {
        FRI_FOLD_NUM_PUBLIC
    }
}

impl<F: Field> BaseAir<F> for FriFoldGroupAir {
    fn width(&self) -> usize {
        FRI_FOLD_WIDTH
    }

    fn max_constraint_degree(&self) -> Option<usize> {
        Some(2)
    }

    fn num_public_values(&self) -> usize {
        Self::num_public(self.step_count)
    }
}

impl<AB: AirBuilder> Air<AB> for FriFoldGroupAir
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

        builder.assert_zero(pv[0].clone() - AB::Expr::from_u32(self.step_count as u32));

        let stride = Self::pv_stride();
        for i in 0..self.step_count {
            let base = 1 + i * stride;
            // Layout per step: index | log_h | t_inv | beta[3] | v0[3] | v1[3] | out[3]
            let t = pv[base + 2].clone();
            let beta = [
                pv[base + 3].clone(),
                pv[base + 4].clone(),
                pv[base + 5].clone(),
            ];
            let v0 = [
                pv[base + 6].clone(),
                pv[base + 7].clone(),
                pv[base + 8].clone(),
            ];
            let v1 = [
                pv[base + 9].clone(),
                pv[base + 10].clone(),
                pv[base + 11].clone(),
            ];
            let out = [
                pv[base + 12].clone(),
                pv[base + 13].clone(),
                pv[base + 14].clone(),
            ];

            let sum = ef_add_limbs::<AB>(&v0, &v1);
            let diff = ef_sub_limbs::<AB>(&v0, &v1);
            let diff_t = ef_scale_by_base::<AB>(&diff, t);
            let beta_diff_t = ef_mul_limbs::<AB>(&beta, &diff_t);
            let sum_plus = ef_add_limbs::<AB>(&sum, &beta_diff_t);
            let expected = ef_halve_limbs::<AB>(&sum_plus);
            ef_assert_eq(builder, &expected, &out);
        }
    }
}

fn build_group_public_values(steps: &[FriFoldStepProof]) -> Vec<Mersenne31> {
    let mut pv = Vec::with_capacity(FriFoldGroupAir::num_public(steps.len()));
    pv.push(Mersenne31::from_u32(steps.len() as u32));
    for s in steps {
        pv.push(Mersenne31::from_u32(s.index));
        pv.push(Mersenne31::from_u32(s.log_folded_height));
        pv.push(s.t_inv);
        pv.extend_from_slice(&s.beta_limbs);
        pv.extend_from_slice(&s.v0_limbs);
        pv.extend_from_slice(&s.v1_limbs);
        pv.extend_from_slice(&s.out_limbs);
    }
    pv
}

fn build_group_matrix(step_count: usize) -> RowMajorMatrix<Mersenne31> {
    // At least two ok=1 rows before uni-STARK padding.
    let rows = step_count.max(2);
    let values = vec![Mersenne31::ONE; rows];
    RowMajorMatrix::new(values, FRI_FOLD_WIDTH)
}

fn native_check_steps(kind: u8, steps: &[FriFoldStepProof]) -> bool {
    match kind {
        FRI_FOLD_KIND_Y => steps.iter().all(verify_fri_fold_y_native),
        FRI_FOLD_KIND_X => steps.iter().all(verify_fri_fold_x_native),
        _ => false,
    }
}

/// Prove one FriFold group covering `steps` (must be non-empty, ≤ max, same kind).
pub fn generate_fri_fold_group_proof(
    kind: u8,
    steps: &[FriFoldStepProof],
    log_folded_height: Option<u32>,
) -> Result<FriFoldGroupProof, String> {
    if steps.is_empty() {
        return Err("FriFold group requires at least one step".into());
    }
    if steps.len() > FRI_FOLD_GROUP_MAX_STEPS {
        return Err(format!(
            "FriFold group too large: {} > {FRI_FOLD_GROUP_MAX_STEPS}",
            steps.len()
        ));
    }
    if kind != FRI_FOLD_KIND_Y && kind != FRI_FOLD_KIND_X {
        return Err(format!("invalid FriFold group kind {kind}"));
    }
    if !native_check_steps(kind, steps) {
        return Err("FriFold group native self-check failed".into());
    }
    if let Some(h) = log_folded_height {
        if steps.iter().any(|s| s.log_folded_height != h) {
            return Err("FriFold group log_folded_height mismatch".into());
        }
    }

    let air = FriFoldGroupAir {
        step_count: steps.len(),
    };
    let pv = build_group_public_values(steps);
    let matrix = pad_air_matrix_for_uni_stark(build_group_matrix(steps.len()));
    p3_air::check_constraints(&air, &matrix, &pv);
    let config = devnet_circle_config();
    let proof = prove(&config, &air, matrix, &pv);
    let group_stark = super::prove_workspace::encode_stark_and_drop(proof, "fri fold group")?;

    Ok(FriFoldGroupProof {
        kind,
        step_count: steps.len() as u32,
        log_folded_height: log_folded_height.unwrap_or(u32::MAX),
        group_stark,
    })
}

/// Verify group STARK + host twiddle/algebra for residual step limbs.
pub fn verify_fri_fold_group_proof(steps: &[FriFoldStepProof], proof: &FriFoldGroupProof) -> bool {
    if steps.len() as u32 != proof.step_count {
        eprintln!(
            "[FriFoldGroup] step_count mismatch: limbs {} vs proof {}",
            steps.len(),
            proof.step_count
        );
        return false;
    }
    if proof.kind != FRI_FOLD_KIND_Y && proof.kind != FRI_FOLD_KIND_X {
        eprintln!("[FriFoldGroup] invalid kind {}", proof.kind);
        return false;
    }
    if proof.log_folded_height != u32::MAX
        && steps
            .iter()
            .any(|s| s.log_folded_height != proof.log_folded_height)
    {
        eprintln!("[FriFoldGroup] log_folded_height mismatch");
        return false;
    }
    if !native_check_steps(proof.kind, steps) {
        return false;
    }

    let air = FriFoldGroupAir {
        step_count: steps.len(),
    };
    let pv = build_group_public_values(steps);
    let stark: p3_uni_stark::Proof<WqcStarkConfig> = match postcard::from_bytes(&proof.group_stark)
    {
        Ok(p) => p,
        Err(e) => {
            eprintln!("[FriFoldGroup] postcard: {e}");
            return false;
        }
    };
    let config = devnet_circle_config();
    match verify(&config, &air, &stark, &pv) {
        Ok(()) => true,
        Err(e) => {
            eprintln!("[FriFoldGroup] STARK: {e:?}");
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::plonky3_stark::config::Challenge;
    use crate::plonky3_stark::recursion::fri_fold_air::{
        fri_fold_step_limbs_x, fri_fold_step_limbs_y,
    };
    use p3_field::PrimeCharacteristicRing;
    use rand::{Rng, SeedableRng};

    fn rand_chal(rng: &mut rand::rngs::StdRng) -> Challenge {
        Challenge::new([
            Mersenne31::from_u32(rng.gen()),
            Mersenne31::from_u32(rng.gen()),
            Mersenne31::from_u32(rng.gen()),
        ])
    }

    #[test]
    fn fri_fold_group_y_roundtrip() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(21);
        let mut steps = Vec::new();
        for i in 0..3 {
            let log_h = 2usize;
            let index = i % (1 << log_h);
            steps.push(
                fri_fold_step_limbs_y(
                    index,
                    log_h,
                    rand_chal(&mut rng),
                    rand_chal(&mut rng),
                    rand_chal(&mut rng),
                )
                .expect("limbs"),
            );
        }
        let proof =
            generate_fri_fold_group_proof(FRI_FOLD_KIND_Y, &steps, None).expect("group prove");
        assert!(verify_fri_fold_group_proof(&steps, &proof));
        assert!(!verify_fri_fold_group_proof(
            &steps,
            &FriFoldGroupProof {
                kind: FRI_FOLD_KIND_X,
                ..proof.clone()
            }
        ));
    }

    #[test]
    fn fri_fold_group_x_roundtrip() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(22);
        let log_h = 3u32;
        let mut steps = Vec::new();
        for i in 0..4 {
            let index = i % (1 << log_h);
            steps.push(
                fri_fold_step_limbs_x(
                    index as usize,
                    log_h as usize,
                    rand_chal(&mut rng),
                    rand_chal(&mut rng),
                    rand_chal(&mut rng),
                )
                .expect("limbs"),
            );
        }
        let proof = generate_fri_fold_group_proof(FRI_FOLD_KIND_X, &steps, Some(log_h))
            .expect("group prove");
        assert_eq!(proof.log_folded_height, log_h);
        assert!(verify_fri_fold_group_proof(&steps, &proof));
    }
}

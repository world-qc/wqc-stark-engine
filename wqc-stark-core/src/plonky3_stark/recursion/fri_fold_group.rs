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
use crate::plonky3_stark::config::{
    devnet_circle_config, devnet_circle_config_with_queries, WqcStarkConfig, DEVNET_FRI_NUM_QUERIES,
};

use super::ef_limbs::{
    ef_add_limbs, ef_assert_eq, ef_halve_limbs, ef_mul_limbs, ef_scale_by_base, ef_sub_limbs,
};
use super::fri_fold_air::{
    fri_fold_x_native_ok, fri_fold_y_native_ok, verify_fri_fold_x_native, verify_fri_fold_y_native,
    FriFoldStepProof, FRI_FOLD_WIDTH,
};

/// Soft cap on steps packed into one group STARK (idle unitary ≈ 80–160).
pub const FRI_FOLD_GROUP_MAX_STEPS: usize = 256;

/// `0` = fold_y (first-layer), `1` = fold_x (commit-phase), `2` = mixed Y then X.
pub const FRI_FOLD_KIND_Y: u8 = 0;
pub const FRI_FOLD_KIND_X: u8 = 1;
pub const FRI_FOLD_KIND_YX: u8 = 2;

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
    /// Every step folds with the same FRI challenge: one `beta[3]` in the header.
    pub shared_beta: bool,
}

/// Per-step publics actually constrained by the fold equation:
/// `t_inv | [beta[3] unless shared] | v0[3] | v1[3] | out[3]`.
/// `index` / `log_folded_height` stay off the publics — the host binds those
/// positionally against the FRI transcript.
const FRI_FOLD_GROUP_STEP_PUBLIC: usize = 1 + 3 + 3 + 3;
const EF_LIMBS: usize = 3;

impl FriFoldGroupAir {
    pub fn num_public(step_count: usize, shared_beta: bool) -> usize {
        Self::header_len(shared_beta) + step_count * Self::pv_stride(shared_beta)
    }

    const fn header_len(shared_beta: bool) -> usize {
        if shared_beta {
            1 + EF_LIMBS
        } else {
            1
        }
    }

    const fn pv_stride(shared_beta: bool) -> usize {
        if shared_beta {
            FRI_FOLD_GROUP_STEP_PUBLIC
        } else {
            FRI_FOLD_GROUP_STEP_PUBLIC + EF_LIMBS
        }
    }
}

/// True when every step in the group shares one FRI fold challenge.
fn betas_are_shared(steps: &[FriFoldStepProof]) -> bool {
    steps.len() > 1 && steps.iter().all(|s| s.beta_limbs == steps[0].beta_limbs)
}

impl<F: Field> BaseAir<F> for FriFoldGroupAir {
    fn width(&self) -> usize {
        FRI_FOLD_WIDTH
    }

    fn max_constraint_degree(&self) -> Option<usize> {
        Some(2)
    }

    fn num_public_values(&self) -> usize {
        Self::num_public(self.step_count, self.shared_beta)
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

        let shared = self.shared_beta;
        let stride = Self::pv_stride(shared);
        for i in 0..self.step_count {
            let base = Self::header_len(shared) + i * stride;
            // Per step: t_inv | [beta[3] unless shared] | v0[3] | v1[3] | out[3]
            let t = pv[base].clone();
            let beta_base = if shared { 1 } else { base + 1 };
            let beta = [
                pv[beta_base].clone(),
                pv[beta_base + 1].clone(),
                pv[beta_base + 2].clone(),
            ];
            let vals_base = if shared {
                base + 1
            } else {
                base + 1 + EF_LIMBS
            };
            let v0 = [
                pv[vals_base].clone(),
                pv[vals_base + 1].clone(),
                pv[vals_base + 2].clone(),
            ];
            let v1 = [
                pv[vals_base + 3].clone(),
                pv[vals_base + 4].clone(),
                pv[vals_base + 5].clone(),
            ];
            let out = [
                pv[vals_base + 6].clone(),
                pv[vals_base + 7].clone(),
                pv[vals_base + 8].clone(),
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
    let shared = betas_are_shared(steps);
    let mut pv = Vec::with_capacity(FriFoldGroupAir::num_public(steps.len(), shared));
    pv.push(Mersenne31::from_u32(steps.len() as u32));
    if shared {
        pv.extend_from_slice(&steps[0].beta_limbs);
    }
    for s in steps {
        pv.push(s.t_inv);
        if !shared {
            pv.extend_from_slice(&s.beta_limbs);
        }
        pv.extend_from_slice(&s.v0_limbs);
        pv.extend_from_slice(&s.v1_limbs);
        pv.extend_from_slice(&s.out_limbs);
    }
    debug_assert_eq!(pv.len(), FriFoldGroupAir::num_public(steps.len(), shared));
    pv
}

fn build_group_matrix(step_count: usize) -> RowMajorMatrix<Mersenne31> {
    // At least two ok=1 rows before uni-STARK padding.
    let rows = step_count.max(2);
    let values = vec![Mersenne31::ONE; rows];
    RowMajorMatrix::new(values, FRI_FOLD_WIDTH)
}

/// Mixed group is `fold_y` steps followed by `fold_x` steps (same order as bind).
fn native_check_yx_split(steps: &[FriFoldStepProof]) -> bool {
    if steps.len() < 2 {
        return false;
    }
    let mut n_y = 0usize;
    while n_y < steps.len() && fri_fold_y_native_ok(&steps[n_y]) {
        n_y += 1;
    }
    n_y > 0 && n_y < steps.len() && steps[n_y..].iter().all(fri_fold_x_native_ok)
}

fn native_check_steps(kind: u8, steps: &[FriFoldStepProof]) -> bool {
    match kind {
        FRI_FOLD_KIND_Y => steps.iter().all(verify_fri_fold_y_native),
        FRI_FOLD_KIND_X => steps.iter().all(verify_fri_fold_x_native),
        FRI_FOLD_KIND_YX => native_check_yx_split(steps),
        _ => false,
    }
}

/// Prove one FriFold group covering `steps` (must be non-empty, ≤ max, same kind).
pub fn generate_fri_fold_group_proof(
    kind: u8,
    steps: &[FriFoldStepProof],
    log_folded_height: Option<u32>,
) -> Result<FriFoldGroupProof, String> {
    generate_fri_fold_group_proof_with_queries(
        kind,
        steps,
        log_folded_height,
        DEVNET_FRI_NUM_QUERIES,
    )
}

/// Like [`generate_fri_fold_group_proof`], with explicit nested FRI query count.
pub fn generate_fri_fold_group_proof_with_queries(
    kind: u8,
    steps: &[FriFoldStepProof],
    log_folded_height: Option<u32>,
    num_queries: usize,
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
    if num_queries == 0 || num_queries > DEVNET_FRI_NUM_QUERIES {
        return Err(format!(
            "nested FRI query count {num_queries} out of range 1..={DEVNET_FRI_NUM_QUERIES}"
        ));
    }
    if kind != FRI_FOLD_KIND_Y && kind != FRI_FOLD_KIND_X && kind != FRI_FOLD_KIND_YX {
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
        shared_beta: betas_are_shared(steps),
    };
    let pv = build_group_public_values(steps);
    let matrix = pad_air_matrix_for_uni_stark(build_group_matrix(steps.len()));
    p3_air::check_constraints(&air, &matrix, &pv);
    let config = if num_queries == DEVNET_FRI_NUM_QUERIES {
        devnet_circle_config()
    } else {
        devnet_circle_config_with_queries(num_queries)
    };
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
    if proof.kind != FRI_FOLD_KIND_Y
        && proof.kind != FRI_FOLD_KIND_X
        && proof.kind != FRI_FOLD_KIND_YX
    {
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
        shared_beta: betas_are_shared(steps),
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
    let config = match super::fri_fs_replay::circle_config_matching_proof(&stark) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("[FriFoldGroup] config: {e}");
            return false;
        }
    };
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

    #[test]
    fn fri_fold_group_x_mixed_height_roundtrip() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(23);
        let mut steps = Vec::new();
        for log_h in [2usize, 3, 4] {
            for i in 0..2 {
                let index = i % (1 << log_h);
                steps.push(
                    fri_fold_step_limbs_x(
                        index,
                        log_h,
                        rand_chal(&mut rng),
                        rand_chal(&mut rng),
                        rand_chal(&mut rng),
                    )
                    .expect("limbs"),
                );
            }
        }
        let proof =
            generate_fri_fold_group_proof(FRI_FOLD_KIND_X, &steps, None).expect("mixed prove");
        assert_eq!(proof.log_folded_height, u32::MAX);
        assert!(verify_fri_fold_group_proof(&steps, &proof));
    }

    #[test]
    fn fri_fold_group_yx_roundtrip() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(24);
        let mut steps = Vec::new();
        for i in 0..2 {
            let log_h = 2usize;
            steps.push(
                fri_fold_step_limbs_y(
                    i % (1 << log_h),
                    log_h,
                    rand_chal(&mut rng),
                    rand_chal(&mut rng),
                    rand_chal(&mut rng),
                )
                .expect("y"),
            );
        }
        for log_h in [2usize, 3] {
            steps.push(
                fri_fold_step_limbs_x(
                    0,
                    log_h,
                    rand_chal(&mut rng),
                    rand_chal(&mut rng),
                    rand_chal(&mut rng),
                )
                .expect("x"),
            );
        }
        let proof =
            generate_fri_fold_group_proof(FRI_FOLD_KIND_YX, &steps, None).expect("yx prove");
        assert_eq!(proof.kind, FRI_FOLD_KIND_YX);
        assert!(verify_fri_fold_group_proof(&steps, &proof));
        assert!(!verify_fri_fold_group_proof(
            &steps,
            &FriFoldGroupProof {
                kind: FRI_FOLD_KIND_Y,
                ..proof.clone()
            }
        ));
    }
}

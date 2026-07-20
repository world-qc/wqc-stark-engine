//! Bind in-circuit OOD step proofs to child uni-STARK openings.

use p3_air::{Air, BaseAir};
use p3_commit::{Pcs, PolynomialSpace};
use p3_field::{BasedVectorSpace, Field};
use p3_uni_stark::{
    get_log_num_quotient_chunks, recompose_quotient_from_chunks, AirLayout, Proof,
    StarkGenericConfig, SymbolicAirBuilder,
};

use crate::plonky3_stark::aggregation_air::{AggregationAir, AGG_WIDTH};
use crate::plonky3_stark::config::{devnet_circle_config, Challenge, Val, WqcStarkConfig};
use crate::plonky3_stark::distribution_air::DistributionAir;
use crate::plonky3_stark::quantum_air::QuantumExecutionAir;
use crate::plonky3_stark::shot_sampling_air::{ShotSamplingAir, SHOT_SAMPLING_AIR_WIDTH};
use crate::trace_spec::AIR_WIDTH;

use super::fri_fold_native::limbs_to_challenge;
use super::fri_fs_replay::replay_fri_challenges;
use super::ood_air::{OodAirKind, OodStepProof};
use super::ood_native::ood_kind_for_leaf;
use super::pcs_geom::LeafKind;

fn recompute_selectors(
    degree_bits: usize,
    zeta: Challenge,
) -> Result<(Challenge, Challenge, Challenge, Challenge), String> {
    let config = devnet_circle_config();
    let pcs = config.pcs();
    let degree = 1usize << degree_bits;
    let domain = <crate::plonky3_stark::config::Pcs as Pcs<
        Challenge,
        crate::plonky3_stark::config::Challenger,
    >>::natural_domain_for_degree(pcs, degree);
    if domain.vanishing_poly_at_point(zeta).is_zero() {
        return Err("ζ on trace domain".into());
    }
    let sels = domain.selectors_at_point(zeta);
    Ok((
        sels.inv_vanishing,
        sels.is_first_row,
        sels.is_last_row,
        sels.is_transition,
    ))
}

fn expected_trace_width(step: &OodStepProof) -> Result<usize, String> {
    match step.kind {
        OodAirKind::Aggregation => Ok(AGG_WIDTH),
        OodAirKind::Unitary => Ok(AIR_WIDTH),
        OodAirKind::Distribution => {
            let dim = 1usize << step.degree_bits;
            Ok(DistributionAir {
                dim,
                num_outcomes: step.num_outcomes as usize,
            }
            .width())
        }
        OodAirKind::ShotSampling => Ok(SHOT_SAMPLING_AIR_WIDTH),
    }
}

fn recompose_for_step(
    proof: &Proof<WqcStarkConfig>,
    step: &OodStepProof,
) -> Result<Challenge, String> {
    let zeta = limbs_to_challenge(step.zeta_limbs);
    match step.kind {
        OodAirKind::Aggregation => recompose_quotient_for_air(proof, &AggregationAir, zeta),
        OodAirKind::Unitary => recompose_quotient_for_air(proof, &QuantumExecutionAir, zeta),
        OodAirKind::Distribution => {
            let dim = 1usize << step.degree_bits;
            let air = DistributionAir {
                dim,
                num_outcomes: step.num_outcomes as usize,
            };
            recompose_quotient_for_air(proof, &air, zeta)
        }
        OodAirKind::ShotSampling => recompose_quotient_for_air(proof, &ShotSamplingAir, zeta),
    }
}

fn recompose_quotient_for_air<A>(
    proof: &Proof<WqcStarkConfig>,
    air: &A,
    zeta: Challenge,
) -> Result<Challenge, String>
where
    A: BaseAir<Val> + Air<SymbolicAirBuilder<Val>>,
{
    let width = air.width();
    let config = devnet_circle_config();
    let pcs = config.pcs();
    let degree = 1usize << proof.degree_bits;
    let init_trace_domain = <crate::plonky3_stark::config::Pcs as Pcs<
        Challenge,
        crate::plonky3_stark::config::Challenger,
    >>::natural_domain_for_degree(pcs, degree);
    let layout = AirLayout {
        preprocessed_width: 0,
        main_width: width,
        num_public_values: air.num_public_values(),
        num_periodic_columns: 0,
        ..Default::default()
    };
    let log_num_quotient_chunks = get_log_num_quotient_chunks::<Val, A>(air, layout, 0);
    let num_quotient_chunks = 1usize << log_num_quotient_chunks;
    if proof.opened_values.quotient_chunks.len() != num_quotient_chunks {
        return Err(format!(
            "quotient chunk count {} != {}",
            proof.opened_values.quotient_chunks.len(),
            num_quotient_chunks
        ));
    }
    if proof
        .opened_values
        .quotient_chunks
        .iter()
        .any(|c| c.len() != <Challenge as BasedVectorSpace<Val>>::DIMENSION)
    {
        return Err("quotient chunk width mismatch".into());
    }
    let quotient_domain_size = 1usize << (proof.degree_bits + log_num_quotient_chunks);
    let quotient_domain = init_trace_domain.create_disjoint_domain(quotient_domain_size);
    let quotient_chunks_domains = quotient_domain.split_domains(num_quotient_chunks);
    Ok(recompose_quotient_from_chunks::<WqcStarkConfig>(
        &quotient_chunks_domains,
        &proof.opened_values.quotient_chunks,
        zeta,
    ))
}

/// Binds an OOD step to a child proof's FS challenges and OOD openings.
pub fn bind_ood_to_proof(proof: &Proof<WqcStarkConfig>, step: &OodStepProof) -> Result<(), String> {
    let expected_width = expected_trace_width(step)?;
    if step.width as usize != expected_width {
        return Err(format!(
            "OOD width {} != air width {}",
            step.width, expected_width
        ));
    }
    if proof.degree_bits as u32 != step.degree_bits {
        return Err("degree_bits mismatch".into());
    }

    let chal = replay_fri_challenges(proof, expected_width)?;
    let zeta = limbs_to_challenge(step.zeta_limbs);
    let alpha = limbs_to_challenge(step.alpha_limbs);
    if chal.zeta != zeta || chal.constraint_alpha != alpha {
        return Err("ζ/α mismatch vs FS replay".into());
    }

    let (inv_van, is_first, is_last, is_trans) = recompute_selectors(proof.degree_bits, zeta)?;
    if limbs_to_challenge(step.inv_vanishing_limbs) != inv_van
        || limbs_to_challenge(step.is_first_row_limbs) != is_first
        || limbs_to_challenge(step.is_last_row_limbs) != is_last
        || limbs_to_challenge(step.is_transition_limbs) != is_trans
    {
        return Err("selector mismatch vs domain".into());
    }

    let trace_next = proof
        .opened_values
        .trace_next
        .as_ref()
        .ok_or_else(|| "missing trace_next".to_string())?;
    if proof.opened_values.trace_local.len() != expected_width
        || trace_next.len() != expected_width
        || step.trace_local_limbs.len() != expected_width
        || step.trace_next_limbs.len() != expected_width
    {
        return Err("trace width mismatch".into());
    }
    for (i, (local, next)) in proof
        .opened_values
        .trace_local
        .iter()
        .zip(trace_next.iter())
        .enumerate()
    {
        if limbs_to_challenge(step.trace_local_limbs[i]) != *local
            || limbs_to_challenge(step.trace_next_limbs[i]) != *next
        {
            return Err(format!("trace opening mismatch at col {i}"));
        }
    }

    let quotient = recompose_for_step(proof, step)?;
    if limbs_to_challenge(step.quotient_limbs) != quotient {
        return Err("quotient mismatch".into());
    }
    Ok(())
}

pub fn bind_leaf_ood_to_proof(
    proof: &Proof<WqcStarkConfig>,
    step: &OodStepProof,
    leaf_kind: LeafKind,
) -> Result<(), String> {
    if step.kind != ood_kind_for_leaf(leaf_kind) {
        return Err("OOD kind mismatch vs leaf kind".into());
    }
    bind_ood_to_proof(proof, step)
}

pub fn verify_ood_step_bound(
    proof: &Proof<WqcStarkConfig>,
    step: &OodStepProof,
) -> Result<(), String> {
    bind_ood_to_proof(proof, step)?;
    if !super::ood_air::verify_ood_proof(step) {
        return Err("in-circuit OOD STARK failed".into());
    }
    Ok(())
}

pub fn verify_agg_ood_step(
    proof: &Proof<WqcStarkConfig>,
    step: &OodStepProof,
) -> Result<(), String> {
    if step.kind != OodAirKind::Aggregation {
        return Err("expected Aggregation OOD step".into());
    }
    verify_ood_step_bound(proof, step)
}

pub fn verify_leaf_ood_step(
    proof: &Proof<WqcStarkConfig>,
    step: &OodStepProof,
    leaf_kind: LeafKind,
) -> Result<(), String> {
    bind_leaf_ood_to_proof(proof, step, leaf_kind)?;
    if !super::ood_air::verify_ood_proof(step) {
        return Err("in-circuit OOD STARK failed".into());
    }
    Ok(())
}

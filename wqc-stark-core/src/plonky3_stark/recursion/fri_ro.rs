//! Reconstruct AggregationAir Circle PCS reduced openings (R3-M3b2).
//!
//! Host-side mirror of `CirclePcs::verify`'s `open_input`: DEEP quotient → λ
//! correction → first-layer `fold_y`. Output is the FRI reduced-opening list
//! `(log_height, value)` in descending height order.
//!
//! Uses local circle-point helpers because `p3_circle::Point` is not re-exported.

use std::collections::BTreeMap;

use p3_commit::{BatchOpening, Mmcs, Pcs, PolynomialSpace};
use p3_field::PrimeCharacteristicRing;
use p3_uni_stark::{Proof, StarkGenericConfig};
use serde::Deserialize;

use crate::plonky3_stark::aggregation_air::AGG_WIDTH;
use crate::plonky3_stark::config::{
    devnet_circle_config, Challenge, ChallengeMmcs, Val, ValMmcs, WqcStarkConfig,
};

use super::deep_ro_native::deep_quotient_reduce_row;
use super::fri_fold_native::{cfft_permute_index, fold_y_row, point_v_n, standard_nth_point};
use super::fri_fs_replay::{AggFriChallenges, CirclePcsProofView};

/// First-layer fold_y witness for one LDE height.
#[derive(Debug, Clone)]
pub struct FoldYWitness {
    pub index: usize,
    pub log_folded_height: usize,
    pub beta: Challenge,
    pub v0: Challenge,
    pub v1: Challenge,
}

#[derive(Deserialize)]
#[serde(bound = "")]
pub(crate) struct CircleInputProofView {
    pub(crate) input_openings: Vec<BatchOpening<Val, ValMmcs>>,
    pub(crate) first_layer_siblings: Vec<Challenge>,
    pub(crate) first_layer_proof: <ChallengeMmcs as Mmcs<Challenge>>::Proof,
}

pub(crate) fn decode_input_proof(
    fri_qp_input: &p3_circle::CircleInputProof<Val, Challenge, ValMmcs, ChallengeMmcs>,
) -> Result<CircleInputProofView, String> {
    let bytes = postcard::to_allocvec(fri_qp_input)
        .map_err(|e| format!("postcard encode input_proof: {e}"))?;
    postcard::from_bytes(&bytes).map_err(|e| format!("postcard decode input_proof: {e}"))
}

/// FRI reduced openings after first-layer fold_y: `(log_height, value)`.
pub type ReducedOpenings = Vec<(usize, Challenge)>;

/// Reconstruct FRI reduced openings + first-layer fold_y witnesses for one query.
pub fn reconstruct_agg_query_ro(
    proof: &Proof<WqcStarkConfig>,
    chal: &AggFriChallenges,
    pcs_view: &CirclePcsProofView,
    query: usize,
) -> Result<(ReducedOpenings, Vec<FoldYWitness>), String> {
    let query_index = *chal
        .query_indices
        .get(query)
        .ok_or_else(|| format!("missing query index {query}"))?;
    let qp = pcs_view
        .fri_proof
        .query_proofs
        .get(query)
        .ok_or_else(|| format!("missing FRI query {query}"))?;
    let input = decode_input_proof(&qp.input_proof)?;

    if input.input_openings.len() != 2 {
        return Err(format!(
            "expected 2 input opening batches, got {}",
            input.input_openings.len()
        ));
    }
    if input.first_layer_siblings.len() != pcs_view.lambdas.len() {
        return Err("first_layer_siblings / lambdas length mismatch".into());
    }
    if proof.opened_values.quotient_chunks.len() != 1 {
        return Err(format!(
            "unexpected quotient chunk count {}",
            proof.opened_values.quotient_chunks.len()
        ));
    }

    let config = devnet_circle_config();
    let pcs = config.pcs();
    let log_blowup = chal.log_blowup;
    let degree = 1usize << proof.degree_bits;
    let init_trace_domain = <crate::plonky3_stark::config::Pcs as Pcs<
        Challenge,
        crate::plonky3_stark::config::Challenger,
    >>::natural_domain_for_degree(pcs, degree);
    let zeta = chal.zeta;
    let zeta_next = init_trace_domain
        .next_point(zeta)
        .ok_or_else(|| "trace domain next_point unavailable".to_string())?;
    let alpha = chal.batch_alpha;
    let bivariate_beta = chal.bivariate_beta;

    let log_global_max_height = pcs_view.fri_proof.commit_phase_commits.len() + log_blowup + 1;

    let log2 = |mut n: usize| {
        let mut log = 0usize;
        while n > 1 {
            n >>= 1;
            log += 1;
        }
        log
    };
    let trace_log_height = log2(init_trace_domain.size()) + log_blowup;
    let quotient_domain = init_trace_domain.create_disjoint_domain(degree);
    let quot_log_height = log2(quotient_domain.size()) + log_blowup;

    let mut reduced_openings: BTreeMap<usize, Challenge> = BTreeMap::new();

    // Batch 0: trace openings at zeta and zeta_next.
    {
        let opened = input.input_openings[0]
            .opened_values
            .first()
            .ok_or_else(|| "empty trace input opening".to_string())?;
        if opened.len() != AGG_WIDTH {
            return Err(format!("trace opening width {}", opened.len()));
        }
        let trace_next = proof
            .opened_values
            .trace_next
            .as_ref()
            .ok_or_else(|| "missing trace_next".to_string())?;
        let log_height = trace_log_height;
        let bits_reduced = log_global_max_height - log_height;
        let orig_idx = cfft_permute_index(query_index >> bits_reduced, log_height);
        let p = standard_nth_point(log_height, orig_idx);
        let alpha_pow_width_2 = alpha.exp_u64(opened.len() as u64).square();
        let mut alpha_offset = Challenge::ONE;
        let mut ro = Challenge::ZERO;
        ro += alpha_offset
            * deep_quotient_reduce_row(
                alpha,
                p.x,
                p.y,
                zeta,
                opened,
                &proof.opened_values.trace_local,
            );
        alpha_offset *= alpha_pow_width_2;
        ro +=
            alpha_offset * deep_quotient_reduce_row(alpha, p.x, p.y, zeta_next, opened, trace_next);
        reduced_openings.insert(log_height, ro);
    }

    // Batch 1: quotient chunk at zeta.
    {
        let opened = input.input_openings[1]
            .opened_values
            .first()
            .ok_or_else(|| "empty quotient input opening".to_string())?;
        let ps_at_zeta = &proof.opened_values.quotient_chunks[0];
        if opened.len() != ps_at_zeta.len() {
            return Err("quotient opening / OOD width mismatch".into());
        }
        let log_height = quot_log_height;
        let bits_reduced = log_global_max_height - log_height;
        let orig_idx = cfft_permute_index(query_index >> bits_reduced, log_height);
        let p = standard_nth_point(log_height, orig_idx);
        let ro = deep_quotient_reduce_row(alpha, p.x, p.y, zeta, opened, ps_at_zeta);
        reduced_openings.insert(log_height, ro);
    }

    if reduced_openings.len() != pcs_view.lambdas.len() {
        return Err(format!(
            "RO height count {} != lambdas {}",
            reduced_openings.len(),
            pcs_view.lambdas.len()
        ));
    }

    let mut fri_input = Vec::new();
    let mut fold_ys = Vec::new();
    for (((log_height, ro), &fl_sib), &lambda) in reduced_openings
        .into_iter()
        .zip(input.first_layer_siblings.iter())
        .zip(pcs_view.lambdas.iter())
    {
        let orig_size = log_height - log_blowup;
        let bits_reduced = log_global_max_height - log_height;
        let orig_idx = cfft_permute_index(query_index >> bits_reduced, log_height);
        let p = standard_nth_point(log_height, orig_idx);
        let lambda_corrected = ro - lambda * point_v_n(p.x, orig_size);
        let mut fl_values = [lambda_corrected, lambda_corrected];
        fl_values[((query_index >> bits_reduced) & 1) ^ 1] = fl_sib;
        let fold_index = query_index >> (bits_reduced + 1);
        let log_folded = log_height - 1;
        let out = fold_y_row(
            fold_index,
            log_folded,
            bivariate_beta,
            fl_values[0],
            fl_values[1],
        );
        fold_ys.push(FoldYWitness {
            index: fold_index,
            log_folded_height: log_folded,
            beta: bivariate_beta,
            v0: fl_values[0],
            v1: fl_values[1],
        });
        fri_input.push((log_folded, out));
    }
    fri_input.reverse();
    Ok((fri_input, fold_ys))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::aggregation::CHILD_HASH_LEN;
    use crate::plonky3_stark::aggregation::AggregationContext;
    use crate::plonky3_stark::generate_aggregation_proof;
    use crate::plonky3_stark::recursion::fri_fs_replay::{
        decode_pcs_view, replay_agg_fri_challenges,
    };
    use crate::plonky3_stark::transcript_v4::decode_agg_proof_owned;

    #[test]
    fn reconstruct_ro_query0_reaches_final_poly() {
        let ctx = AggregationContext {
            parent_task_id: "parent",
            compose_label: "L1:0",
            manifest_root_hash: "",
            left_child_hash: [4u8; CHILD_HASH_LEN],
            right_child_hash: [6u8; CHILD_HASH_LEN],
        };
        let transcript = generate_aggregation_proof(&ctx).expect("prove");
        let plonky3 = decode_agg_proof_owned(&transcript, &ctx).expect("decode");
        let proof: Proof<WqcStarkConfig> = postcard::from_bytes(&plonky3).expect("postcard");
        let chal = replay_agg_fri_challenges(&proof).expect("fs");
        let view = decode_pcs_view(&proof).expect("pcs");
        let (ros, fold_ys) = reconstruct_agg_query_ro(&proof, &chal, &view, 0).expect("ro");
        assert_eq!(ros.len(), 2);
        assert_eq!(fold_ys.len(), 2);
        assert_eq!(ros[0].0, 3);
        assert_eq!(ros[1].0, 2);
    }
}

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

/// Reconstruct FRI reduced openings + first-layer fold_y for one query (any trace width).
pub fn reconstruct_query_ro(
    proof: &Proof<WqcStarkConfig>,
    chal: &AggFriChallenges,
    pcs_view: &CirclePcsProofView,
    query: usize,
    trace_width: usize,
) -> Result<(ReducedOpenings, Vec<FoldYWitness>), String> {
    if trace_width == 0 {
        return Err("trace_width must be > 0".into());
    }
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
    let num_quot_chunks = proof.opened_values.quotient_chunks.len();
    if num_quot_chunks == 0 || !num_quot_chunks.is_power_of_two() {
        return Err(format!("invalid quotient chunk count {num_quot_chunks}"));
    }
    if input.input_openings[1].opened_values.len() != num_quot_chunks {
        return Err(format!(
            "quot opening matrices {} != chunks {num_quot_chunks}",
            input.input_openings[1].opened_values.len()
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
    let log_num_quot_chunks = log2(num_quot_chunks);
    let trace_log_height = log2(init_trace_domain.size()) + log_blowup;
    // Matches uni-stark: disjoint domain of size 2^(degree_bits + log_chunks), then split.
    let quotient_parent = init_trace_domain
        .create_disjoint_domain(1usize << (proof.degree_bits + log_num_quot_chunks));
    let quot_chunk_domains = quotient_parent.split_domains(num_quot_chunks);

    // log_height -> (alpha_offset, ro) — mirrors CirclePcs::verify open_input.
    let mut reduced_openings: BTreeMap<usize, (Challenge, Challenge)> = BTreeMap::new();

    let mut accumulate = |log_height: usize, width: usize, deep: Challenge| {
        let e = reduced_openings
            .entry(log_height)
            .or_insert((Challenge::ONE, Challenge::ZERO));
        e.1 += e.0 * deep;
        e.0 *= alpha.exp_u64(width as u64).square();
    };

    // Batch 0: trace openings at zeta and zeta_next.
    {
        let opened = input.input_openings[0]
            .opened_values
            .first()
            .ok_or_else(|| "empty trace input opening".to_string())?;
        if opened.len() != trace_width {
            return Err(format!(
                "trace opening width {}, want {trace_width}",
                opened.len()
            ));
        }
        let trace_next = proof
            .opened_values
            .trace_next
            .as_ref()
            .ok_or_else(|| "missing trace_next".to_string())?;
        if proof.opened_values.trace_local.len() != trace_width || trace_next.len() != trace_width {
            return Err(format!(
                "trace OOD width mismatch: local={}, next={}, want {trace_width}",
                proof.opened_values.trace_local.len(),
                trace_next.len()
            ));
        }
        let log_height = trace_log_height;
        let bits_reduced = log_global_max_height - log_height;
        let orig_idx = cfft_permute_index(query_index >> bits_reduced, log_height);
        let p = standard_nth_point(log_height, orig_idx);
        accumulate(
            log_height,
            opened.len(),
            deep_quotient_reduce_row(
                alpha,
                p.x,
                p.y,
                zeta,
                opened,
                &proof.opened_values.trace_local,
            ),
        );
        accumulate(
            log_height,
            opened.len(),
            deep_quotient_reduce_row(alpha, p.x, p.y, zeta_next, opened, trace_next),
        );
    }

    // Batch 1: quotient chunks at zeta (possibly many matrices / heights).
    {
        let openings = &input.input_openings[1].opened_values;
        for (i, opened) in openings.iter().enumerate() {
            let ps_at_zeta = &proof.opened_values.quotient_chunks[i];
            if opened.len() != ps_at_zeta.len() {
                return Err(format!("quot chunk {i}: opening / OOD width mismatch"));
            }
            let log_height = log2(quot_chunk_domains[i].size()) + log_blowup;
            let bits_reduced = log_global_max_height - log_height;
            let orig_idx = cfft_permute_index(query_index >> bits_reduced, log_height);
            let p = standard_nth_point(log_height, orig_idx);
            accumulate(
                log_height,
                opened.len(),
                deep_quotient_reduce_row(alpha, p.x, p.y, zeta, opened, ps_at_zeta),
            );
        }
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
    for (((log_height, (_alpha_off, ro)), &fl_sib), &lambda) in reduced_openings
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

/// Reconstruct FRI reduced openings for AggregationAir (width [`AGG_WIDTH`]).
pub fn reconstruct_agg_query_ro(
    proof: &Proof<WqcStarkConfig>,
    chal: &AggFriChallenges,
    pcs_view: &CirclePcsProofView,
    query: usize,
) -> Result<(ReducedOpenings, Vec<FoldYWitness>), String> {
    reconstruct_query_ro(proof, chal, pcs_view, query, AGG_WIDTH)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::plonky3_stark::recursion::fri_fs_replay::{
        decode_pcs_view, replay_agg_fri_challenges,
    };

    #[test]
    fn reconstruct_ro_query0_reaches_final_poly() {
        use crate::aggregation::CHILD_HASH_LEN;
        use crate::plonky3_stark::aggregation::AggregationContext;
        use crate::plonky3_stark::generate_aggregation_proof;
        use crate::plonky3_stark::transcript_v4::decode_agg_proof_owned;

        let ctx = AggregationContext {
            parent_task_id: "parent",
            compose_label: "L1:0",
            manifest_root_hash: "",
            left_child_hash: [4u8; CHILD_HASH_LEN],
            right_child_hash: [6u8; CHILD_HASH_LEN],
            security_level: "",
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

    #[test]
    fn born_same_height_ro_matches_expected_fold_input() {
        use crate::distribution::DistributionSegment;
        use crate::plonky3_stark::generate_born_stark_proof;
        use crate::plonky3_stark::recursion::fri_fold_native::{
            solve_v0_for_fold, solve_v1_for_fold,
        };
        use crate::plonky3_stark::transcript_born::decode_born_stark_owned;
        use crate::plonky3_stark::BornStarkContext;

        let inv_sqrt2 = 1.0f64 / 2.0f64.sqrt();
        let sv = vec![(inv_sqrt2, 0.0), (0.0, 0.0), (0.0, 0.0), (inv_sqrt2, 0.0)];
        let probs = vec![("00".into(), 0.5), ("11".into(), 0.5)];
        let binding = crate::distribution::BornBinding::from_specs(2, 2, &[(0, 0), (1, 1)], sv)
            .expect("bind");
        let segment = DistributionSegment {
            sample_seed: 42,
            shots: 128,
            measurement_spec_hash: "spec".into(),
            probability_digest: crate::distribution::calculate_probability_digest(&probs),
            probabilities: probs,
            born_binding: Some(binding),
        };
        let link = segment
            .born_binding
            .as_ref()
            .unwrap()
            .terminal_statevector_digest
            .clone();
        let born_ctx = BornStarkContext {
            sub_task_id: "sub-born-ro",
            probability_digest: &segment.probability_digest,
            terminal_statevector_digest: &link,
            security_level: "",
        };
        let born_inner = generate_born_stark_proof(&born_ctx, &segment).expect("born prove");
        let plonky3 = decode_born_stark_owned(&born_inner, &born_ctx).expect("decode");
        let proof: Proof<WqcStarkConfig> = postcard::from_bytes(&plonky3).expect("postcard");
        let trace_width = proof.opened_values.trace_local.len();
        let chal =
            super::super::fri_fs_replay::replay_fri_challenges(&proof, trace_width).expect("fs");
        let view = decode_pcs_view(&proof).expect("pcs");

        let mut mismatches = 0usize;
        for q in 0..chal.query_indices.len() {
            let query_index = chal.query_indices[q];
            let (ros, _) = reconstruct_query_ro(&proof, &chal, &view, q, trace_width).expect("ro");
            let qp = &view.fri_proof.query_proofs[q];
            let fold_x_sibling = qp.commit_phase_openings[0].sibling_values[0];
            let domain_index = query_index >> chal.extra_query_index_bits;
            let fold_x_out = if domain_index.is_multiple_of(2) {
                solve_v0_for_fold(
                    domain_index >> 1,
                    1,
                    chal.betas[0],
                    fold_x_sibling,
                    view.fri_proof.final_poly,
                )
            } else {
                solve_v1_for_fold(
                    domain_index >> 1,
                    1,
                    chal.betas[0],
                    fold_x_sibling,
                    view.fri_proof.final_poly,
                )
            };

            if ros[0].1 != fold_x_out {
                mismatches += 1;
            }
        }
        assert_eq!(mismatches, 0, "same-height RO mismatch count");
    }
}

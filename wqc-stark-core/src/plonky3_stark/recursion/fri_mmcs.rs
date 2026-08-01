//! Host FRI Mmcs checks for AggregationAir Circle PCS (R3-M3b4).
//!
//! Authenticates query openings to commitments (ValMmcs input batches,
//! ChallengeMmcs first-layer + commit-phase) without re-running Plonky3 FRI
//! fold algebra (covered by FriFold STARKs + RO bind).

use p3_commit::{BatchOpeningRef, Mmcs, Pcs, PolynomialSpace};
use p3_field::{BasedVectorSpace, PrimeCharacteristicRing};
use p3_matrix::Dimensions;
use p3_uni_stark::{Proof, StarkGenericConfig};

use crate::plonky3_stark::aggregation_air::AGG_WIDTH;
use crate::plonky3_stark::config::{
    devnet_circle_config, Challenge, ChallengeMmcs, Val, ValMmcs, WqcStarkConfig,
};

use super::fri_fold_bind::AGG_FRI_MAX_ROUNDS;
use super::fri_fold_native::fold_x_row;
use super::fri_fs_replay::{decode_pcs_view, replay_agg_fri_challenges};
use super::fri_ro::{decode_input_proof, reconstruct_agg_query_ro};

fn log2_strict(n: usize) -> Result<usize, String> {
    if n == 0 || !n.is_power_of_two() {
        return Err(format!("expected power-of-two height, got {n}"));
    }
    Ok(n.trailing_zeros() as usize)
}

/// Verifies AggregationAir FRI query openings against PCS / FRI commitments.
pub fn verify_agg_fri_openings(proof: &Proof<WqcStarkConfig>) -> Result<(), String> {
    let chal = replay_agg_fri_challenges(proof)?;
    let view = decode_pcs_view(proof)?;
    let fri = &view.fri_proof;
    let config = devnet_circle_config();
    let pcs = config.pcs();
    let fri_mmcs = &pcs.fri_params.mmcs;

    let degree = 1usize << proof.degree_bits;
    let init_trace_domain = <crate::plonky3_stark::config::Pcs as Pcs<
        Challenge,
        crate::plonky3_stark::config::Challenger,
    >>::natural_domain_for_degree(pcs, degree);
    // AggregationAir has a single quotient chunk (log_num_quotient_chunks = 0).
    let quotient_domain = init_trace_domain.create_disjoint_domain(degree);

    let log_blowup = chal.log_blowup;
    let log_global_max_height = fri.commit_phase_commits.len() + log_blowup + 1;
    let trace_height = init_trace_domain.size() << log_blowup;
    let quot_height = quotient_domain.size() << log_blowup;
    let trace_log_height = log2_strict(trace_height)?;
    let quot_log_height = log2_strict(quot_height)?;

    if fri.query_proofs.len() != chal.query_indices.len() {
        return Err("FRI query / FS index count mismatch".into());
    }

    for (q, (&query_index, qp)) in chal
        .query_indices
        .iter()
        .zip(fri.query_proofs.iter())
        .enumerate()
    {
        let input = decode_input_proof(&qp.input_proof)?;
        if input.input_openings.len() != 2 {
            return Err(format!(
                "query {q}: expected 2 input openings, got {}",
                input.input_openings.len()
            ));
        }

        // --- ValMmcs: trace batch ---
        {
            let opening = &input.input_openings[0];
            let dims = [Dimensions {
                width: AGG_WIDTH,
                height: trace_height,
            }];
            let idx = query_index >> (log_global_max_height - trace_log_height);
            pcs.mmcs
                .verify_batch(
                    &proof.commitments.trace,
                    &dims,
                    idx,
                    BatchOpeningRef::new(&opening.opened_values, &opening.opening_proof),
                )
                .map_err(|e| format!("query {q}: trace ValMmcs: {e:?}"))?;
        }

        // --- ValMmcs: quotient batch ---
        {
            let opening = &input.input_openings[1];
            let dims = [Dimensions {
                width: <Challenge as BasedVectorSpace<Val>>::DIMENSION,
                height: quot_height,
            }];
            let idx = query_index >> (log_global_max_height - quot_log_height);
            pcs.mmcs
                .verify_batch(
                    &proof.commitments.quotient_chunks,
                    &dims,
                    idx,
                    BatchOpeningRef::new(&opening.opened_values, &opening.opening_proof),
                )
                .map_err(|e| format!("query {q}: quotient ValMmcs: {e:?}"))?;
        }

        let (reduced, fold_ys) = reconstruct_agg_query_ro(proof, &chal, &view, q)?;

        // --- ChallengeMmcs: first layer ---
        {
            if fold_ys.len() != input.first_layer_siblings.len() {
                return Err(format!("query {q}: first-layer sibling count mismatch"));
            }
            let fl_dims: Vec<Dimensions> = fold_ys
                .iter()
                .map(|w| Dimensions {
                    width: 2,
                    height: 1 << w.log_folded_height,
                })
                .collect();
            let fl_leaves: Vec<Vec<Challenge>> = fold_ys.iter().map(|w| vec![w.v0, w.v1]).collect();
            fri_mmcs
                .verify_batch(
                    &view.first_layer_commitment,
                    &fl_dims,
                    query_index >> 1,
                    BatchOpeningRef::new(&fl_leaves, &input.first_layer_proof),
                )
                .map_err(|e| format!("query {q}: first-layer ChallengeMmcs: {e:?}"))?;
        }

        // --- ChallengeMmcs: commit-phase rounds ---
        verify_commit_phase_mmcs(
            qp,
            &chal.betas,
            &fri.commit_phase_commits,
            fri_mmcs,
            query_index,
            chal.extra_query_index_bits,
            chal.log_blowup,
            fri.final_poly,
            &reduced,
            q,
        )?;
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn verify_commit_phase_mmcs(
    qp: &p3_circle::CircleQueryProof<
        Challenge,
        ChallengeMmcs,
        p3_circle::CircleInputProof<Val, Challenge, ValMmcs, ChallengeMmcs>,
    >,
    betas: &[Challenge],
    commits: &[<ChallengeMmcs as Mmcs<Challenge>>::Commitment],
    fri_mmcs: &ChallengeMmcs,
    query_index: usize,
    extra_bits: usize,
    log_blowup: usize,
    final_poly: Challenge,
    reduced: &[(usize, Challenge)],
    query: usize,
) -> Result<(), String> {
    let openings = &qp.commit_phase_openings;
    if openings.len() != betas.len() || openings.len() != commits.len() {
        return Err(format!(
            "query {query}: commit-phase openings/betas/commits length mismatch"
        ));
    }
    if openings.len() > AGG_FRI_MAX_ROUNDS {
        return Err(format!(
            "query {query}: too many FRI rounds: {}",
            openings.len()
        ));
    }
    if openings.iter().any(|o| o.log_arity != 1) {
        return Err(format!(
            "query {query}: only arity-2 (log_arity=1) supported"
        ));
    }

    let mut index = query_index >> extra_bits;
    let mut log_current = openings.len() + log_blowup;
    let mut folded_eval = Challenge::ZERO;
    let mut ro_iter = reduced.iter().peekable();

    for (round, opening) in openings.iter().enumerate() {
        if let Some(&&(lh, ro)) = ro_iter.peek() {
            if lh == log_current {
                folded_eval += ro;
                ro_iter.next();
            }
        }
        if opening.sibling_values.len() != 1 {
            return Err(format!(
                "query {query} round {round}: expected 1 sibling, got {}",
                opening.sibling_values.len()
            ));
        }
        let sibling = opening.sibling_values[0];
        let index_in_group = index % 2;
        let mut evals = vec![Challenge::ZERO; 2];
        evals[index_in_group] = folded_eval;
        evals[index_in_group ^ 1] = sibling;

        let log_folded = log_current - 1;
        index >>= 1;
        let dims = [Dimensions {
            width: 2,
            height: 1 << log_folded,
        }];
        fri_mmcs
            .verify_batch(
                &commits[round],
                &dims,
                index,
                BatchOpeningRef::new(&[evals.clone()], &opening.opening_proof),
            )
            .map_err(|e| {
                format!("query {query} round {round}: commit-phase ChallengeMmcs: {e:?}")
            })?;

        folded_eval = fold_x_row(index, log_folded, betas[round], evals[0], evals[1]);
        log_current = log_folded;
    }

    if log_current != log_blowup {
        return Err(format!(
            "query {query}: final fold height {log_current} != log_blowup {log_blowup}"
        ));
    }
    if folded_eval != final_poly {
        return Err(format!(
            "query {query}: commit-phase fold chain does not match final_poly"
        ));
    }
    if ro_iter.next().is_some() {
        return Err(format!("query {query}: unused reduced openings remain"));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::aggregation::CHILD_HASH_LEN;
    use crate::plonky3_stark::aggregation::AggregationContext;
    use crate::plonky3_stark::generate_aggregation_proof;
    use crate::plonky3_stark::transcript_v4::decode_agg_proof_owned;

    #[test]
    fn honest_aggregation_fri_openings_pass() {
        let ctx = AggregationContext {
            parent_task_id: "parent",
            compose_label: "L1:0",
            manifest_root_hash: "",
            left_child_hash: [17u8; CHILD_HASH_LEN],
            right_child_hash: [19u8; CHILD_HASH_LEN],
            security_level: "",
        };
        let transcript = generate_aggregation_proof(&ctx).expect("prove");
        let plonky3 = decode_agg_proof_owned(&transcript, &ctx).expect("decode");
        let proof: Proof<WqcStarkConfig> = postcard::from_bytes(&plonky3).expect("postcard");
        verify_agg_fri_openings(&proof).expect("mmcs");
    }

    #[test]
    fn tampered_trace_opening_fails_val_mmcs() {
        let ctx = AggregationContext {
            parent_task_id: "parent",
            compose_label: "L1:0",
            manifest_root_hash: "",
            left_child_hash: [21u8; CHILD_HASH_LEN],
            right_child_hash: [23u8; CHILD_HASH_LEN],
            security_level: "",
        };
        let transcript = generate_aggregation_proof(&ctx).expect("prove");
        let plonky3 = decode_agg_proof_owned(&transcript, &ctx).expect("decode");
        let proof: Proof<WqcStarkConfig> = postcard::from_bytes(&plonky3).expect("postcard");
        let chal = replay_agg_fri_challenges(&proof).expect("fs");
        let view = decode_pcs_view(&proof).expect("pcs");
        let qp = &view.fri_proof.query_proofs[0];
        let mut input = decode_input_proof(&qp.input_proof).expect("input");
        // Flip a leaf value so ValMmcs must reject.
        if let Some(row) = input.input_openings[0].opened_values.first_mut() {
            if let Some(v) = row.first_mut() {
                *v += Val::ONE;
            }
        }
        let query_index = chal.query_indices[0];
        let config = devnet_circle_config();
        let pcs = config.pcs();
        let degree = 1usize << proof.degree_bits;
        let init_trace_domain = <crate::plonky3_stark::config::Pcs as Pcs<
            Challenge,
            crate::plonky3_stark::config::Challenger,
        >>::natural_domain_for_degree(pcs, degree);
        let log_blowup = chal.log_blowup;
        let log_global_max_height = view.fri_proof.commit_phase_commits.len() + log_blowup + 1;
        let trace_height = init_trace_domain.size() << log_blowup;
        let trace_log_height = log2_strict(trace_height).unwrap();
        let dims = [Dimensions {
            width: AGG_WIDTH,
            height: trace_height,
        }];
        let idx = query_index >> (log_global_max_height - trace_log_height);
        let opening = &input.input_openings[0];
        assert!(pcs
            .mmcs
            .verify_batch(
                &proof.commitments.trace,
                &dims,
                idx,
                BatchOpeningRef::new(&opening.opened_values, &opening.opening_proof),
            )
            .is_err());
    }
}

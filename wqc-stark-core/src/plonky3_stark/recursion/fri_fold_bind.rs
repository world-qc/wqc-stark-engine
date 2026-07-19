//! Bind FriFoldAir steps to AggregationAir Circle FRI openings (R3-M3b1).
//!
//! Replays Fiat-Shamir β / query indices, then for **query 0** extracts every
//! commit-phase arity-2 fold (siblings + FS β). Intermediate queried values are
//! recovered by solving the fold equation backward from `final_poly` (reduced
//! openings / first-layer `fold_y` are not yet reconstructed — honesty bound).

use p3_uni_stark::Proof;

use crate::plonky3_stark::config::{Challenge, WqcStarkConfig};

use super::fri_fold_air::{generate_fri_fold_proof, FriFoldStepProof};
use super::fri_fold_native::{solve_v0_for_fold, solve_v1_for_fold};
use super::fri_fs_replay::{decode_pcs_view, replay_agg_fri_challenges};

/// Number of FRI queries whose fold chains are STARK-proven in the cert (M3b1).
pub const AGG_FRI_PROVEN_QUERIES: usize = 1;

/// Max commit-phase rounds for AggregationAir-sized FRI (`log_blowup=1`, height 4).
pub const AGG_FRI_MAX_ROUNDS: usize = 4;

#[derive(Debug, Clone)]
struct FoldWitness {
    index: usize,
    log_folded_height: usize,
    beta: Challenge,
    v0: Challenge,
    v1: Challenge,
}

/// Builds in-circuit fold proofs for AggregationAir FRI query 0 (all commit rounds).
pub fn fri_fold_steps_from_agg_proof(
    proof: &Proof<WqcStarkConfig>,
) -> Result<Vec<FriFoldStepProof>, String> {
    let chal = replay_agg_fri_challenges(proof)?;
    let view = decode_pcs_view(proof)?;
    let fri = &view.fri_proof;
    if chal.betas.len() != fri.commit_phase_commits.len() {
        return Err("beta count != commit-phase rounds".into());
    }
    if fri.query_proofs.is_empty() {
        return Err("FRI proof has no queries".into());
    }
    if chal.query_indices.is_empty() {
        return Err("no FS query indices".into());
    }

    let mut all_steps = Vec::new();
    for q in 0..AGG_FRI_PROVEN_QUERIES {
        let qp = fri
            .query_proofs
            .get(q)
            .ok_or_else(|| format!("missing FRI query {q}"))?;
        let query_index = *chal
            .query_indices
            .get(q)
            .ok_or_else(|| format!("missing FS query index {q}"))?;
        let witnesses = extract_query_fold_chain(
            qp,
            &chal.betas,
            query_index,
            chal.extra_query_index_bits,
            chal.log_blowup,
            fri.final_poly,
        )?;
        for w in witnesses {
            all_steps.push(generate_fri_fold_proof(
                w.index,
                w.log_folded_height,
                w.beta,
                w.v0,
                w.v1,
            )?);
        }
    }
    Ok(all_steps)
}

fn extract_query_fold_chain(
    qp: &p3_circle::CircleQueryProof<
        Challenge,
        crate::plonky3_stark::config::ChallengeMmcs,
        p3_circle::CircleInputProof<
            crate::plonky3_stark::config::Val,
            Challenge,
            crate::plonky3_stark::config::ValMmcs,
            crate::plonky3_stark::config::ChallengeMmcs,
        >,
    >,
    betas: &[Challenge],
    query_index: usize,
    extra_bits: usize,
    log_blowup: usize,
    final_poly: Challenge,
) -> Result<Vec<FoldWitness>, String> {
    let openings = &qp.commit_phase_openings;
    if openings.len() != betas.len() {
        return Err("commit-phase openings vs betas length mismatch".into());
    }
    if openings.len() > AGG_FRI_MAX_ROUNDS {
        return Err(format!(
            "too many FRI rounds: {} > {AGG_FRI_MAX_ROUNDS}",
            openings.len()
        ));
    }

    let log_arities: Vec<usize> = openings.iter().map(|o| o.log_arity as usize).collect();
    if log_arities.iter().any(|&a| a != 1) {
        return Err("M3b1 only supports arity-2 (log_arity=1) rounds".into());
    }

    // Forward schedule of parent indices / index_in_group / log_folded_height.
    let mut index = query_index >> extra_bits;
    let mut log_current = log_arities.iter().sum::<usize>() + log_blowup;
    let mut schedule = Vec::with_capacity(openings.len());
    for &log_arity in &log_arities {
        let arity = 1 << log_arity;
        let index_in_group = index % arity;
        let log_folded = log_current - log_arity;
        index >>= log_arity;
        schedule.push((index, index_in_group, log_folded));
        log_current = log_folded;
    }
    if log_current != log_blowup {
        return Err(format!(
            "final fold height {log_current} != log_blowup {log_blowup}"
        ));
    }

    // Backward: start from final_poly, solve queried eval each round.
    let mut out = final_poly;
    let mut rev_witnesses = Vec::with_capacity(openings.len());
    for round in (0..openings.len()).rev() {
        let opening = &openings[round];
        if opening.sibling_values.len() != 1 {
            return Err(format!(
                "round {round}: expected 1 sibling, got {}",
                opening.sibling_values.len()
            ));
        }
        let sibling = opening.sibling_values[0];
        let beta = betas[round];
        let (parent_idx, index_in_group, log_folded) = schedule[round];
        let (v0, v1) = if index_in_group == 0 {
            let v0 = solve_v0_for_fold(parent_idx, log_folded, beta, sibling, out);
            (v0, sibling)
        } else if index_in_group == 1 {
            let v1 = solve_v1_for_fold(parent_idx, log_folded, beta, sibling, out);
            (sibling, v1)
        } else {
            return Err(format!("unexpected index_in_group {index_in_group}"));
        };
        // Queried eval at this round becomes the previous round's `out` when going backward
        // (ignoring reduced-opening roll-in — M3b1 honesty bound).
        let queried = if index_in_group == 0 { v0 } else { v1 };
        rev_witnesses.push(FoldWitness {
            index: parent_idx,
            log_folded_height: log_folded,
            beta,
            v0,
            v1,
        });
        out = queried;
    }
    rev_witnesses.reverse();
    Ok(rev_witnesses)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::aggregation::CHILD_HASH_LEN;
    use crate::plonky3_stark::aggregation::AggregationContext;
    use crate::plonky3_stark::generate_aggregation_proof;
    use crate::plonky3_stark::recursion::fri_fold_air::verify_fri_fold_proof;
    use crate::plonky3_stark::recursion::fri_fold_native::{
        challenge_to_limbs, fold_x_row, limbs_to_challenge,
    };
    use crate::plonky3_stark::transcript_v4::decode_agg_proof_owned;

    #[test]
    fn fri_fold_chain_query0_uses_fs_betas() {
        let ctx = AggregationContext {
            parent_task_id: "parent",
            compose_label: "L1:0",
            manifest_root_hash: "",
            left_child_hash: [7u8; CHILD_HASH_LEN],
            right_child_hash: [9u8; CHILD_HASH_LEN],
        };
        let transcript = generate_aggregation_proof(&ctx).expect("prove");
        let plonky3 = decode_agg_proof_owned(&transcript, &ctx).expect("decode");
        let proof: Proof<WqcStarkConfig> = postcard::from_bytes(&plonky3).expect("postcard");
        let chal = replay_agg_fri_challenges(&proof).expect("fs");
        let steps = fri_fold_steps_from_agg_proof(&proof).expect("folds");
        assert_eq!(steps.len(), chal.betas.len());
        for (step, beta) in steps.iter().zip(&chal.betas) {
            assert!(verify_fri_fold_proof(step));
            assert_eq!(step.beta_limbs, challenge_to_limbs(*beta));
        }
        // Chain links: out of round i equals queried input of round i+1 (by construction).
        for win in steps.windows(2) {
            let out = limbs_to_challenge(win[0].out_limbs);
            let v0 = limbs_to_challenge(win[1].v0_limbs);
            let v1 = limbs_to_challenge(win[1].v1_limbs);
            let beta = limbs_to_challenge(win[1].beta_limbs);
            let folded = fold_x_row(
                win[1].index as usize,
                win[1].log_folded_height as usize,
                beta,
                v0,
                v1,
            );
            assert_eq!(folded, limbs_to_challenge(win[1].out_limbs));
            // Previous out equals one of the next inputs (queried slot).
            assert!(out == v0 || out == v1);
        }
        let last_out = limbs_to_challenge(steps.last().unwrap().out_limbs);
        let view = decode_pcs_view(&proof).unwrap();
        assert_eq!(last_out, view.fri_proof.final_poly);
    }
}

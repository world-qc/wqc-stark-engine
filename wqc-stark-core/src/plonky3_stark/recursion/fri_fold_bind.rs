//! Bind FriFoldAir / fold_y steps to AggregationAir Circle FRI (R3-M3b2).
//!
//! Replays Fiat-Shamir challenges, reconstructs query-0 reduced openings via
//! DEEP + λ + `fold_y`, then extracts commit-phase `fold_x` witnesses with real
//! queried evals (no `solve_v0`).

use p3_field::PrimeCharacteristicRing;
use p3_uni_stark::Proof;

use crate::plonky3_stark::config::{Challenge, WqcStarkConfig};

use super::fri_fold_air::{generate_fri_fold_proof, generate_fri_fold_y_proof, FriFoldStepProof};
use super::fri_fold_native::fold_x_row;
use super::fri_fs_replay::{decode_pcs_view, replay_agg_fri_challenges};
use super::fri_ro::reconstruct_agg_query_ro;

/// Number of FRI queries whose fold chains are STARK-proven in the cert.
pub const AGG_FRI_PROVEN_QUERIES: usize = 1;

/// Max commit-phase rounds for AggregationAir-sized FRI.
pub const AGG_FRI_MAX_ROUNDS: usize = 4;

/// Max first-layer fold_y steps (one per LDE height; Agg has 2).
pub const AGG_FRI_MAX_FOLD_YS: usize = 4;

#[derive(Debug, Clone)]
struct FoldWitness {
    index: usize,
    log_folded_height: usize,
    beta: Challenge,
    v0: Challenge,
    v1: Challenge,
}

/// Query-0 FRI fold proofs: first-layer `fold_y`s then commit-phase `fold_x`s.
#[derive(Debug, Clone)]
pub struct AggFriFoldBundle {
    pub fold_ys: Vec<FriFoldStepProof>,
    pub fold_xs: Vec<FriFoldStepProof>,
}

/// Builds in-circuit fold proofs for AggregationAir FRI query 0.
pub fn fri_fold_bundle_from_agg_proof(
    proof: &Proof<WqcStarkConfig>,
) -> Result<AggFriFoldBundle, String> {
    let chal = replay_agg_fri_challenges(proof)?;
    let view = decode_pcs_view(proof)?;
    let fri = &view.fri_proof;
    if chal.betas.len() != fri.commit_phase_commits.len() {
        return Err("beta count != commit-phase rounds".into());
    }

    let mut fold_ys = Vec::new();
    let mut fold_xs = Vec::new();
    for q in 0..AGG_FRI_PROVEN_QUERIES {
        let qp = fri
            .query_proofs
            .get(q)
            .ok_or_else(|| format!("missing FRI query {q}"))?;
        let query_index = *chal
            .query_indices
            .get(q)
            .ok_or_else(|| format!("missing FS query index {q}"))?;
        let (reduced, y_wits) = reconstruct_agg_query_ro(proof, &chal, &view, q)?;
        if y_wits.len() > AGG_FRI_MAX_FOLD_YS {
            return Err(format!("too many fold_y steps: {}", y_wits.len()));
        }
        for w in &y_wits {
            fold_ys.push(generate_fri_fold_y_proof(
                w.index,
                w.log_folded_height,
                w.beta,
                w.v0,
                w.v1,
            )?);
        }
        let x_wits = extract_query_fold_chain_forward(
            qp,
            &chal.betas,
            query_index,
            chal.extra_query_index_bits,
            chal.log_blowup,
            fri.final_poly,
            &reduced,
        )?;
        for w in x_wits {
            fold_xs.push(generate_fri_fold_proof(
                w.index,
                w.log_folded_height,
                w.beta,
                w.v0,
                w.v1,
            )?);
        }
    }
    Ok(AggFriFoldBundle { fold_ys, fold_xs })
}

/// Legacy helper: commit-phase fold_x steps only.
pub fn fri_fold_steps_from_agg_proof(
    proof: &Proof<WqcStarkConfig>,
) -> Result<Vec<FriFoldStepProof>, String> {
    Ok(fri_fold_bundle_from_agg_proof(proof)?.fold_xs)
}

fn extract_query_fold_chain_forward(
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
    reduced: &[(usize, Challenge)],
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
    if openings.iter().any(|o| o.log_arity != 1) {
        return Err("M3b2 only supports arity-2 (log_arity=1) rounds".into());
    }

    let mut index = query_index >> extra_bits;
    let mut log_current = openings.len() + log_blowup; // sum(log_arities)=rounds when all 1
    let mut folded_eval = Challenge::ZERO;
    let mut ro_iter = reduced.iter().peekable();
    let mut witnesses = Vec::with_capacity(openings.len());

    for (round, opening) in openings.iter().enumerate() {
        if let Some(&&(lh, ro)) = ro_iter.peek() {
            if lh == log_current {
                folded_eval += ro;
                ro_iter.next();
            }
        }
        if opening.sibling_values.len() != 1 {
            return Err(format!(
                "round {round}: expected 1 sibling, got {}",
                opening.sibling_values.len()
            ));
        }
        let sibling = opening.sibling_values[0];
        let index_in_group = index % 2;
        let (v0, v1) = if index_in_group == 0 {
            (folded_eval, sibling)
        } else {
            (sibling, folded_eval)
        };
        let log_folded = log_current - 1;
        index >>= 1;
        let out = fold_x_row(index, log_folded, betas[round], v0, v1);
        witnesses.push(FoldWitness {
            index,
            log_folded_height: log_folded,
            beta: betas[round],
            v0,
            v1,
        });
        folded_eval = out;
        log_current = log_folded;
    }
    if log_current != log_blowup {
        return Err(format!(
            "final fold height {log_current} != log_blowup {log_blowup}"
        ));
    }
    if folded_eval != final_poly {
        return Err("forward FRI fold chain does not match final_poly".into());
    }
    if ro_iter.next().is_some() {
        return Err("unused reduced openings remain".into());
    }
    Ok(witnesses)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::aggregation::CHILD_HASH_LEN;
    use crate::plonky3_stark::aggregation::AggregationContext;
    use crate::plonky3_stark::generate_aggregation_proof;
    use crate::plonky3_stark::recursion::fri_fold_air::{
        verify_fri_fold_proof, verify_fri_fold_y_proof,
    };
    use crate::plonky3_stark::recursion::fri_fold_native::{
        challenge_to_limbs, limbs_to_challenge,
    };
    use crate::plonky3_stark::transcript_v4::decode_agg_proof_owned;

    #[test]
    fn fri_fold_bundle_query0_matches_final_poly() {
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
        let bundle = fri_fold_bundle_from_agg_proof(&proof).expect("bundle");
        assert_eq!(bundle.fold_ys.len(), 2);
        assert_eq!(bundle.fold_xs.len(), chal.betas.len());
        for y in &bundle.fold_ys {
            assert!(verify_fri_fold_y_proof(y));
            assert_eq!(y.beta_limbs, challenge_to_limbs(chal.bivariate_beta));
        }
        for (step, beta) in bundle.fold_xs.iter().zip(&chal.betas) {
            assert!(verify_fri_fold_proof(step));
            assert_eq!(step.beta_limbs, challenge_to_limbs(*beta));
        }
        let last_out = limbs_to_challenge(bundle.fold_xs.last().unwrap().out_limbs);
        let view = decode_pcs_view(&proof).unwrap();
        assert_eq!(last_out, view.fri_proof.final_poly);
    }
}

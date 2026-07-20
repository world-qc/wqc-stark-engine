//! Bind FriFoldAir / fold_y steps to AggregationAir Circle FRI (R3-M3b3).
//!
//! Covers **all** devnet FRI queries: reconstructs reduced openings (DEEP + λ +
//! `fold_y`) and extracts commit-phase `fold_x` witnesses with real queried evals.

use p3_field::PrimeCharacteristicRing;
use p3_uni_stark::Proof;

use crate::plonky3_stark::config::{Challenge, WqcStarkConfig, DEVNET_FRI_NUM_QUERIES};

use super::fri_fold_air::{generate_fri_fold_proof, generate_fri_fold_y_proof, FriFoldStepProof};
use super::fri_fold_native::{challenge_to_limbs, fold_x_row, fold_y_row};
use super::fri_fs_replay::{decode_pcs_view, replay_fri_challenges};
use super::fri_ro::reconstruct_query_ro;

/// Number of FRI queries whose fold chains are STARK-proven in the cert (M3b3: all).
pub const AGG_FRI_PROVEN_QUERIES: usize = DEVNET_FRI_NUM_QUERIES;

/// Leaf certs use the same FRI query count as AggregationAir (devnet config).
pub const LEAF_FRI_PROVEN_QUERIES: usize = DEVNET_FRI_NUM_QUERIES;

/// Max commit-phase rounds for AggregationAir-sized FRI.
pub const AGG_FRI_MAX_ROUNDS: usize = 4;

/// Max commit-phase rounds for leaf FRI (generous).
pub const LEAF_FRI_MAX_ROUNDS: usize = 20;

/// Max first-layer fold_y steps per query (one per LDE height; Agg has 2).
pub const AGG_FRI_MAX_FOLD_YS_PER_QUERY: usize = 4;

/// Max total first-layer fold_y steps across proven queries.
pub const AGG_FRI_MAX_FOLD_YS: usize = AGG_FRI_MAX_FOLD_YS_PER_QUERY * AGG_FRI_PROVEN_QUERIES;

#[derive(Debug, Clone)]
pub(crate) struct FoldWitness {
    index: usize,
    log_folded_height: usize,
    beta: Challenge,
    v0: Challenge,
    v1: Challenge,
}

/// FRI fold proofs for proven queries: first-layer `fold_y`s then commit-phase `fold_x`s.
#[derive(Debug, Clone)]
pub struct AggFriFoldBundle {
    pub fold_ys: Vec<FriFoldStepProof>,
    pub fold_xs: Vec<FriFoldStepProof>,
}

/// True when the cert proves every FRI query used by [`devnet_circle_config`].
pub const fn covers_all_devnet_fri_queries() -> bool {
    AGG_FRI_PROVEN_QUERIES >= DEVNET_FRI_NUM_QUERIES
}

/// Builds in-circuit fold proofs for a uni-STARK FRI (all proven queries).
pub fn fri_fold_bundle_from_proof(
    proof: &Proof<WqcStarkConfig>,
    trace_width: usize,
) -> Result<AggFriFoldBundle, String> {
    let chal = replay_fri_challenges(proof, trace_width)?;
    let view = decode_pcs_view(proof)?;
    let fri = &view.fri_proof;
    if chal.betas.len() != fri.commit_phase_commits.len() {
        return Err("beta count != commit-phase rounds".into());
    }
    if chal.query_indices.len() < LEAF_FRI_PROVEN_QUERIES {
        return Err(format!(
            "FS query count {} < proven {}",
            chal.query_indices.len(),
            LEAF_FRI_PROVEN_QUERIES
        ));
    }
    let max_rounds = if trace_width == crate::plonky3_stark::aggregation_air::AGG_WIDTH {
        AGG_FRI_MAX_ROUNDS
    } else {
        LEAF_FRI_MAX_ROUNDS
    };

    let mut fold_ys = Vec::new();
    let mut fold_xs = Vec::new();
    for q in 0..LEAF_FRI_PROVEN_QUERIES {
        let qp = fri
            .query_proofs
            .get(q)
            .ok_or_else(|| format!("missing FRI query {q}"))?;
        let query_index = chal.query_indices[q];
        let (reduced, y_wits) = reconstruct_query_ro(proof, &chal, &view, q, trace_width)?;
        if y_wits.len() > AGG_FRI_MAX_FOLD_YS_PER_QUERY {
            return Err(format!(
                "too many fold_y steps on query {q}: {}",
                y_wits.len()
            ));
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
            max_rounds,
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

/// Builds in-circuit fold proofs for AggregationAir FRI (all proven queries).
pub fn fri_fold_bundle_from_agg_proof(
    proof: &Proof<WqcStarkConfig>,
) -> Result<AggFriFoldBundle, String> {
    fri_fold_bundle_from_proof(proof, crate::plonky3_stark::aggregation_air::AGG_WIDTH)
}

/// Legacy helper: commit-phase fold_x steps only.
pub fn fri_fold_steps_from_agg_proof(
    proof: &Proof<WqcStarkConfig>,
) -> Result<Vec<FriFoldStepProof>, String> {
    Ok(fri_fold_bundle_from_agg_proof(proof)?.fold_xs)
}

/// Host-checks that cert fold publics match RO-forward witnesses (any trace width).
pub fn bind_fri_fold_bundle_to_proof_width(
    proof: &Proof<WqcStarkConfig>,
    fold_ys: &[FriFoldStepProof],
    fold_xs: &[FriFoldStepProof],
    trace_width: usize,
) -> Result<(), String> {
    let chal = replay_fri_challenges(proof, trace_width)?;
    let view = decode_pcs_view(proof)?;
    let fri = &view.fri_proof;
    let max_rounds = if trace_width == crate::plonky3_stark::aggregation_air::AGG_WIDTH {
        AGG_FRI_MAX_ROUNDS
    } else {
        LEAF_FRI_MAX_ROUNDS
    };
    let mut y_off = 0usize;
    let mut x_off = 0usize;
    for q in 0..LEAF_FRI_PROVEN_QUERIES {
        let qp = fri
            .query_proofs
            .get(q)
            .ok_or_else(|| format!("missing FRI query {q}"))?;
        let (reduced, y_wits) = reconstruct_query_ro(proof, &chal, &view, q, trace_width)?;
        for w in &y_wits {
            let step = fold_ys
                .get(y_off)
                .ok_or_else(|| format!("missing fold_y step at {y_off}"))?;
            if !fold_step_matches_y(step, w.index, w.log_folded_height, w.beta, w.v0, w.v1) {
                return Err(format!("fold_y public mismatch at query {q} step {y_off}"));
            }
            y_off += 1;
        }
        let x_wits = extract_query_fold_chain_forward(
            qp,
            &chal.betas,
            chal.query_indices[q],
            chal.extra_query_index_bits,
            chal.log_blowup,
            fri.final_poly,
            &reduced,
            max_rounds,
        )?;
        for w in &x_wits {
            let step = fold_xs
                .get(x_off)
                .ok_or_else(|| format!("missing fold_x step at {x_off}"))?;
            if !fold_step_matches_x(step, w.index, w.log_folded_height, w.beta, w.v0, w.v1) {
                return Err(format!("fold_x public mismatch at query {q} step {x_off}"));
            }
            x_off += 1;
        }
    }
    if y_off != fold_ys.len() {
        return Err(format!(
            "fold_y count mismatch: bound {y_off}, cert {}",
            fold_ys.len()
        ));
    }
    if x_off != fold_xs.len() {
        return Err(format!(
            "fold_x count mismatch: bound {x_off}, cert {}",
            fold_xs.len()
        ));
    }
    Ok(())
}

/// Host-checks that cert fold publics match RO-forward witnesses from `proof` (no STARK prove).
pub fn bind_fri_fold_bundle_to_proof(
    proof: &Proof<WqcStarkConfig>,
    fold_ys: &[FriFoldStepProof],
    fold_xs: &[FriFoldStepProof],
) -> Result<(), String> {
    bind_fri_fold_bundle_to_proof_width(
        proof,
        fold_ys,
        fold_xs,
        crate::plonky3_stark::aggregation_air::AGG_WIDTH,
    )
}

fn fold_step_matches_x(
    step: &FriFoldStepProof,
    index: usize,
    log_folded_height: usize,
    beta: Challenge,
    v0: Challenge,
    v1: Challenge,
) -> bool {
    let out = fold_x_row(index, log_folded_height, beta, v0, v1);
    step.index as usize == index
        && step.log_folded_height as usize == log_folded_height
        && step.beta_limbs == challenge_to_limbs(beta)
        && step.v0_limbs == challenge_to_limbs(v0)
        && step.v1_limbs == challenge_to_limbs(v1)
        && step.out_limbs == challenge_to_limbs(out)
}

fn fold_step_matches_y(
    step: &FriFoldStepProof,
    index: usize,
    log_folded_height: usize,
    beta: Challenge,
    v0: Challenge,
    v1: Challenge,
) -> bool {
    let out = fold_y_row(index, log_folded_height, beta, v0, v1);
    step.index as usize == index
        && step.log_folded_height as usize == log_folded_height
        && step.beta_limbs == challenge_to_limbs(beta)
        && step.v0_limbs == challenge_to_limbs(v0)
        && step.v1_limbs == challenge_to_limbs(v1)
        && step.out_limbs == challenge_to_limbs(out)
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn extract_query_fold_chain_forward(
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
    max_rounds: usize,
) -> Result<Vec<FoldWitness>, String> {
    let openings = &qp.commit_phase_openings;
    if openings.len() != betas.len() {
        return Err("commit-phase openings vs betas length mismatch".into());
    }
    if openings.len() > max_rounds {
        return Err(format!(
            "too many FRI rounds: {} > {max_rounds}",
            openings.len()
        ));
    }
    if openings.iter().any(|o| o.log_arity != 1) {
        return Err("M3b3 only supports arity-2 (log_arity=1) rounds".into());
    }

    let mut index = query_index >> extra_bits;
    let mut log_current = openings.len() + log_blowup;
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
        let _out = fold_x_row(index, log_folded, betas[round], v0, v1);
        witnesses.push(FoldWitness {
            index,
            log_folded_height: log_folded,
            beta: betas[round],
            v0,
            v1,
        });
        folded_eval = _out;
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
    use crate::plonky3_stark::recursion::fri_fold_native::limbs_to_challenge;
    use crate::plonky3_stark::recursion::fri_fs_replay::replay_agg_fri_challenges;
    use crate::plonky3_stark::transcript_v4::decode_agg_proof_owned;

    #[test]
    fn fri_fold_bundle_all_queries_match_final_poly() {
        assert!(covers_all_devnet_fri_queries());
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
        assert_eq!(bundle.fold_ys.len(), 2 * AGG_FRI_PROVEN_QUERIES);
        assert_eq!(
            bundle.fold_xs.len(),
            chal.betas.len() * AGG_FRI_PROVEN_QUERIES
        );
        bind_fri_fold_bundle_to_proof(&proof, &bundle.fold_ys, &bundle.fold_xs).expect("bind");
        // Spot-check first and last STARKs (full verify of 160 is covered by cert roundtrip).
        assert!(verify_fri_fold_y_proof(&bundle.fold_ys[0]));
        assert!(verify_fri_fold_y_proof(bundle.fold_ys.last().unwrap()));
        assert!(verify_fri_fold_proof(&bundle.fold_xs[0]));
        assert!(verify_fri_fold_proof(bundle.fold_xs.last().unwrap()));
        let last_out = limbs_to_challenge(bundle.fold_xs.last().unwrap().out_limbs);
        let view = decode_pcs_view(&proof).unwrap();
        assert_eq!(last_out, view.fri_proof.final_poly);
    }
}

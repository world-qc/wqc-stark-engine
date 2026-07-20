//! Bind DeepRoAir (quotient W=3, query 0) to AggregationAir FriFoldY (R3-M3c1).

use p3_commit::{Pcs, PolynomialSpace};
use p3_uni_stark::{Proof, StarkGenericConfig};

use crate::plonky3_stark::config::{devnet_circle_config, Challenge, WqcStarkConfig};

use super::deep_ro_air::{generate_deep_ro_proof, verify_deep_ro_proof, DeepRoStepProof};
use super::fri_fold_air::FriFoldStepProof;
use super::fri_fold_native::{
    cfft_permute_index, challenge_to_limbs, limbs_to_challenge, standard_nth_point,
};
use super::fri_fs_replay::{decode_pcs_view, replay_agg_fri_challenges};
use super::fri_ro::{decode_input_proof, reconstruct_agg_query_ro};

/// M3c1: at most one DeepRo step (query-0 quotient).
pub const AGG_DEEP_RO_MAX: usize = 1;

fn log2_size(n: usize) -> usize {
    let mut log = 0usize;
    let mut m = n;
    while m > 1 {
        m >>= 1;
        log += 1;
    }
    log
}

/// Prove DeepRo for AggregationAir FRI query 0 quotient batch.
pub fn deep_ro_quot_query0_from_agg_proof(
    proof: &Proof<WqcStarkConfig>,
) -> Result<DeepRoStepProof, String> {
    let chal = replay_agg_fri_challenges(proof)?;
    let view = decode_pcs_view(proof)?;
    let qp = view
        .fri_proof
        .query_proofs
        .first()
        .ok_or_else(|| "missing FRI query 0".to_string())?;
    let input = decode_input_proof(&qp.input_proof)?;
    if input.input_openings.len() != 2 {
        return Err("expected 2 input openings".into());
    }
    if proof.opened_values.quotient_chunks.len() != 1 {
        return Err("expected 1 quotient chunk".into());
    }

    let config = devnet_circle_config();
    let pcs = config.pcs();
    let degree = 1usize << proof.degree_bits;
    let init_trace_domain = <crate::plonky3_stark::config::Pcs as Pcs<
        Challenge,
        crate::plonky3_stark::config::Challenger,
    >>::natural_domain_for_degree(pcs, degree);
    let quotient_domain = init_trace_domain.create_disjoint_domain(degree);
    let log_blowup = chal.log_blowup;
    let quot_log_height = log2_size(quotient_domain.size()) + log_blowup;
    let log_global_max_height = view.fri_proof.commit_phase_commits.len() + log_blowup + 1;
    let query_index = chal.query_indices[0];
    let bits_reduced = log_global_max_height - quot_log_height;
    let orig_idx = cfft_permute_index(query_index >> bits_reduced, quot_log_height);
    let p = standard_nth_point(quot_log_height, orig_idx);

    let opened = input.input_openings[1]
        .opened_values
        .first()
        .ok_or_else(|| "empty quotient opening".to_string())?;
    if opened.len() != 3 {
        return Err(format!("quotient opening width {}, want 3", opened.len()));
    }
    let px = [opened[0], opened[1], opened[2]];
    let ps_at_zeta = &proof.opened_values.quotient_chunks[0];
    if ps_at_zeta.len() != 3 {
        return Err(format!("quotient OOD len {}, want 3", ps_at_zeta.len()));
    }
    let pz = [ps_at_zeta[0], ps_at_zeta[1], ps_at_zeta[2]];

    // lambdas ordered by ascending reduced-opening height (BTreeMap).
    let trace_log_height = log2_size(init_trace_domain.size()) + log_blowup;
    let mut heights = [trace_log_height, quot_log_height];
    heights.sort();
    let lambda_idx = heights
        .iter()
        .position(|&h| h == quot_log_height)
        .ok_or_else(|| "quot height missing".to_string())?;
    let lambda = *view
        .lambdas
        .get(lambda_idx)
        .ok_or_else(|| "missing lambda for quot height".to_string())?;

    let log_n = quot_log_height - log_blowup;
    generate_deep_ro_proof(p.x, p.y, chal.batch_alpha, px, pz, lambda, log_n, chal.zeta)
}

/// Bind DeepRo out to the quotient-height FriFoldY queried leaf (query 0).
pub fn bind_deep_ro_to_fold_y(
    proof: &Proof<WqcStarkConfig>,
    deep_ro: &DeepRoStepProof,
    fold_ys: &[FriFoldStepProof],
) -> Result<(), String> {
    if !verify_deep_ro_proof(deep_ro) {
        return Err("DeepRo STARK verify failed".into());
    }
    let chal = replay_agg_fri_challenges(proof)?;
    let view = decode_pcs_view(proof)?;
    let (_ros, y_wits) = reconstruct_agg_query_ro(proof, &chal, &view, 0)?;

    let config = devnet_circle_config();
    let pcs = config.pcs();
    let degree = 1usize << proof.degree_bits;
    let init_trace_domain = <crate::plonky3_stark::config::Pcs as Pcs<
        Challenge,
        crate::plonky3_stark::config::Challenger,
    >>::natural_domain_for_degree(pcs, degree);
    let quotient_domain = init_trace_domain.create_disjoint_domain(degree);
    let log_blowup = chal.log_blowup;
    let quot_log_height = log2_size(quotient_domain.size()) + log_blowup;
    let log_folded = quot_log_height - 1;
    let log_global_max_height = view.fri_proof.commit_phase_commits.len() + log_blowup + 1;
    let query_index = chal.query_indices[0];
    let bits_reduced = log_global_max_height - quot_log_height;
    let queried_slot = (query_index >> bits_reduced) & 1;

    // FS / opening bind
    if deep_ro.alpha_limbs != challenge_to_limbs(chal.batch_alpha) {
        return Err("DeepRo alpha != batch_alpha".into());
    }
    if deep_ro.zeta_limbs != challenge_to_limbs(chal.zeta) {
        return Err("DeepRo zeta mismatch".into());
    }
    if deep_ro.log_n as usize != quot_log_height - log_blowup {
        return Err("DeepRo log_n mismatch".into());
    }

    let qp = &view.fri_proof.query_proofs[0];
    let input = decode_input_proof(&qp.input_proof)?;
    let opened = input.input_openings[1]
        .opened_values
        .first()
        .ok_or_else(|| "empty quotient opening".to_string())?;
    if opened.len() != 3 || deep_ro.px != [opened[0], opened[1], opened[2]] {
        return Err("DeepRo px != quotient opening".into());
    }
    let ps_at_zeta = &proof.opened_values.quotient_chunks[0];
    if ps_at_zeta.len() != 3 {
        return Err("quotient OOD len != 3".into());
    }
    for (i, &pz_i) in ps_at_zeta.iter().enumerate().take(3) {
        if deep_ro.pz_limbs[i] != challenge_to_limbs(pz_i) {
            return Err(format!("DeepRo pz[{i}] mismatch"));
        }
    }

    let orig_idx = cfft_permute_index(query_index >> bits_reduced, quot_log_height);
    let p = standard_nth_point(quot_log_height, orig_idx);
    if deep_ro.sx != p.x || deep_ro.sy != p.y {
        return Err("DeepRo circle point mismatch".into());
    }

    let trace_log_height = log2_size(init_trace_domain.size()) + log_blowup;
    let mut heights = [trace_log_height, quot_log_height];
    heights.sort();
    let lambda_idx = heights
        .iter()
        .position(|&h| h == quot_log_height)
        .ok_or_else(|| "quot height missing".to_string())?;
    let lambda = view.lambdas[lambda_idx];
    if deep_ro.lambda_limbs != challenge_to_limbs(lambda) {
        return Err("DeepRo lambda mismatch".into());
    }

    // Find query-0 FriFoldY for this height among fold_ys (all queries concatenated).
    // Query 0 fold_ys come first: 2 steps (ascending height order matching y_wits).
    let y_wit = y_wits
        .iter()
        .find(|w| w.log_folded_height == log_folded)
        .ok_or_else(|| "missing fold_y witness for quot height".to_string())?;
    let fold = fold_ys
        .iter()
        .take(y_wits.len())
        .find(|f| f.log_folded_height as usize == log_folded && f.index as usize == y_wit.index)
        .ok_or_else(|| "missing FriFoldY for quot height on query 0".to_string())?;

    let out = limbs_to_challenge(deep_ro.out_limbs);
    let leaf = if queried_slot == 0 {
        limbs_to_challenge(fold.v0_limbs)
    } else {
        limbs_to_challenge(fold.v1_limbs)
    };
    if out != leaf {
        return Err("DeepRo out != FriFoldY queried leaf".into());
    }
    if out
        != (if queried_slot == 0 {
            y_wit.v0
        } else {
            y_wit.v1
        })
    {
        return Err("DeepRo out != reconstructed fold_y leaf".into());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::aggregation::CHILD_HASH_LEN;
    use crate::plonky3_stark::aggregation::AggregationContext;
    use crate::plonky3_stark::generate_aggregation_proof;
    use crate::plonky3_stark::recursion::fri_fold_bind::fri_fold_bundle_from_agg_proof;
    use crate::plonky3_stark::transcript_v4::decode_agg_proof_owned;

    #[test]
    fn deep_ro_quot_query0_binds_fold_y() {
        let ctx = AggregationContext {
            parent_task_id: "parent",
            compose_label: "L1:0",
            manifest_root_hash: "",
            left_child_hash: [31u8; CHILD_HASH_LEN],
            right_child_hash: [33u8; CHILD_HASH_LEN],
        };
        let transcript = generate_aggregation_proof(&ctx).expect("prove");
        let plonky3 = decode_agg_proof_owned(&transcript, &ctx).expect("decode");
        let proof: Proof<WqcStarkConfig> = postcard::from_bytes(&plonky3).expect("postcard");
        let deep = deep_ro_quot_query0_from_agg_proof(&proof).expect("deep");
        assert!(verify_deep_ro_proof(&deep));
        let bundle = fri_fold_bundle_from_agg_proof(&proof).expect("bundle");
        bind_deep_ro_to_fold_y(&proof, &deep, &bundle.fold_ys).expect("bind");
    }
}

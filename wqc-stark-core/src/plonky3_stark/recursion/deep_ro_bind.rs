//! Bind DeepRo / DeepRoTrace (all FRI queries) to AggregationAir FriFoldY (R3-M3c3).

use p3_commit::{Pcs, PolynomialSpace};
use p3_field::PrimeCharacteristicRing;
use p3_uni_stark::{Proof, StarkGenericConfig};

use crate::plonky3_stark::aggregation_air::AGG_WIDTH;
use crate::plonky3_stark::config::{devnet_circle_config, Challenge, WqcStarkConfig};

use super::deep_ro_air::{generate_deep_ro_proof, verify_deep_ro_proof, DeepRoStepProof};
use super::deep_ro_leaf_trace_air::{
    generate_deep_ro_leaf_trace_proof, verify_deep_ro_leaf_trace_proof, DeepRoLeafTraceStepProof,
};
use super::deep_ro_trace_air::{
    generate_deep_ro_trace_proof, verify_deep_ro_trace_proof, DeepRoTraceStepProof,
};
use super::fri_fold_air::FriFoldStepProof;
use super::fri_fold_bind::{AGG_FRI_PROVEN_QUERIES, LEAF_FRI_PROVEN_QUERIES};
use super::fri_fold_native::{
    cfft_permute_index, challenge_to_limbs, limbs_to_challenge, standard_nth_point,
};
use super::fri_fs_replay::{
    decode_pcs_view, replay_agg_fri_challenges, replay_fri_challenges, AggFriChallenges,
    CirclePcsProofView,
};
use super::fri_ro::{decode_input_proof, reconstruct_agg_query_ro, reconstruct_query_ro};

/// M3c3: one DeepRo (quot) per proven FRI query.
pub const AGG_DEEP_RO_MAX: usize = AGG_FRI_PROVEN_QUERIES;

/// M3c3: one DeepRoTrace per proven FRI query.
pub const AGG_DEEP_RO_TRACE_MAX: usize = AGG_FRI_PROVEN_QUERIES;

/// Quotient + trace DeepRo proofs for all proven FRI queries (index = query).
#[derive(Debug, Clone)]
pub struct AggDeepRoBundle {
    pub deep_ros: Vec<DeepRoStepProof>,
    pub deep_ro_traces: Vec<DeepRoTraceStepProof>,
}

fn log2_size(n: usize) -> usize {
    let mut log = 0usize;
    let mut m = n;
    while m > 1 {
        m >>= 1;
        log += 1;
    }
    log
}

/// Offset into concatenated `fold_ys` for the start of query `q`'s fold_y steps.
fn fold_y_offset_for_query(
    proof: &Proof<WqcStarkConfig>,
    chal: &AggFriChallenges,
    view: &CirclePcsProofView,
    query: usize,
) -> Result<usize, String> {
    let mut off = 0usize;
    for q in 0..query {
        let (_ros, y_wits) = reconstruct_agg_query_ro(proof, chal, view, q)?;
        off += y_wits.len();
    }
    Ok(off)
}

/// Prove DeepRo for AggregationAir FRI quotient batch at `query`.
pub fn deep_ro_quot_from_agg_proof(
    proof: &Proof<WqcStarkConfig>,
    query: usize,
) -> Result<DeepRoStepProof, String> {
    let chal = replay_agg_fri_challenges(proof)?;
    let view = decode_pcs_view(proof)?;
    if query >= chal.query_indices.len() {
        return Err(format!("query {query} out of range"));
    }
    let qp = view
        .fri_proof
        .query_proofs
        .get(query)
        .ok_or_else(|| format!("missing FRI query {query}"))?;
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
    let query_index = chal.query_indices[query];
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

/// Prove DeepRo for AggregationAir FRI query 0 quotient batch.
pub fn deep_ro_quot_query0_from_agg_proof(
    proof: &Proof<WqcStarkConfig>,
) -> Result<DeepRoStepProof, String> {
    deep_ro_quot_from_agg_proof(proof, 0)
}

/// Bind DeepRo out to the quotient-height FriFoldY queried leaf at `query`.
pub fn bind_deep_ro_to_fold_y(
    proof: &Proof<WqcStarkConfig>,
    deep_ro: &DeepRoStepProof,
    fold_ys: &[FriFoldStepProof],
    query: usize,
) -> Result<(), String> {
    if !verify_deep_ro_proof(deep_ro) {
        return Err("DeepRo STARK verify failed".into());
    }
    let chal = replay_agg_fri_challenges(proof)?;
    let view = decode_pcs_view(proof)?;
    if query >= chal.query_indices.len() {
        return Err(format!("query {query} out of range"));
    }
    let (_ros, y_wits) = reconstruct_agg_query_ro(proof, &chal, &view, query)?;
    let y_off = fold_y_offset_for_query(proof, &chal, &view, query)?;

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
    let query_index = chal.query_indices[query];
    let bits_reduced = log_global_max_height - quot_log_height;
    let queried_slot = (query_index >> bits_reduced) & 1;

    if deep_ro.alpha_limbs != challenge_to_limbs(chal.batch_alpha) {
        return Err("DeepRo alpha != batch_alpha".into());
    }
    if deep_ro.zeta_limbs != challenge_to_limbs(chal.zeta) {
        return Err("DeepRo zeta mismatch".into());
    }
    if deep_ro.log_n as usize != quot_log_height - log_blowup {
        return Err("DeepRo log_n mismatch".into());
    }

    let qp = &view.fri_proof.query_proofs[query];
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

    let y_wit = y_wits
        .iter()
        .find(|w| w.log_folded_height == log_folded)
        .ok_or_else(|| "missing fold_y witness for quot height".to_string())?;
    let fold = fold_ys
        .iter()
        .skip(y_off)
        .take(y_wits.len())
        .find(|f| f.log_folded_height as usize == log_folded && f.index as usize == y_wit.index)
        .ok_or_else(|| format!("missing FriFoldY for quot height on query {query}"))?;

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

/// Prove DeepRoTrace for AggregationAir FRI trace batch at `query`.
pub fn deep_ro_trace_from_agg_proof(
    proof: &Proof<WqcStarkConfig>,
    query: usize,
) -> Result<DeepRoTraceStepProof, String> {
    let chal = replay_agg_fri_challenges(proof)?;
    let view = decode_pcs_view(proof)?;
    if query >= chal.query_indices.len() {
        return Err(format!("query {query} out of range"));
    }
    let qp = view
        .fri_proof
        .query_proofs
        .get(query)
        .ok_or_else(|| format!("missing FRI query {query}"))?;
    let input = decode_input_proof(&qp.input_proof)?;
    if input.input_openings.len() != 2 {
        return Err("expected 2 input openings".into());
    }

    let config = devnet_circle_config();
    let pcs = config.pcs();
    let degree = 1usize << proof.degree_bits;
    let init_trace_domain = <crate::plonky3_stark::config::Pcs as Pcs<
        Challenge,
        crate::plonky3_stark::config::Challenger,
    >>::natural_domain_for_degree(pcs, degree);
    let zeta = chal.zeta;
    let zeta_next = init_trace_domain
        .next_point(zeta)
        .ok_or_else(|| "trace domain next_point unavailable".to_string())?;
    let log_blowup = chal.log_blowup;
    let trace_log_height = log2_size(init_trace_domain.size()) + log_blowup;
    let quotient_domain = init_trace_domain.create_disjoint_domain(degree);
    let quot_log_height = log2_size(quotient_domain.size()) + log_blowup;
    let log_global_max_height = view.fri_proof.commit_phase_commits.len() + log_blowup + 1;
    let query_index = chal.query_indices[query];
    let bits_reduced = log_global_max_height - trace_log_height;
    let orig_idx = cfft_permute_index(query_index >> bits_reduced, trace_log_height);
    let p = standard_nth_point(trace_log_height, orig_idx);

    let opened = input.input_openings[0]
        .opened_values
        .first()
        .ok_or_else(|| "empty trace opening".to_string())?;
    if opened.len() != AGG_WIDTH {
        return Err(format!(
            "trace opening width {}, want {AGG_WIDTH}",
            opened.len()
        ));
    }
    let mut px_arr = [opened[0]; AGG_WIDTH];
    px_arr.copy_from_slice(opened.as_slice());

    let trace_local = &proof.opened_values.trace_local;
    let trace_next = proof
        .opened_values
        .trace_next
        .as_ref()
        .ok_or_else(|| "missing trace_next".to_string())?;
    if trace_local.len() != AGG_WIDTH || trace_next.len() != AGG_WIDTH {
        return Err("trace OOD width mismatch".into());
    }
    let mut pz_local = [Challenge::ZERO; AGG_WIDTH];
    let mut pz_next = [Challenge::ZERO; AGG_WIDTH];
    pz_local.copy_from_slice(trace_local.as_slice());
    pz_next.copy_from_slice(trace_next.as_slice());

    let mut heights = [trace_log_height, quot_log_height];
    heights.sort();
    let lambda_idx = heights
        .iter()
        .position(|&h| h == trace_log_height)
        .ok_or_else(|| "trace height missing".to_string())?;
    let lambda = *view
        .lambdas
        .get(lambda_idx)
        .ok_or_else(|| "missing lambda for trace height".to_string())?;

    let log_n = trace_log_height - log_blowup;
    generate_deep_ro_trace_proof(
        p.x,
        p.y,
        chal.batch_alpha,
        &px_arr,
        &pz_local,
        &pz_next,
        lambda,
        log_n,
        zeta,
        zeta_next,
    )
}

/// Prove DeepRoTrace for AggregationAir FRI query 0 trace batch.
pub fn deep_ro_trace_query0_from_agg_proof(
    proof: &Proof<WqcStarkConfig>,
) -> Result<DeepRoTraceStepProof, String> {
    deep_ro_trace_from_agg_proof(proof, 0)
}

/// Bind DeepRoTrace out to the trace-height FriFoldY queried leaf at `query`.
pub fn bind_deep_ro_trace_to_fold_y(
    proof: &Proof<WqcStarkConfig>,
    deep_ro: &DeepRoTraceStepProof,
    fold_ys: &[FriFoldStepProof],
    query: usize,
) -> Result<(), String> {
    if !verify_deep_ro_trace_proof(deep_ro) {
        return Err("DeepRoTrace STARK verify failed".into());
    }
    let chal = replay_agg_fri_challenges(proof)?;
    let view = decode_pcs_view(proof)?;
    if query >= chal.query_indices.len() {
        return Err(format!("query {query} out of range"));
    }
    let (_ros, y_wits) = reconstruct_agg_query_ro(proof, &chal, &view, query)?;
    let y_off = fold_y_offset_for_query(proof, &chal, &view, query)?;

    let config = devnet_circle_config();
    let pcs = config.pcs();
    let degree = 1usize << proof.degree_bits;
    let init_trace_domain = <crate::plonky3_stark::config::Pcs as Pcs<
        Challenge,
        crate::plonky3_stark::config::Challenger,
    >>::natural_domain_for_degree(pcs, degree);
    let zeta_next = init_trace_domain
        .next_point(chal.zeta)
        .ok_or_else(|| "trace domain next_point unavailable".to_string())?;
    let log_blowup = chal.log_blowup;
    let trace_log_height = log2_size(init_trace_domain.size()) + log_blowup;
    let log_folded = trace_log_height - 1;
    let quotient_domain = init_trace_domain.create_disjoint_domain(degree);
    let quot_log_height = log2_size(quotient_domain.size()) + log_blowup;
    let log_global_max_height = view.fri_proof.commit_phase_commits.len() + log_blowup + 1;
    let query_index = chal.query_indices[query];
    let bits_reduced = log_global_max_height - trace_log_height;
    let queried_slot = (query_index >> bits_reduced) & 1;

    if deep_ro.alpha_limbs != challenge_to_limbs(chal.batch_alpha) {
        return Err("DeepRoTrace alpha != batch_alpha".into());
    }
    if deep_ro.zeta_limbs != challenge_to_limbs(chal.zeta) {
        return Err("DeepRoTrace zeta mismatch".into());
    }
    if deep_ro.zeta_next_limbs != challenge_to_limbs(zeta_next) {
        return Err("DeepRoTrace zeta_next mismatch".into());
    }
    if deep_ro.log_n as usize != trace_log_height - log_blowup {
        return Err("DeepRoTrace log_n mismatch".into());
    }

    let qp = &view.fri_proof.query_proofs[query];
    let input = decode_input_proof(&qp.input_proof)?;
    let opened = input.input_openings[0]
        .opened_values
        .first()
        .ok_or_else(|| "empty trace opening".to_string())?;
    if opened.len() != AGG_WIDTH || deep_ro.px.as_slice() != opened.as_slice() {
        return Err("DeepRoTrace px != trace opening".into());
    }
    let trace_local = &proof.opened_values.trace_local;
    let trace_next = proof
        .opened_values
        .trace_next
        .as_ref()
        .ok_or_else(|| "missing trace_next".to_string())?;
    if trace_local.len() != AGG_WIDTH || trace_next.len() != AGG_WIDTH {
        return Err("trace OOD width mismatch".into());
    }
    for i in 0..AGG_WIDTH {
        if deep_ro.pz_local_limbs[i] != challenge_to_limbs(trace_local[i]) {
            return Err(format!("DeepRoTrace pz_local[{i}] mismatch"));
        }
        if deep_ro.pz_next_limbs[i] != challenge_to_limbs(trace_next[i]) {
            return Err(format!("DeepRoTrace pz_next[{i}] mismatch"));
        }
    }

    let orig_idx = cfft_permute_index(query_index >> bits_reduced, trace_log_height);
    let p = standard_nth_point(trace_log_height, orig_idx);
    if deep_ro.sx != p.x || deep_ro.sy != p.y {
        return Err("DeepRoTrace circle point mismatch".into());
    }

    let mut heights = [trace_log_height, quot_log_height];
    heights.sort();
    let lambda_idx = heights
        .iter()
        .position(|&h| h == trace_log_height)
        .ok_or_else(|| "trace height missing".to_string())?;
    let lambda = view.lambdas[lambda_idx];
    if deep_ro.lambda_limbs != challenge_to_limbs(lambda) {
        return Err("DeepRoTrace lambda mismatch".into());
    }

    let y_wit = y_wits
        .iter()
        .find(|w| w.log_folded_height == log_folded)
        .ok_or_else(|| "missing fold_y witness for trace height".to_string())?;
    let fold = fold_ys
        .iter()
        .skip(y_off)
        .take(y_wits.len())
        .find(|f| f.log_folded_height as usize == log_folded && f.index as usize == y_wit.index)
        .ok_or_else(|| format!("missing FriFoldY for trace height on query {query}"))?;

    let out = limbs_to_challenge(deep_ro.out_limbs);
    let leaf = if queried_slot == 0 {
        limbs_to_challenge(fold.v0_limbs)
    } else {
        limbs_to_challenge(fold.v1_limbs)
    };
    if out != leaf {
        return Err("DeepRoTrace out != FriFoldY queried leaf".into());
    }
    if out
        != (if queried_slot == 0 {
            y_wit.v0
        } else {
            y_wit.v1
        })
    {
        return Err("DeepRoTrace out != reconstructed fold_y leaf".into());
    }
    Ok(())
}

/// Prove DeepRo + DeepRoTrace for all proven FRI queries.
pub fn deep_ro_bundle_from_agg_proof(
    proof: &Proof<WqcStarkConfig>,
) -> Result<AggDeepRoBundle, String> {
    let chal = replay_agg_fri_challenges(proof)?;
    if chal.query_indices.len() < AGG_FRI_PROVEN_QUERIES {
        return Err(format!(
            "FS query count {} < proven {}",
            chal.query_indices.len(),
            AGG_FRI_PROVEN_QUERIES
        ));
    }
    let mut deep_ros = Vec::with_capacity(AGG_FRI_PROVEN_QUERIES);
    let mut deep_ro_traces = Vec::with_capacity(AGG_FRI_PROVEN_QUERIES);
    for q in 0..AGG_FRI_PROVEN_QUERIES {
        deep_ros.push(
            deep_ro_quot_from_agg_proof(proof, q)
                .map_err(|e| format!("DeepRo quot query {q}: {e}"))?,
        );
        deep_ro_traces.push(
            deep_ro_trace_from_agg_proof(proof, q)
                .map_err(|e| format!("DeepRoTrace query {q}: {e}"))?,
        );
    }
    Ok(AggDeepRoBundle {
        deep_ros,
        deep_ro_traces,
    })
}

/// Bind all DeepRo / DeepRoTrace steps in a bundle to FriFoldY leaves.
pub fn bind_deep_ro_bundle_to_proof(
    proof: &Proof<WqcStarkConfig>,
    deep_ros: &[DeepRoStepProof],
    deep_ro_traces: &[DeepRoTraceStepProof],
    fold_ys: &[FriFoldStepProof],
) -> Result<(), String> {
    if deep_ros.len() != AGG_DEEP_RO_MAX {
        return Err(format!(
            "deep_ros len {}, want {AGG_DEEP_RO_MAX}",
            deep_ros.len()
        ));
    }
    if deep_ro_traces.len() != AGG_DEEP_RO_TRACE_MAX {
        return Err(format!(
            "deep_ro_traces len {}, want {AGG_DEEP_RO_TRACE_MAX}",
            deep_ro_traces.len()
        ));
    }
    for q in 0..AGG_FRI_PROVEN_QUERIES {
        bind_deep_ro_to_fold_y(proof, &deep_ros[q], fold_ys, q)
            .map_err(|e| format!("DeepRo bind query {q}: {e}"))?;
        bind_deep_ro_trace_to_fold_y(proof, &deep_ro_traces[q], fold_ys, q)
            .map_err(|e| format!("DeepRoTrace bind query {q}: {e}"))?;
    }
    Ok(())
}

/// Leaf DeepRo bundle: quot DeepRo + variable-width leaf DeepRoTrace.
#[derive(Debug, Clone)]
pub struct LeafDeepRoBundle {
    pub deep_ros: Vec<DeepRoStepProof>,
    pub deep_ro_traces: Vec<DeepRoLeafTraceStepProof>,
}

fn fold_y_offset_for_query_width(
    proof: &Proof<WqcStarkConfig>,
    chal: &AggFriChallenges,
    view: &CirclePcsProofView,
    query: usize,
    trace_width: usize,
) -> Result<usize, String> {
    let mut off = 0usize;
    for q in 0..query {
        let (_ros, y_wits) = reconstruct_query_ro(proof, chal, view, q, trace_width)?;
        off += y_wits.len();
    }
    Ok(off)
}

/// Prove DeepRo for leaf FRI quotient batch at `query` (W=3, any main-trace width).
pub fn deep_ro_quot_from_proof(
    proof: &Proof<WqcStarkConfig>,
    query: usize,
    trace_width: usize,
) -> Result<DeepRoStepProof, String> {
    let chal = replay_fri_challenges(proof, trace_width)?;
    let view = decode_pcs_view(proof)?;
    if query >= chal.query_indices.len() {
        return Err(format!("query {query} out of range"));
    }
    let qp = view
        .fri_proof
        .query_proofs
        .get(query)
        .ok_or_else(|| format!("missing FRI query {query}"))?;
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
    let query_index = chal.query_indices[query];
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

/// Prove DeepRoLeafTrace for leaf FRI trace batch at `query`.
pub fn deep_ro_leaf_trace_from_proof(
    proof: &Proof<WqcStarkConfig>,
    query: usize,
    trace_width: usize,
) -> Result<DeepRoLeafTraceStepProof, String> {
    let chal = replay_fri_challenges(proof, trace_width)?;
    let view = decode_pcs_view(proof)?;
    if query >= chal.query_indices.len() {
        return Err(format!("query {query} out of range"));
    }
    let qp = view
        .fri_proof
        .query_proofs
        .get(query)
        .ok_or_else(|| format!("missing FRI query {query}"))?;
    let input = decode_input_proof(&qp.input_proof)?;
    if input.input_openings.len() != 2 {
        return Err("expected 2 input openings".into());
    }

    let config = devnet_circle_config();
    let pcs = config.pcs();
    let degree = 1usize << proof.degree_bits;
    let init_trace_domain = <crate::plonky3_stark::config::Pcs as Pcs<
        Challenge,
        crate::plonky3_stark::config::Challenger,
    >>::natural_domain_for_degree(pcs, degree);
    let zeta = chal.zeta;
    let zeta_next = init_trace_domain
        .next_point(zeta)
        .ok_or_else(|| "trace domain next_point unavailable".to_string())?;
    let log_blowup = chal.log_blowup;
    let trace_log_height = log2_size(init_trace_domain.size()) + log_blowup;
    let quotient_domain = init_trace_domain.create_disjoint_domain(degree);
    let quot_log_height = log2_size(quotient_domain.size()) + log_blowup;
    let log_global_max_height = view.fri_proof.commit_phase_commits.len() + log_blowup + 1;
    let query_index = chal.query_indices[query];
    let bits_reduced = log_global_max_height - trace_log_height;
    let orig_idx = cfft_permute_index(query_index >> bits_reduced, trace_log_height);
    let p = standard_nth_point(trace_log_height, orig_idx);

    let opened = input.input_openings[0]
        .opened_values
        .first()
        .ok_or_else(|| "empty trace opening".to_string())?;
    if opened.len() != trace_width {
        return Err(format!(
            "trace opening width {}, want {trace_width}",
            opened.len()
        ));
    }
    let trace_local = &proof.opened_values.trace_local;
    let trace_next = proof
        .opened_values
        .trace_next
        .as_ref()
        .ok_or_else(|| "missing trace_next".to_string())?;
    if trace_local.len() != trace_width || trace_next.len() != trace_width {
        return Err("trace OOD width mismatch".into());
    }

    let mut heights = [trace_log_height, quot_log_height];
    heights.sort();
    let lambda_idx = heights
        .iter()
        .position(|&h| h == trace_log_height)
        .ok_or_else(|| "trace height missing".to_string())?;
    let lambda = *view
        .lambdas
        .get(lambda_idx)
        .ok_or_else(|| "missing lambda for trace height".to_string())?;

    let log_n = trace_log_height - log_blowup;
    generate_deep_ro_leaf_trace_proof(
        p.x,
        p.y,
        chal.batch_alpha,
        opened,
        trace_local,
        trace_next,
        lambda,
        log_n,
        zeta,
        zeta_next,
    )
}

/// Bind leaf DeepRo out to the quotient-height FriFoldY queried leaf at `query`.
pub fn bind_deep_ro_leaf_quot_to_fold_y(
    proof: &Proof<WqcStarkConfig>,
    deep_ro: &DeepRoStepProof,
    fold_ys: &[FriFoldStepProof],
    query: usize,
    trace_width: usize,
) -> Result<(), String> {
    if !verify_deep_ro_proof(deep_ro) {
        return Err("DeepRo STARK verify failed".into());
    }
    let chal = replay_fri_challenges(proof, trace_width)?;
    let view = decode_pcs_view(proof)?;
    if query >= chal.query_indices.len() {
        return Err(format!("query {query} out of range"));
    }
    let (_ros, y_wits) = reconstruct_query_ro(proof, &chal, &view, query, trace_width)?;
    let y_off = fold_y_offset_for_query_width(proof, &chal, &view, query, trace_width)?;

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
    let query_index = chal.query_indices[query];
    let bits_reduced = log_global_max_height - quot_log_height;
    let queried_slot = (query_index >> bits_reduced) & 1;

    if deep_ro.alpha_limbs != challenge_to_limbs(chal.batch_alpha) {
        return Err("DeepRo alpha != batch_alpha".into());
    }
    if deep_ro.zeta_limbs != challenge_to_limbs(chal.zeta) {
        return Err("DeepRo zeta mismatch".into());
    }
    if deep_ro.log_n as usize != quot_log_height - log_blowup {
        return Err("DeepRo log_n mismatch".into());
    }

    let qp = &view.fri_proof.query_proofs[query];
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

    let y_wit = y_wits
        .iter()
        .find(|w| w.log_folded_height == log_folded)
        .ok_or_else(|| "missing fold_y witness for quot height".to_string())?;
    let fold = fold_ys
        .iter()
        .skip(y_off)
        .take(y_wits.len())
        .find(|f| f.log_folded_height as usize == log_folded && f.index as usize == y_wit.index)
        .ok_or_else(|| format!("missing FriFoldY for quot height on query {query}"))?;

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

/// Bind leaf DeepRoTrace out to the trace-height FriFoldY queried leaf at `query`.
pub fn bind_deep_ro_leaf_trace_to_fold_y(
    proof: &Proof<WqcStarkConfig>,
    deep_ro: &DeepRoLeafTraceStepProof,
    fold_ys: &[FriFoldStepProof],
    query: usize,
    trace_width: usize,
) -> Result<(), String> {
    if !verify_deep_ro_leaf_trace_proof(deep_ro) {
        return Err("DeepRoLeafTrace STARK verify failed".into());
    }
    if deep_ro.width as usize != trace_width {
        return Err("DeepRoLeafTrace width mismatch".into());
    }
    let chal = replay_fri_challenges(proof, trace_width)?;
    let view = decode_pcs_view(proof)?;
    if query >= chal.query_indices.len() {
        return Err(format!("query {query} out of range"));
    }
    let (_ros, y_wits) = reconstruct_query_ro(proof, &chal, &view, query, trace_width)?;
    let y_off = fold_y_offset_for_query_width(proof, &chal, &view, query, trace_width)?;

    let config = devnet_circle_config();
    let pcs = config.pcs();
    let degree = 1usize << proof.degree_bits;
    let init_trace_domain = <crate::plonky3_stark::config::Pcs as Pcs<
        Challenge,
        crate::plonky3_stark::config::Challenger,
    >>::natural_domain_for_degree(pcs, degree);
    let zeta_next = init_trace_domain
        .next_point(chal.zeta)
        .ok_or_else(|| "trace domain next_point unavailable".to_string())?;
    let log_blowup = chal.log_blowup;
    let trace_log_height = log2_size(init_trace_domain.size()) + log_blowup;
    let log_folded = trace_log_height - 1;
    let quotient_domain = init_trace_domain.create_disjoint_domain(degree);
    let quot_log_height = log2_size(quotient_domain.size()) + log_blowup;
    let log_global_max_height = view.fri_proof.commit_phase_commits.len() + log_blowup + 1;
    let query_index = chal.query_indices[query];
    let bits_reduced = log_global_max_height - trace_log_height;
    let queried_slot = (query_index >> bits_reduced) & 1;

    if deep_ro.alpha_limbs != challenge_to_limbs(chal.batch_alpha) {
        return Err("DeepRoLeafTrace alpha != batch_alpha".into());
    }
    if deep_ro.zeta_limbs != challenge_to_limbs(chal.zeta) {
        return Err("DeepRoLeafTrace zeta mismatch".into());
    }
    if deep_ro.zeta_next_limbs != challenge_to_limbs(zeta_next) {
        return Err("DeepRoLeafTrace zeta_next mismatch".into());
    }
    if deep_ro.log_n as usize != trace_log_height - log_blowup {
        return Err("DeepRoLeafTrace log_n mismatch".into());
    }

    let qp = &view.fri_proof.query_proofs[query];
    let input = decode_input_proof(&qp.input_proof)?;
    let opened = input.input_openings[0]
        .opened_values
        .first()
        .ok_or_else(|| "empty trace opening".to_string())?;
    if opened.len() != trace_width || deep_ro.px.as_slice() != opened.as_slice() {
        return Err("DeepRoLeafTrace px != trace opening".into());
    }
    let trace_local = &proof.opened_values.trace_local;
    let trace_next = proof
        .opened_values
        .trace_next
        .as_ref()
        .ok_or_else(|| "missing trace_next".to_string())?;
    if trace_local.len() != trace_width || trace_next.len() != trace_width {
        return Err("trace OOD width mismatch".into());
    }
    for i in 0..trace_width {
        if deep_ro.pz_local_limbs[i] != challenge_to_limbs(trace_local[i]) {
            return Err(format!("DeepRoLeafTrace pz_local[{i}] mismatch"));
        }
        if deep_ro.pz_next_limbs[i] != challenge_to_limbs(trace_next[i]) {
            return Err(format!("DeepRoLeafTrace pz_next[{i}] mismatch"));
        }
    }

    let orig_idx = cfft_permute_index(query_index >> bits_reduced, trace_log_height);
    let p = standard_nth_point(trace_log_height, orig_idx);
    if deep_ro.sx != p.x || deep_ro.sy != p.y {
        return Err("DeepRoLeafTrace circle point mismatch".into());
    }

    let mut heights = [trace_log_height, quot_log_height];
    heights.sort();
    let lambda_idx = heights
        .iter()
        .position(|&h| h == trace_log_height)
        .ok_or_else(|| "trace height missing".to_string())?;
    let lambda = view.lambdas[lambda_idx];
    if deep_ro.lambda_limbs != challenge_to_limbs(lambda) {
        return Err("DeepRoLeafTrace lambda mismatch".into());
    }

    let y_wit = y_wits
        .iter()
        .find(|w| w.log_folded_height == log_folded)
        .ok_or_else(|| "missing fold_y witness for trace height".to_string())?;
    let fold = fold_ys
        .iter()
        .skip(y_off)
        .take(y_wits.len())
        .find(|f| f.log_folded_height as usize == log_folded && f.index as usize == y_wit.index)
        .ok_or_else(|| format!("missing FriFoldY for trace height on query {query}"))?;

    let out = limbs_to_challenge(deep_ro.out_limbs);
    let leaf = if queried_slot == 0 {
        limbs_to_challenge(fold.v0_limbs)
    } else {
        limbs_to_challenge(fold.v1_limbs)
    };
    if out != leaf {
        return Err("DeepRoLeafTrace out != FriFoldY queried leaf".into());
    }
    if out
        != (if queried_slot == 0 {
            y_wit.v0
        } else {
            y_wit.v1
        })
    {
        return Err("DeepRoLeafTrace out != reconstructed fold_y leaf".into());
    }
    Ok(())
}

/// Prove DeepRo + DeepRoLeafTrace for all proven FRI queries on a leaf proof.
pub fn deep_ro_bundle_from_leaf_proof(
    proof: &Proof<WqcStarkConfig>,
    trace_width: usize,
) -> Result<LeafDeepRoBundle, String> {
    let chal = replay_fri_challenges(proof, trace_width)?;
    if chal.query_indices.len() < LEAF_FRI_PROVEN_QUERIES {
        return Err(format!(
            "FS query count {} < proven {}",
            chal.query_indices.len(),
            LEAF_FRI_PROVEN_QUERIES
        ));
    }
    let mut deep_ros = Vec::with_capacity(LEAF_FRI_PROVEN_QUERIES);
    let mut deep_ro_traces = Vec::with_capacity(LEAF_FRI_PROVEN_QUERIES);
    for q in 0..LEAF_FRI_PROVEN_QUERIES {
        deep_ros.push(
            deep_ro_quot_from_proof(proof, q, trace_width)
                .map_err(|e| format!("DeepRo quot query {q}: {e}"))?,
        );
        deep_ro_traces.push(
            deep_ro_leaf_trace_from_proof(proof, q, trace_width)
                .map_err(|e| format!("DeepRoLeafTrace query {q}: {e}"))?,
        );
    }
    Ok(LeafDeepRoBundle {
        deep_ros,
        deep_ro_traces,
    })
}

/// Bind all leaf DeepRo / DeepRoLeafTrace steps to FriFoldY leaves.
pub fn bind_deep_ro_leaf_bundle_to_proof(
    proof: &Proof<WqcStarkConfig>,
    deep_ros: &[DeepRoStepProof],
    deep_ro_traces: &[DeepRoLeafTraceStepProof],
    fold_ys: &[FriFoldStepProof],
    trace_width: usize,
) -> Result<(), String> {
    if deep_ros.len() != LEAF_FRI_PROVEN_QUERIES {
        return Err(format!(
            "deep_ros len {}, want {LEAF_FRI_PROVEN_QUERIES}",
            deep_ros.len()
        ));
    }
    if deep_ro_traces.len() != LEAF_FRI_PROVEN_QUERIES {
        return Err(format!(
            "deep_ro_traces len {}, want {LEAF_FRI_PROVEN_QUERIES}",
            deep_ro_traces.len()
        ));
    }
    for q in 0..LEAF_FRI_PROVEN_QUERIES {
        bind_deep_ro_leaf_quot_to_fold_y(proof, &deep_ros[q], fold_ys, q, trace_width)
            .map_err(|e| format!("DeepRo bind query {q}: {e}"))?;
        bind_deep_ro_leaf_trace_to_fold_y(proof, &deep_ro_traces[q], fold_ys, q, trace_width)
            .map_err(|e| format!("DeepRoLeafTrace bind query {q}: {e}"))?;
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
        let deep = deep_ro_quot_from_agg_proof(&proof, 0).expect("deep");
        assert!(verify_deep_ro_proof(&deep));
        let bundle = fri_fold_bundle_from_agg_proof(&proof).expect("bundle");
        bind_deep_ro_to_fold_y(&proof, &deep, &bundle.fold_ys, 0).expect("bind");
    }

    #[test]
    fn deep_ro_trace_query0_binds_fold_y() {
        let ctx = AggregationContext {
            parent_task_id: "parent",
            compose_label: "L1:0",
            manifest_root_hash: "",
            left_child_hash: [41u8; CHILD_HASH_LEN],
            right_child_hash: [43u8; CHILD_HASH_LEN],
        };
        let transcript = generate_aggregation_proof(&ctx).expect("prove");
        let plonky3 = decode_agg_proof_owned(&transcript, &ctx).expect("decode");
        let proof: Proof<WqcStarkConfig> = postcard::from_bytes(&plonky3).expect("postcard");
        let deep = deep_ro_trace_from_agg_proof(&proof, 0).expect("deep");
        assert!(verify_deep_ro_trace_proof(&deep));
        let bundle = fri_fold_bundle_from_agg_proof(&proof).expect("bundle");
        bind_deep_ro_trace_to_fold_y(&proof, &deep, &bundle.fold_ys, 0).expect("bind");
    }

    #[test]
    fn deep_ro_bundle_all_queries_binds() {
        let ctx = AggregationContext {
            parent_task_id: "parent",
            compose_label: "L1:0",
            manifest_root_hash: "",
            left_child_hash: [51u8; CHILD_HASH_LEN],
            right_child_hash: [53u8; CHILD_HASH_LEN],
        };
        let transcript = generate_aggregation_proof(&ctx).expect("prove");
        let plonky3 = decode_agg_proof_owned(&transcript, &ctx).expect("decode");
        let proof: Proof<WqcStarkConfig> = postcard::from_bytes(&plonky3).expect("postcard");
        let deep_bundle = deep_ro_bundle_from_agg_proof(&proof).expect("deep bundle");
        assert_eq!(deep_bundle.deep_ros.len(), AGG_DEEP_RO_MAX);
        assert_eq!(deep_bundle.deep_ro_traces.len(), AGG_DEEP_RO_TRACE_MAX);
        let fri = fri_fold_bundle_from_agg_proof(&proof).expect("fri bundle");
        bind_deep_ro_bundle_to_proof(
            &proof,
            &deep_bundle.deep_ros,
            &deep_bundle.deep_ro_traces,
            &fri.fold_ys,
        )
        .expect("bind all");
        // Spot-check last query.
        let last = AGG_FRI_PROVEN_QUERIES - 1;
        bind_deep_ro_to_fold_y(&proof, &deep_bundle.deep_ros[last], &fri.fold_ys, last)
            .expect("last quot");
        bind_deep_ro_trace_to_fold_y(
            &proof,
            &deep_bundle.deep_ro_traces[last],
            &fri.fold_ys,
            last,
        )
        .expect("last trace");
    }
}

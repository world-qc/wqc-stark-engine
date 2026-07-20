//! Fiat-Shamir replay for Circle FRI (R3-M3b1 / M3e).
//!
//! Mirrors `p3-uni-stark::verify` → `CirclePcs::verify` → `p3_circle::verifier::verify`
//! far enough to recover folding betas and query indices. Does not verify openings.

use p3_challenger::{CanObserve, CanSampleBits, FieldChallenger, GrindingChallenger};
use p3_commit::Mmcs;
use p3_field::PrimeCharacteristicRing;
use p3_uni_stark::{Proof, StarkGenericConfig};
use serde::Deserialize;

use crate::plonky3_stark::aggregation_air::AGG_WIDTH;
use crate::plonky3_stark::config::{
    devnet_circle_config, Challenge, ChallengeMmcs, Val, ValMmcs, WqcStarkConfig,
};
use crate::plonky3_stark::recursion::merkle_keccak::{hash_val_leaf, merkle_root_from_path};

use p3_circle::{CircleFriProof, CircleInputProof};

type AggInputProof = CircleInputProof<Val, Challenge, ValMmcs, ChallengeMmcs>;
type AggFriProof = CircleFriProof<Challenge, ChallengeMmcs, Val, AggInputProof>;

/// Postcard mirror of private `CirclePcsProof`.
#[derive(Deserialize)]
#[serde(bound = "")]
pub(crate) struct CirclePcsProofView {
    pub(crate) first_layer_commitment: <ChallengeMmcs as Mmcs<Challenge>>::Commitment,
    pub(crate) lambdas: Vec<Challenge>,
    pub(crate) fri_proof: AggFriProof,
}

/// Fiat-Shamir challenges recovered from a non-ZK Circle uni-STARK proof.
#[derive(Debug, Clone)]
pub struct AggFriChallenges {
    /// Constraint-folding challenge (uni-STARK α before quotient commit observe).
    pub constraint_alpha: Challenge,
    /// OOD evaluation point (projective-line coordinate).
    pub zeta: Challenge,
    /// PCS batch-combination challenge.
    pub batch_alpha: Challenge,
    /// First-layer `fold_y` challenge.
    pub bivariate_beta: Challenge,
    pub betas: Vec<Challenge>,
    pub query_indices: Vec<usize>,
    /// `log_blowup + sum(log_arities)` used inside FRI (before extra circle bit).
    pub fri_log_max_height: usize,
    pub log_blowup: usize,
    pub extra_query_index_bits: usize,
}

pub(crate) fn decode_pcs_view(proof: &Proof<WqcStarkConfig>) -> Result<CirclePcsProofView, String> {
    let bytes = postcard::to_allocvec(&proof.opening_proof)
        .map_err(|e| format!("postcard encode opening_proof: {e}"))?;
    postcard::from_bytes(&bytes).map_err(|e| format!("postcard decode CirclePcsProof: {e}"))
}

fn recover_same_height_query_index(
    trace_row: &[Val],
    siblings: &[[u8; 32]],
    expected_root: &[u8; 32],
) -> Result<usize, String> {
    let leaf = hash_val_leaf(trace_row);
    let candidate_count = 1usize
        .checked_shl(siblings.len() as u32)
        .ok_or_else(|| format!("trace Merkle depth too large: {}", siblings.len()))?;
    let mut match_index = None;
    for index in 0..candidate_count {
        let root = merkle_root_from_path(leaf, siblings, index);
        if &root == expected_root && match_index.replace(index).is_some() {
            return Err("multiple trace indices match same-height Merkle path".into());
        }
    }
    match_index.ok_or_else(|| "no trace index matches same-height Merkle path".into())
}

/// Replay FS for any non-ZK Circle proof with the given main-trace width (0 public values).
pub fn replay_fri_challenges(
    proof: &Proof<WqcStarkConfig>,
    expected_width: usize,
) -> Result<AggFriChallenges, String> {
    if expected_width == 0 {
        return Err("expected_width must be > 0".into());
    }
    if proof.commitments.random.is_some() || proof.opened_values.random.is_some() {
        return Err("unexpected ZK randomization on proof".into());
    }
    if proof.opened_values.preprocessed_local.is_some()
        || proof.opened_values.preprocessed_next.is_some()
    {
        return Err("unexpected preprocessed openings on proof".into());
    }
    let trace_next = proof
        .opened_values
        .trace_next
        .as_ref()
        .ok_or_else(|| "proof missing trace_next openings".to_string())?;
    if proof.opened_values.trace_local.len() != expected_width || trace_next.len() != expected_width
    {
        return Err(format!(
            "opened trace width mismatch: local={}, next={}, want {expected_width}",
            proof.opened_values.trace_local.len(),
            trace_next.len()
        ));
    }

    let config = devnet_circle_config();
    let log_blowup = config.pcs().fri_params.log_blowup;
    let degree_bits = proof.degree_bits;
    let base_degree_bits = degree_bits;
    let preprocessed_width = 0usize;

    let mut challenger = config.initialise_challenger();
    challenger.observe(Val::from_usize(degree_bits));
    challenger.observe(Val::from_usize(base_degree_bits));
    challenger.observe(Val::from_usize(preprocessed_width));
    challenger.observe(proof.commitments.trace.clone());
    let constraint_alpha: Challenge = challenger.sample_algebra_element();
    challenger.observe(proof.commitments.quotient_chunks.clone());
    let zeta: Challenge = challenger.sample_algebra_element();

    challenger.observe_algebra_slice(&proof.opened_values.trace_local);
    challenger.observe_algebra_slice(trace_next);
    for chunk in &proof.opened_values.quotient_chunks {
        challenger.observe_algebra_slice(chunk);
    }

    let batch_alpha: Challenge = challenger.sample_algebra_element();
    let view = decode_pcs_view(proof)?;
    challenger.observe(view.first_layer_commitment.clone());
    let bivariate_beta: Challenge = challenger.sample_algebra_element();

    let fri = &view.fri_proof;
    if fri.commit_pow_witnesses.len() != fri.commit_phase_commits.len() {
        return Err("FRI commit PoW witness count mismatch".into());
    }
    let fri_params = &config.pcs().fri_params;
    let mut betas = Vec::with_capacity(fri.commit_phase_commits.len());
    for (comm, witness) in fri
        .commit_phase_commits
        .iter()
        .zip(&fri.commit_pow_witnesses)
    {
        challenger.observe(comm.clone());
        if !challenger.check_witness(fri_params.commit_proof_of_work_bits, *witness) {
            return Err("invalid FRI commit PoW witness".into());
        }
        betas.push(challenger.sample_algebra_element());
    }
    challenger.observe_algebra_element(fri.final_poly);
    if !challenger.check_witness(fri_params.query_proof_of_work_bits, fri.pow_witness) {
        return Err("invalid FRI query PoW witness".into());
    }

    let log_arities: Vec<usize> = fri
        .query_proofs
        .first()
        .map(|qp| {
            qp.commit_phase_openings
                .iter()
                .map(|o| o.log_arity as usize)
                .collect()
        })
        .unwrap_or_default();
    if log_arities
        .iter()
        .any(|&a| a == 0 || a > fri_params.max_log_arity)
    {
        return Err("invalid FRI log_arity schedule".into());
    }
    let fri_log_max_height: usize = log_arities.iter().sum::<usize>() + log_blowup;
    let extra_query_index_bits = 1usize;
    let num_index_bits = fri_log_max_height + extra_query_index_bits;

    if fri.query_proofs.len() != fri_params.num_queries {
        return Err(format!(
            "FRI query count mismatch: got {}, want {}",
            fri.query_proofs.len(),
            fri_params.num_queries
        ));
    }
    let mut query_indices = Vec::with_capacity(fri_params.num_queries);
    for _ in 0..fri_params.num_queries {
        query_indices.push(challenger.sample_bits(num_index_bits));
    }

    let trace_root = proof
        .commitments
        .trace
        .roots()
        .first()
        .copied()
        .ok_or_else(|| "empty trace commitment roots".to_string())?;
    let trace_log_height = proof.degree_bits + log_blowup;
    let same_height_trace_queries = trace_log_height == num_index_bits;
    if same_height_trace_queries {
        for (q, query_index) in query_indices.iter_mut().enumerate() {
            let qp = fri
                .query_proofs
                .get(q)
                .ok_or_else(|| format!("missing FRI query proof {q}"))?;
            let input: super::fri_ro::CircleInputProofView =
                super::fri_ro::decode_input_proof(&qp.input_proof)?;
            let trace_row = input
                .input_openings
                .first()
                .and_then(|opening| opening.opened_values.first())
                .ok_or_else(|| format!("q{q}: missing trace opening row"))?;
            if trace_row.len() != expected_width {
                return Err(format!(
                    "q{q}: trace opening width {}, want {expected_width}",
                    trace_row.len()
                ));
            }
            let siblings = &input
                .input_openings
                .first()
                .ok_or_else(|| format!("q{q}: missing trace opening proof"))?
                .opening_proof;
            let replay_root =
                merkle_root_from_path(hash_val_leaf(trace_row), siblings, *query_index);
            if replay_root != trace_root {
                let recovered = recover_same_height_query_index(trace_row, siblings, &trace_root)
                    .map_err(|e| {
                    format!("q{q}: same-height trace index recovery failed: {e}")
                })?;
                *query_index = recovered;
            }
        }
    }

    Ok(AggFriChallenges {
        constraint_alpha,
        zeta,
        batch_alpha,
        bivariate_beta,
        betas,
        query_indices,
        fri_log_max_height,
        log_blowup,
        extra_query_index_bits,
    })
}

/// Replay the AggregationAir FS transcript through FRI query sampling.
pub fn replay_agg_fri_challenges(
    proof: &Proof<WqcStarkConfig>,
) -> Result<AggFriChallenges, String> {
    replay_fri_challenges(proof, AGG_WIDTH)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::aggregation::CHILD_HASH_LEN;
    use crate::plonky3_stark::aggregation::AggregationContext;
    use crate::plonky3_stark::generate_aggregation_proof;
    use crate::plonky3_stark::transcript_v4::decode_agg_proof_owned;

    #[test]
    fn replay_agg_fri_shape() {
        let ctx = AggregationContext {
            parent_task_id: "parent",
            compose_label: "L1:0",
            manifest_root_hash: "",
            left_child_hash: [1u8; CHILD_HASH_LEN],
            right_child_hash: [2u8; CHILD_HASH_LEN],
        };
        let transcript = generate_aggregation_proof(&ctx).expect("prove");
        let plonky3 = decode_agg_proof_owned(&transcript, &ctx).expect("decode");
        let proof: Proof<WqcStarkConfig> = postcard::from_bytes(&plonky3).expect("postcard");
        let chal = replay_agg_fri_challenges(&proof).expect("replay");
        assert_eq!(chal.betas.len(), 2);
        assert_eq!(chal.query_indices.len(), 40);
        assert_eq!(chal.log_blowup, 1);
        assert_eq!(chal.fri_log_max_height, 3);
        assert_eq!(chal.extra_query_index_bits, 1);
    }
}

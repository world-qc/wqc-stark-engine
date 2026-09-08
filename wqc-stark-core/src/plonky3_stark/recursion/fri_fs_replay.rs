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
    devnet_circle_config_with_queries, Challenge, ChallengeMmcs, Val, ValMmcs, WqcStarkConfig,
    DEVNET_FRI_NUM_QUERIES,
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

/// Outer FRI query count embedded in a Circle uni-STARK proof (`1..=DEVNET_FRI_NUM_QUERIES`).
pub fn fri_queries_from_proof(proof: &Proof<WqcStarkConfig>) -> Result<usize, String> {
    let view = decode_pcs_view(proof)?;
    let n = view.fri_proof.query_proofs.len();
    if n == 0 || n > DEVNET_FRI_NUM_QUERIES {
        return Err(format!(
            "FRI query count {n} out of range 1..={DEVNET_FRI_NUM_QUERIES}"
        ));
    }
    Ok(n)
}

/// Circle config whose `num_queries` matches the proof's FRI query vector.
pub fn circle_config_matching_proof(
    proof: &Proof<WqcStarkConfig>,
) -> Result<WqcStarkConfig, String> {
    Ok(devnet_circle_config_with_queries(fri_queries_from_proof(
        proof,
    )?))
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

    let config = circle_config_matching_proof(proof)?;
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

/// Replay the RecursiveAggregationAir FS transcript through FRI query sampling.
pub fn replay_rec_agg_fri_challenges(
    proof: &Proof<WqcStarkConfig>,
) -> Result<AggFriChallenges, String> {
    use crate::plonky3_stark::recursion::air::REC_AGG_WIDTH;
    replay_fri_challenges(proof, REC_AGG_WIDTH)
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
            security_level: "",
        };
        let transcript = generate_aggregation_proof(&ctx).expect("prove");
        let plonky3 = decode_agg_proof_owned(&transcript, &ctx).expect("decode");
        let proof: Proof<WqcStarkConfig> = postcard::from_bytes(&plonky3).expect("postcard");
        let chal = replay_agg_fri_challenges(&proof).expect("replay");
        assert_eq!(chal.query_indices.len(), 40);
        assert_eq!(chal.betas.len(), 2);
        assert_eq!(chal.log_blowup, 1);
        assert_eq!(chal.fri_log_max_height, 3);
        assert_eq!(chal.extra_query_index_bits, 1);
    }

    #[test]
    fn replay_agg_fri_shape_low_security() {
        let ctx = AggregationContext {
            parent_task_id: "parent",
            compose_label: "L1:0",
            manifest_root_hash: "",
            left_child_hash: [1u8; CHILD_HASH_LEN],
            right_child_hash: [2u8; CHILD_HASH_LEN],
            security_level: "low",
        };
        let transcript = generate_aggregation_proof(&ctx).expect("prove");
        let plonky3 = decode_agg_proof_owned(&transcript, &ctx).expect("decode");
        let proof: Proof<WqcStarkConfig> = postcard::from_bytes(&plonky3).expect("postcard");
        assert_eq!(fri_queries_from_proof(&proof).expect("n"), 8);
        let chal = replay_agg_fri_challenges(&proof).expect("replay");
        assert_eq!(chal.query_indices.len(), 8);
    }

    #[test]
    fn emit_fri_fs_chain_golden() {
        use p3_field::BasedVectorSpace;
        use p3_field::PrimeField32;
        use sha3::{Digest, Keccak256};
        use std::path::PathBuf;

        let ctx = AggregationContext {
            parent_task_id: "parent",
            compose_label: "L1:0",
            manifest_root_hash: "",
            left_child_hash: [1u8; CHILD_HASH_LEN],
            right_child_hash: [2u8; CHILD_HASH_LEN],
            security_level: "ultra",
        };
        let transcript = generate_aggregation_proof(&ctx).expect("prove");
        let plonky3 = decode_agg_proof_owned(&transcript, &ctx).expect("decode");
        let proof: Proof<WqcStarkConfig> = postcard::from_bytes(&plonky3).expect("postcard");
        let chal = replay_agg_fri_challenges(&proof).expect("replay");
        assert_eq!(chal.query_indices.len(), 40);
        assert_eq!(chal.betas.len(), 2);

        let degree_bits = proof.degree_bits;
        assert_eq!(degree_bits, 2);
        let trace_root = *proof.commitments.trace.roots().first().expect("trace root");
        let quot_root = *proof
            .commitments
            .quotient_chunks
            .roots()
            .first()
            .expect("quot root");
        let view = decode_pcs_view(&proof).expect("pcs");
        let first_layer = *view
            .first_layer_commitment
            .roots()
            .first()
            .expect("first layer");
        let fri0 = *view.fri_proof.commit_phase_commits[0]
            .roots()
            .first()
            .expect("fri0");
        let fri1 = *view.fri_proof.commit_phase_commits[1]
            .roots()
            .first()
            .expect("fri1");

        fn push_u32(out: &mut Vec<u8>, v: u32) {
            out.extend_from_slice(&v.to_le_bytes());
        }
        fn push_challenge(out: &mut Vec<u8>, c: &Challenge) {
            for limb in BasedVectorSpace::<Val>::as_basis_coefficients_slice(c) {
                push_u32(out, limb.as_canonical_u32());
            }
        }
        fn keccak(msg: &[u8]) -> [u8; 32] {
            Keccak256::digest(msg).into()
        }

        let mut prefix = Vec::new();
        push_u32(&mut prefix, degree_bits as u32);
        push_u32(&mut prefix, degree_bits as u32);
        push_u32(&mut prefix, 0);
        prefix.extend_from_slice(&trace_root);
        assert_eq!(prefix.len(), 44);
        let d1 = keccak(&prefix);

        let mut m2 = Vec::new();
        m2.extend_from_slice(&d1);
        m2.extend_from_slice(&quot_root);
        assert_eq!(m2.len(), 64);
        let d2 = keccak(&m2);

        let mut m3 = Vec::new();
        m3.extend_from_slice(&d2);
        for c in &proof.opened_values.trace_local {
            push_challenge(&mut m3, c);
        }
        for c in proof.opened_values.trace_next.as_ref().unwrap() {
            push_challenge(&mut m3, c);
        }
        assert_eq!(proof.opened_values.quotient_chunks.len(), 1);
        for c in &proof.opened_values.quotient_chunks[0] {
            push_challenge(&mut m3, c);
        }
        assert_eq!(m3.len(), 1652, "openings absorb");
        let d3 = keccak(&m3);

        let mut m4 = Vec::new();
        m4.extend_from_slice(&d3);
        m4.extend_from_slice(&first_layer);
        let d4 = keccak(&m4);

        let mut m5 = Vec::new();
        m5.extend_from_slice(&d4);
        m5.extend_from_slice(&fri0);
        let d5 = keccak(&m5);

        let mut m6 = Vec::new();
        m6.extend_from_slice(&d5);
        m6.extend_from_slice(&fri1);
        let chain = keccak(&m6);

        let final_poly = view.fri_proof.final_poly;
        let pow = view.fri_proof.pow_witness.as_canonical_u32();
        let mut m7 = Vec::new();
        m7.extend_from_slice(&chain);
        push_challenge(&mut m7, &final_poly);
        push_u32(&mut m7, pow);
        assert_eq!(m7.len(), 48);
        let d7: [u8; 32] = keccak(&m7);
        let mut off = 0usize;
        let sample_bits = |d: &[u8; 32], off: &mut usize, bits: usize| -> usize {
            let mut b = [0u8; 4];
            for i in 0..4 {
                b[i] = d[31 - *off - i];
            }
            *off += 4;
            let u = u32::from_le_bytes(b) as usize;
            u & ((1 << bits) - 1)
        };
        assert_eq!(sample_bits(&d7, &mut off, 8), 0, "pow");
        // N=40: PoW + 40 queries with Di'=Keccak(Di) when the 32 B LIFO is exhausted.
        let mut dig = d7;
        for (i, &want) in chal.query_indices.iter().enumerate() {
            if off == 32 {
                dig = keccak(&dig);
                off = 0;
            }
            assert_eq!(sample_bits(&dig, &mut off, 4), want, "qi[{i}]");
        }

        let mut trace_local = Vec::new();
        for c in &proof.opened_values.trace_local {
            let limbs: Vec<u32> = BasedVectorSpace::<Val>::as_basis_coefficients_slice(c)
                .iter()
                .map(|x: &Val| x.as_canonical_u32())
                .collect();
            trace_local.push(limbs);
        }
        let mut trace_next = Vec::new();
        for c in proof.opened_values.trace_next.as_ref().unwrap() {
            let limbs: Vec<u32> = BasedVectorSpace::<Val>::as_basis_coefficients_slice(c)
                .iter()
                .map(|x: &Val| x.as_canonical_u32())
                .collect();
            trace_next.push(limbs);
        }
        let mut quot_open = Vec::new();
        for c in &proof.opened_values.quotient_chunks[0] {
            let limbs: Vec<u32> = BasedVectorSpace::<Val>::as_basis_coefficients_slice(c)
                .iter()
                .map(|x: &Val| x.as_canonical_u32())
                .collect();
            quot_open.push(limbs);
        }
        let fp: Vec<u32> = BasedVectorSpace::<Val>::as_basis_coefficients_slice(&final_poly)
            .iter()
            .map(|x: &Val| x.as_canonical_u32())
            .collect();

        let golden = serde_json::json!({
            "statement": "thick_fri_fs_observe_v0",
            "gate": "e5b-3d",
            "source": "AggregationAir HashChallenger 6-flush ChainDigest + query PoW sample_bits",
            "measured_at": "2026-09-08",
            "approx_r1cs": 2546237,
            "agg_width": 66,
            "degree_bits": degree_bits,
            "flush_lens": [44, 64, 1652, 64, 64, 64],
            "trace_root": trace_root.to_vec(),
            "quot_root": quot_root.to_vec(),
            "trace_local": trace_local,
            "trace_next": trace_next,
            "quot_open": quot_open,
            "first_layer_root": first_layer.to_vec(),
            "fri_commit0": fri0.to_vec(),
            "fri_commit1": fri1.to_vec(),
            "chain_digest": chain.to_vec(),
            "final_poly": fp,
            "pow_witness": pow,
            "query_index": &chal.query_indices[..40],
            "notes": "Absorb-only mid-state (no in-circuit α/ζ/β sample); N=40 Agg ultra; N=40 / ≡ verify_root_proof deferred"
        });

        let out = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../fixtures/e5b/wrap_fri_fs_observe_golden.json");
        std::fs::write(&out, serde_json::to_string_pretty(&golden).unwrap()).expect("write");
        let wrap = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../wqc-snark-wrap/fixtures/e5b3/wrap_fri_fs_observe_golden.json");
        if let Some(parent) = wrap.parent() {
            if parent.exists() {
                let _ = std::fs::write(&wrap, serde_json::to_string_pretty(&golden).unwrap());
            }
        }
    }

    #[test]
    fn lock_fri_fs_observe_golden() {
        use sha3::{Digest, Keccak256};

        let golden_path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../fixtures/e5b/wrap_fri_fs_observe_golden.json"
        );
        let raw = std::fs::read_to_string(golden_path).expect("wrap_fri_fs_observe_golden.json");
        let v: serde_json::Value = serde_json::from_str(&raw).expect("golden json");
        assert_eq!(v["statement"].as_str().unwrap(), "thick_fri_fs_observe_v0");
        assert_eq!(v["approx_r1cs"].as_u64().unwrap(), 2546237);
        assert_eq!(v["degree_bits"].as_u64().unwrap(), 2);
        assert_eq!(v["agg_width"].as_u64().unwrap(), 66);

        fn bytes(v: &serde_json::Value, key: &str) -> Vec<u8> {
            v[key]
                .as_array()
                .unwrap()
                .iter()
                .map(|x| x.as_u64().unwrap() as u8)
                .collect()
        }
        fn ef3_rows(v: &serde_json::Value, key: &str) -> Vec<[u32; 3]> {
            v[key]
                .as_array()
                .unwrap()
                .iter()
                .map(|row| {
                    let a = row.as_array().unwrap();
                    [
                        a[0].as_u64().unwrap() as u32,
                        a[1].as_u64().unwrap() as u32,
                        a[2].as_u64().unwrap() as u32,
                    ]
                })
                .collect()
        }
        fn push_u32(out: &mut Vec<u8>, x: u32) {
            out.extend_from_slice(&x.to_le_bytes());
        }
        fn keccak(msg: &[u8]) -> [u8; 32] {
            Keccak256::digest(msg).into()
        }

        let degree_bits = v["degree_bits"].as_u64().unwrap() as u32;
        let trace_root = bytes(&v, "trace_root");
        let quot_root = bytes(&v, "quot_root");
        let first_layer = bytes(&v, "first_layer_root");
        let fri0 = bytes(&v, "fri_commit0");
        let fri1 = bytes(&v, "fri_commit1");
        let want_chain = bytes(&v, "chain_digest");
        let trace_local = ef3_rows(&v, "trace_local");
        let trace_next = ef3_rows(&v, "trace_next");
        let quot_open = ef3_rows(&v, "quot_open");
        assert_eq!(trace_local.len(), 66);
        assert_eq!(trace_next.len(), 66);
        assert_eq!(quot_open.len(), 3);

        let mut m1 = Vec::new();
        push_u32(&mut m1, degree_bits);
        push_u32(&mut m1, degree_bits);
        push_u32(&mut m1, 0);
        m1.extend_from_slice(&trace_root);
        assert_eq!(m1.len(), 44);
        let d1 = keccak(&m1);

        let mut m2 = Vec::new();
        m2.extend_from_slice(&d1);
        m2.extend_from_slice(&quot_root);
        let d2 = keccak(&m2);

        let mut m3 = Vec::new();
        m3.extend_from_slice(&d2);
        for row in trace_local
            .iter()
            .chain(trace_next.iter())
            .chain(quot_open.iter())
        {
            for limb in row {
                push_u32(&mut m3, *limb);
            }
        }
        assert_eq!(m3.len(), 1652);
        let d3 = keccak(&m3);
        let d4 = keccak(&[d3.as_slice(), first_layer.as_slice()].concat());
        let d5 = keccak(&[d4.as_slice(), fri0.as_slice()].concat());
        let chain = keccak(&[d5.as_slice(), fri1.as_slice()].concat());
        assert_eq!(chain.as_slice(), want_chain.as_slice());

        let final_poly: Vec<u32> = v["final_poly"]
            .as_array()
            .unwrap()
            .iter()
            .map(|x| x.as_u64().unwrap() as u32)
            .collect();
        let pow = v["pow_witness"].as_u64().unwrap() as u32;
        let mut m7 = Vec::new();
        m7.extend_from_slice(&chain);
        for limb in &final_poly {
            push_u32(&mut m7, *limb);
        }
        push_u32(&mut m7, pow);
        let d7: [u8; 32] = keccak(&m7);
        let sample_bits = |d: &[u8; 32], off: &mut usize, bits: usize| -> u32 {
            let mut b = [0u8; 4];
            for i in 0..4 {
                b[i] = d[31 - *off - i];
            }
            *off += 4;
            u32::from_le_bytes(b) & ((1u32 << bits) - 1)
        };
        let mut off = 0usize;
        assert_eq!(sample_bits(&d7, &mut off, 8), 0);
        let want_qi = v["query_index"].as_array().unwrap();
        assert_eq!(want_qi.len(), 40);
        let mut dig = d7;
        for item in want_qi {
            if off == 32 {
                dig = keccak(&dig);
                off = 0;
            }
            assert_eq!(
                sample_bits(&dig, &mut off, 4) as u64,
                item.as_u64().unwrap()
            );
        }
    }

    #[test]
    fn lock_fri_fs_chal_golden() {
        use p3_field::{BasedVectorSpace, PrimeField32};
        use sha3::{Digest, Keccak256};

        let golden_path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../fixtures/e5b/wrap_fri_fs_chal_golden.json"
        );
        let raw = std::fs::read_to_string(golden_path).expect("wrap_fri_fs_chal_golden.json");
        let v: serde_json::Value = serde_json::from_str(&raw).expect("golden json");
        assert_eq!(v["statement"].as_str().unwrap(), "thick_fri_fs_chal_v0");
        assert_eq!(v["approx_r1cs"].as_u64().unwrap(), 3645473);

        fn bytes(v: &serde_json::Value, key: &str) -> Vec<u8> {
            v[key]
                .as_array()
                .unwrap()
                .iter()
                .map(|x| x.as_u64().unwrap() as u8)
                .collect()
        }
        fn ef3(v: &serde_json::Value, key: &str) -> [u32; 3] {
            let a = v[key].as_array().unwrap();
            [
                a[0].as_u64().unwrap() as u32,
                a[1].as_u64().unwrap() as u32,
                a[2].as_u64().unwrap() as u32,
            ]
        }
        fn ef3_rows(v: &serde_json::Value, key: &str) -> Vec<[u32; 3]> {
            v[key]
                .as_array()
                .unwrap()
                .iter()
                .map(|row| {
                    let a = row.as_array().unwrap();
                    [
                        a[0].as_u64().unwrap() as u32,
                        a[1].as_u64().unwrap() as u32,
                        a[2].as_u64().unwrap() as u32,
                    ]
                })
                .collect()
        }
        fn push_u32(out: &mut Vec<u8>, x: u32) {
            out.extend_from_slice(&x.to_le_bytes());
        }
        fn keccak(msg: &[u8]) -> [u8; 32] {
            Keccak256::digest(msg).into()
        }
        fn sample_base_m31(d: &[u8; 32], off: &mut usize) -> u32 {
            let mut b = [0u8; 4];
            for i in 0..4 {
                b[i] = d[31 - *off - i];
            }
            *off += 4;
            let u = u32::from_le_bytes(b) & 0x7fff_ffff;
            assert_ne!(u, 0x7fff_ffff, "M31 reject");
            u
        }
        fn sample_algebra(d: &[u8; 32]) -> [u32; 3] {
            let mut off = 0usize;
            [
                sample_base_m31(d, &mut off),
                sample_base_m31(d, &mut off),
                sample_base_m31(d, &mut off),
            ]
        }

        let degree_bits = v["degree_bits"].as_u64().unwrap() as u32;
        let mut m1 = Vec::new();
        push_u32(&mut m1, degree_bits);
        push_u32(&mut m1, degree_bits);
        push_u32(&mut m1, 0);
        m1.extend_from_slice(&bytes(&v, "trace_root"));
        let d1 = keccak(&m1);
        assert_eq!(sample_algebra(&d1), ef3(&v, "constraint_alpha"));

        let d2 = keccak(&[d1.as_slice(), bytes(&v, "quot_root").as_slice()].concat());
        assert_eq!(sample_algebra(&d2), ef3(&v, "zeta"));

        let mut m3 = Vec::new();
        m3.extend_from_slice(&d2);
        for row in ef3_rows(&v, "trace_local")
            .iter()
            .chain(ef3_rows(&v, "trace_next").iter())
            .chain(ef3_rows(&v, "quot_open").iter())
        {
            for limb in row {
                push_u32(&mut m3, *limb);
            }
        }
        let d3 = keccak(&m3);
        assert_eq!(sample_algebra(&d3), ef3(&v, "batch_alpha"));

        let d4 = keccak(&[d3.as_slice(), bytes(&v, "first_layer_root").as_slice()].concat());
        assert_eq!(sample_algebra(&d4), ef3(&v, "bivariate_beta"));
        let d5 = keccak(&[d4.as_slice(), bytes(&v, "fri_commit0").as_slice()].concat());
        let d6 = keccak(&[d5.as_slice(), bytes(&v, "fri_commit1").as_slice()].concat());
        let betas = v["betas"].as_array().unwrap();
        let b0 = [
            betas[0][0].as_u64().unwrap() as u32,
            betas[0][1].as_u64().unwrap() as u32,
            betas[0][2].as_u64().unwrap() as u32,
        ];
        let b1 = [
            betas[1][0].as_u64().unwrap() as u32,
            betas[1][1].as_u64().unwrap() as u32,
            betas[1][2].as_u64().unwrap() as u32,
        ];
        assert_eq!(sample_algebra(&d5), b0);
        assert_eq!(sample_algebra(&d6), b1);
        assert_eq!(d6.as_slice(), bytes(&v, "chain_digest").as_slice());

        // Live Agg replay must match golden challenge limbs.
        let ctx = AggregationContext {
            parent_task_id: "parent",
            compose_label: "L1:0",
            manifest_root_hash: "",
            left_child_hash: [1u8; CHILD_HASH_LEN],
            right_child_hash: [2u8; CHILD_HASH_LEN],
            security_level: "ultra",
        };
        let transcript = generate_aggregation_proof(&ctx).expect("prove");
        let plonky3 = decode_agg_proof_owned(&transcript, &ctx).expect("decode");
        let proof: Proof<WqcStarkConfig> = postcard::from_bytes(&plonky3).expect("postcard");
        let chal = replay_agg_fri_challenges(&proof).expect("replay");
        let limbs = |c: &Challenge| -> [u32; 3] {
            let s = BasedVectorSpace::<Val>::as_basis_coefficients_slice(c);
            [
                s[0].as_canonical_u32(),
                s[1].as_canonical_u32(),
                s[2].as_canonical_u32(),
            ]
        };
        assert_eq!(limbs(&chal.constraint_alpha), ef3(&v, "constraint_alpha"));
        assert_eq!(limbs(&chal.zeta), ef3(&v, "zeta"));
        assert_eq!(limbs(&chal.batch_alpha), ef3(&v, "batch_alpha"));
        assert_eq!(limbs(&chal.bivariate_beta), ef3(&v, "bivariate_beta"));
        assert_eq!(limbs(&chal.betas[0]), b0);
        assert_eq!(limbs(&chal.betas[1]), b1);
    }

    #[test]
    fn lock_fri_fs_chal_rej_golden() {
        use sha3::{Digest, Keccak256};

        let golden_path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../fixtures/e5b/wrap_fri_fs_chal_rej_golden.json"
        );
        let raw = std::fs::read_to_string(golden_path).expect("wrap_fri_fs_chal_rej_golden.json");
        let v: serde_json::Value = serde_json::from_str(&raw).expect("golden json");
        assert_eq!(v["statement"].as_str().unwrap(), "thick_fri_fs_chal_rej_v0");
        assert_eq!(v["approx_r1cs"].as_u64().unwrap(), 315024);
        assert_eq!(v["reflushes"].as_u64().unwrap(), 1);
        assert_eq!(v["max_algebra_reflush"].as_u64().unwrap(), 3);
        assert_eq!(v["max_algebra_draws"].as_u64().unwrap(), 32);

        fn bytes(v: &serde_json::Value, key: &str) -> [u8; 32] {
            let a = v[key].as_array().unwrap();
            let mut out = [0u8; 32];
            for i in 0..32 {
                out[i] = a[i].as_u64().unwrap() as u8;
            }
            out
        }
        fn ef3(v: &serde_json::Value, key: &str) -> [u32; 3] {
            let a = v[key].as_array().unwrap();
            [
                a[0].as_u64().unwrap() as u32,
                a[1].as_u64().unwrap() as u32,
                a[2].as_u64().unwrap() as u32,
            ]
        }
        const ORDER: u32 = 0x7fff_ffff;
        fn sample_base(d: &[u8; 32], off: &mut usize) -> Option<u32> {
            let mut b = [0u8; 4];
            for i in 0..4 {
                b[i] = d[31 - *off - i];
            }
            *off += 4;
            let u = u32::from_le_bytes(b) & ORDER;
            if u == ORDER {
                None
            } else {
                Some(u)
            }
        }
        fn sample_full(d0: [u8; 32]) -> ([u32; 3], usize, usize) {
            let mut dig = d0;
            let mut off = 0usize;
            let mut reflushes = 0usize;
            let mut out = [0u32; 3];
            let mut limb = 0usize;
            let mut draws = 0usize;
            while limb < 3 {
                if off == 32 {
                    assert!(reflushes < 1);
                    dig = Keccak256::digest(dig).into();
                    reflushes += 1;
                    off = 0;
                }
                draws += 1;
                if let Some(v) = sample_base(&dig, &mut off) {
                    out[limb] = v;
                    limb += 1;
                }
            }
            (out, reflushes, draws)
        }

        let d_intra = bytes(&v, "digest_intra");
        let (intra, r0, draws0) = sample_full(d_intra);
        assert_eq!(r0, 0);
        assert_eq!(draws0, 4);
        assert_eq!(intra, ef3(&v, "chal_intra"));

        let d_re = bytes(&v, "digest_reflush");
        // All LIFO limbs reject.
        let mut off = 0usize;
        for _ in 0..8 {
            assert!(sample_base(&d_re, &mut off).is_none());
        }
        let (re, r1, draws1) = sample_full(d_re);
        assert_eq!(r1, 1);
        assert_eq!(draws1, v["reflush_draws"].as_u64().unwrap() as usize);
        assert_eq!(re, ef3(&v, "chal_reflush"));
        let d1: [u8; 32] = Keccak256::digest(d_re).into();
        let (from_d1, r_d1, _) = sample_full(d1);
        assert_eq!(r_d1, 0);
        assert_eq!(from_d1, re);
    }

    #[test]
    fn emit_fri_fs_auth_golden() {
        use p3_commit::{Pcs, PolynomialSpace};
        use p3_field::PrimeField32;
        use std::path::PathBuf;

        use crate::plonky3_stark::recursion::fri_ro::decode_input_proof;

        let ctx = AggregationContext {
            parent_task_id: "parent",
            compose_label: "L1:0",
            manifest_root_hash: "",
            left_child_hash: [1u8; CHILD_HASH_LEN],
            right_child_hash: [2u8; CHILD_HASH_LEN],
            security_level: "ultra",
        };
        let transcript = generate_aggregation_proof(&ctx).expect("prove");
        let plonky3 = decode_agg_proof_owned(&transcript, &ctx).expect("decode");
        let proof: Proof<WqcStarkConfig> = postcard::from_bytes(&plonky3).expect("postcard");
        let chal = replay_agg_fri_challenges(&proof).expect("replay");
        assert_eq!(proof.degree_bits, 2);
        assert_eq!(chal.query_indices.len(), 40);
        assert_eq!(
            proof.opened_values.quotient_chunks.len(),
            1,
            "Agg single quot chunk"
        );

        let view = decode_pcs_view(&proof).expect("pcs");
        let config = circle_config_matching_proof(&proof).expect("cfg");
        let pcs = config.pcs();
        let degree = 1usize << proof.degree_bits;
        let init_trace_domain = <crate::plonky3_stark::config::Pcs as Pcs<
            Challenge,
            crate::plonky3_stark::config::Challenger,
        >>::natural_domain_for_degree(pcs, degree);
        let log_blowup = chal.log_blowup;
        let log_global_max_height = view.fri_proof.commit_phase_commits.len() + log_blowup + 1;
        let trace_height = init_trace_domain.size() << log_blowup;
        assert!(trace_height.is_power_of_two());
        let trace_log_height = trace_height.trailing_zeros() as usize;
        let y_shift = log_global_max_height - trace_log_height;
        assert_eq!(y_shift, 1, "Agg low ValMmcs index shift");

        // Single quot chunk: disjoint domain then split (matches fri_mmcs_bind).
        let num_quot = proof.opened_values.quotient_chunks.len();
        assert_eq!(num_quot, 1);
        let log_num_quot = num_quot.trailing_zeros() as usize;
        let quot_parent =
            init_trace_domain.create_disjoint_domain(1usize << (proof.degree_bits + log_num_quot));
        let quot_chunk_domains = quot_parent.split_domains(num_quot);
        let quot_h = quot_chunk_domains[0].size() << log_blowup;
        assert!(quot_h.is_power_of_two());
        let quot_log_height = quot_h.trailing_zeros() as usize;
        let quot_shift = log_global_max_height - quot_log_height;
        assert_eq!(quot_h, 16);
        assert_eq!(quot_log_height, 4);
        assert_eq!(quot_shift, 0, "Agg low quot ValMmcs index shift");
        assert_ne!(quot_shift, y_shift);

        let trace_root = *proof.commitments.trace.roots().first().expect("trace root");
        let quot_root = *proof
            .commitments
            .quotient_chunks
            .roots()
            .first()
            .expect("quot root");
        let mut val_mmcs = Vec::with_capacity(40);
        let mut quot_mmcs = Vec::with_capacity(40);
        let mut trace_index = Vec::with_capacity(40);
        let mut quot_index = Vec::with_capacity(40);
        for q in 0..40 {
            let qi = chal.query_indices[q];
            let input =
                decode_input_proof(&view.fri_proof.query_proofs[q].input_proof).expect("input");
            let trace_open = &input.input_openings[0];
            let quot_open = &input.input_openings[1];
            let row = &trace_open.opened_values[0];
            assert_eq!(row.len(), AGG_WIDTH);
            let quot_row = &quot_open.opened_values[0];
            assert_eq!(quot_row.len(), 3, "EF_DIM");

            let t_idx = qi >> y_shift;
            let q_idx = qi >> quot_shift;
            assert_eq!(q_idx, qi);
            assert_eq!(
                merkle_root_from_path(hash_val_leaf(row), &trace_open.opening_proof, t_idx),
                trace_root,
                "q{q} trace ValMmcs root"
            );
            assert_eq!(
                merkle_root_from_path(hash_val_leaf(quot_row), &quot_open.opening_proof, q_idx),
                quot_root,
                "q{q} quot ValMmcs root"
            );
            assert_eq!(trace_open.opening_proof.len(), trace_log_height);
            assert_eq!(quot_open.opening_proof.len(), quot_log_height);

            trace_index.push(t_idx as u32);
            quot_index.push(q_idx as u32);
            val_mmcs.push(serde_json::json!({
                "leaf_row": row.iter().map(|x| x.as_canonical_u32()).collect::<Vec<_>>(),
                "siblings": trace_open.opening_proof.iter().map(|s| s.to_vec()).collect::<Vec<_>>(),
                "index": t_idx as u32,
            }));
            quot_mmcs.push(serde_json::json!({
                "leaf_row": quot_row.iter().map(|x| x.as_canonical_u32()).collect::<Vec<_>>(),
                "siblings": quot_open.opening_proof.iter().map(|s| s.to_vec()).collect::<Vec<_>>(),
                "index": q_idx as u32,
            }));
        }

        use p3_field::{BasedVectorSpace, PrimeCharacteristicRing};

        use crate::plonky3_stark::recursion::deep_ro_native::{
            deep_ro_trace_witness, deep_ro_w3_witness, ef_from_projective_line,
        };
        use crate::plonky3_stark::recursion::fri_fold_native::{
            cfft_permute_index, challenge_to_limbs, fold_x_row, fold_x_twiddle_inv, fold_y_row,
            fold_y_twiddle_inv, standard_nth_point,
        };
        use crate::plonky3_stark::recursion::fri_mmcs_bind::fri_chal_mmcs_bundle_from_agg_proof;
        use crate::plonky3_stark::recursion::fri_ro::reconstruct_query_ro;
        use crate::plonky3_stark::recursion::merkle_keccak::compress_digests;

        let fl_root = *view
            .first_layer_commitment
            .roots()
            .first()
            .expect("first layer");
        let fri0 = *view.fri_proof.commit_phase_commits[0]
            .roots()
            .first()
            .expect("fri0");
        let fri1 = *view.fri_proof.commit_phase_commits[1]
            .roots()
            .first()
            .expect("fri1");
        let chal_bundle = fri_chal_mmcs_bundle_from_agg_proof(&proof).expect("chal mmcs");
        assert_eq!(chal_bundle.len(), chal.query_indices.len());
        assert_eq!(view.lambdas.len(), 2, "trace+quot heights");

        let zeta_next = init_trace_domain.next_point(chal.zeta).expect("zeta_next");
        let (at_x, at_y) = ef_from_projective_line(chal.zeta);
        let (atn_x, atn_y) = ef_from_projective_line(zeta_next);
        let limbs_u32 = |c: Challenge| -> Vec<u32> {
            challenge_to_limbs(c)
                .iter()
                .map(|x| x.as_canonical_u32())
                .collect()
        };
        let val_u32 = |v: Val| v.as_canonical_u32();

        let flatten_u32 = |evals: &[Challenge; 2]| -> Vec<u32> {
            let mut out = Vec::with_capacity(6);
            for e in evals {
                for limb in challenge_to_limbs(*e) {
                    out.push(limb.as_canonical_u32());
                }
            }
            out
        };

        let mut chal_first_layer = Vec::with_capacity(40);
        let mut chal_commit = Vec::with_capacity(40);
        let mut deep_ro = Vec::with_capacity(40);
        let trace_next = proof.opened_values.trace_next.as_ref().expect("trace_next");
        let mut px_trace = [Val::ZERO; AGG_WIDTH];
        let mut pz_local = [Challenge::ZERO; AGG_WIDTH];
        let mut pz_next = [Challenge::ZERO; AGG_WIDTH];
        pz_local[..AGG_WIDTH].copy_from_slice(&proof.opened_values.trace_local[..AGG_WIDTH]);
        pz_next[..AGG_WIDTH].copy_from_slice(&trace_next[..AGG_WIDTH]);
        let mut px_quot = [Val::ZERO; 3];
        let mut pz_quot = [Challenge::ZERO; 3];
        pz_quot.copy_from_slice(&proof.opened_values.quotient_chunks[0][..3]);

        for (q, bundle) in chal_bundle.iter().enumerate() {
            let qi = chal.query_indices[q];
            let fl = &bundle.first_layer;
            // Note: FriChalBatchPathProof.index is post-walk cap (0); use QI>>1.
            let fl_idx = qi >> 1;
            assert_eq!(fl.leaf_rows.len(), 2);
            assert_eq!(fl.siblings.len(), 3, "log2(8)");
            let tall: Vec<u32> = fl.leaf_rows[0]
                .iter()
                .map(|x| x.as_canonical_u32())
                .collect();
            let short: Vec<u32> = fl.leaf_rows[1]
                .iter()
                .map(|x| x.as_canonical_u32())
                .collect();
            assert_eq!(tall.len(), 6);
            assert_eq!(short.len(), 6);
            // Agg 8+4: sib0 then inject short, then sib1, sib2.
            let mut dig = hash_val_leaf(&fl.leaf_rows[0]);
            let mut idx = fl_idx;
            dig = if idx.is_multiple_of(2) {
                compress_digests(dig, fl.siblings[0])
            } else {
                compress_digests(fl.siblings[0], dig)
            };
            idx /= 2;
            dig = compress_digests(dig, hash_val_leaf(&fl.leaf_rows[1]));
            for s in &fl.siblings[1..] {
                dig = if idx.is_multiple_of(2) {
                    compress_digests(dig, *s)
                } else {
                    compress_digests(*s, dig)
                };
                idx /= 2;
            }
            assert_eq!(dig, fl_root, "q{q} first-layer root");

            let (_, fold_ys) =
                reconstruct_query_ro(&proof, &chal, &view, q, AGG_WIDTH).expect("ro");
            assert_eq!(fold_ys.len(), 2, "short+tall");
            let short_flat = flatten_u32(&[fold_ys[0].v0, fold_ys[0].v1]);
            let tall_flat = flatten_u32(&[fold_ys[1].v0, fold_ys[1].v1]);
            assert_eq!(short_flat, short, "q{q} Flatten(fold_y short)==FL short");
            assert_eq!(tall_flat, tall, "q{q} Flatten(fold_y tall)==FL tall");

            let input =
                decode_input_proof(&view.fri_proof.query_proofs[q].input_proof).expect("input");
            px_trace[..AGG_WIDTH]
                .copy_from_slice(&input.input_openings[0].opened_values[0][..AGG_WIDTH]);
            px_quot.copy_from_slice(&input.input_openings[1].opened_values[0][..3]);
            let orig_t = cfft_permute_index(qi >> y_shift, trace_log_height);
            let pt = standard_nth_point(trace_log_height, orig_t);
            let orig_q = cfft_permute_index(qi >> quot_shift, quot_log_height);
            let pq = standard_nth_point(quot_log_height, orig_q);
            let tw = deep_ro_trace_witness(
                chal.batch_alpha,
                pt.x,
                pt.y,
                chal.zeta,
                zeta_next,
                &px_trace,
                &pz_local,
                &pz_next,
                view.lambdas[0],
                proof.degree_bits,
            );
            let qw = deep_ro_w3_witness(
                chal.batch_alpha,
                pq.x,
                pq.y,
                chal.zeta,
                px_quot,
                pz_quot,
                view.lambdas[1],
                proof.degree_bits + 1, // quot orig_size = log_h - blowup = 3
            );
            let pair_short = (qi >> y_shift) & 1;
            let pair_tall = (qi >> quot_shift) & 1;
            let lc_short = if pair_short == 0 {
                fold_ys[0].v0
            } else {
                fold_ys[0].v1
            };
            let lc_tall = if pair_tall == 0 {
                fold_ys[1].v0
            } else {
                fold_ys[1].v1
            };
            assert_eq!(tw.out, lc_short, "q{q} DeepRo trace == FL λc short");
            assert_eq!(qw.out, lc_tall, "q{q} DeepRo quot == FL λc tall");
            assert_eq!(tw.at_x, at_x);
            assert_eq!(tw.at_y, at_y);
            assert_eq!(qw.at_x, at_x);
            assert_eq!(qw.at_y, at_y);

            let t_inv_short = fold_y_twiddle_inv(fold_ys[0].index, fold_ys[0].log_folded_height);
            let t_inv_tall = fold_y_twiddle_inv(fold_ys[1].index, fold_ys[1].log_folded_height);
            let out_short = fold_y_row(
                fold_ys[0].index,
                fold_ys[0].log_folded_height,
                chal.bivariate_beta,
                fold_ys[0].v0,
                fold_ys[0].v1,
            );
            let out_tall = fold_y_row(
                fold_ys[1].index,
                fold_ys[1].log_folded_height,
                chal.bivariate_beta,
                fold_ys[1].v0,
                fold_ys[1].v1,
            );

            let qp = &view.fri_proof.query_proofs[q];
            let openings = &qp.commit_phase_openings;
            assert_eq!(openings.len(), 2);
            let mut index = qi >> chal.extra_query_index_bits;
            let mut log_current = openings.len() + chal.log_blowup;
            let mut folded_eval = Challenge::ZERO;
            let (reduced, _) =
                reconstruct_query_ro(&proof, &chal, &view, q, AGG_WIDTH).expect("ro");
            let mut ro_iter = reduced.iter().peekable();
            let commit_roots = [fri0, fri1];
            let mut rounds = Vec::with_capacity(2);
            let mut fold_xs = Vec::with_capacity(2);
            for (round, opening) in openings.iter().enumerate() {
                if let Some(&&(lh, ro)) = ro_iter.peek() {
                    if lh == log_current {
                        folded_eval += ro;
                        ro_iter.next();
                    }
                }
                let sibling = opening.sibling_values[0];
                let index_in_group = index % 2;
                let mut evals = [Challenge::ZERO; 2];
                evals[index_in_group] = folded_eval;
                evals[index_in_group ^ 1] = sibling;
                let log_folded = log_current - 1;
                index >>= 1;
                let row = flatten_u32(&evals);
                let row_m31: Vec<_> = evals
                    .iter()
                    .flat_map(|e| {
                        BasedVectorSpace::<Val>::as_basis_coefficients_slice(e)
                            .iter()
                            .copied()
                    })
                    .collect();
                assert_eq!(
                    merkle_root_from_path(hash_val_leaf(&row_m31), &opening.opening_proof, index),
                    commit_roots[round],
                    "q{q} commit{round} root"
                );
                assert_eq!(bundle.commit_indices[round] as usize, index);
                rounds.push(serde_json::json!({
                    "leaf_row": row,
                    "siblings": opening.opening_proof.iter().map(|s| s.to_vec()).collect::<Vec<_>>(),
                    "index": index as u32,
                }));
                let out = fold_x_row(index, log_folded, chal.betas[round], evals[0], evals[1]);
                let t_inv = fold_x_twiddle_inv(index, log_folded);
                fold_xs.push(serde_json::json!({
                    "index": index as u32,
                    "log_h": log_folded as u32,
                    "t_inv": t_inv.as_canonical_u32(),
                    "out": limbs_u32(out),
                }));
                folded_eval = out;
                log_current = log_folded;
            }
            assert_eq!(
                folded_eval, view.fri_proof.final_poly,
                "q{q} fold_x → FinalPoly"
            );
            assert!(ro_iter.next().is_none(), "q{q} unused RO");
            chal_commit.push(serde_json::json!(rounds));

            deep_ro.push(serde_json::json!({
                "sx_trace": val_u32(pt.x),
                "sy_trace": val_u32(pt.y),
                "sx_quot": val_u32(pq.x),
                "sy_quot": val_u32(pq.y),
                "v_n_trace": val_u32(tw.v_n),
                "v_n_quot": val_u32(qw.v_n),
                "out_pre_trace0": limbs_u32(tw.deep0.out_pre),
                "out_pre_trace1": limbs_u32(tw.deep1.out_pre),
                "out_pre_quot": limbs_u32(qw.out_pre),
                "deep_out_trace": limbs_u32(tw.out),
                "deep_out_quot": limbs_u32(qw.out),
                "fold_y_short": {
                    "index": fold_ys[0].index as u32,
                    "log_h": fold_ys[0].log_folded_height as u32,
                    "t_inv": t_inv_short.as_canonical_u32(),
                    "out": limbs_u32(out_short),
                },
                "fold_y_tall": {
                    "index": fold_ys[1].index as u32,
                    "log_h": fold_ys[1].log_folded_height as u32,
                    "t_inv": t_inv_tall.as_canonical_u32(),
                    "out": limbs_u32(out_tall),
                },
                "fold_x": fold_xs,
            }));

            chal_first_layer.push(serde_json::json!({
                "tall_row": tall,
                "short_row": short,
                "siblings": fl.siblings.iter().map(|s| s.to_vec()).collect::<Vec<_>>(),
                "index": fl_idx as u32,
                "inject_after_step": 0,
            }));
        }

        let golden = serde_json::json!({
            "statement": "thick_fri_fs_auth_v0",
            "gate": "e5b-3d",
            "source": "AggregationAir ultra-security Trace/Quot ValMmcs + Chal Mmcs + DeepRo→FL Flatten/fold_y + commit-phase fold_x→FinalPoly",
            "measured_at": "2026-09-08",
            "approx_r1cs": 125250450,
            "agg_width": AGG_WIDTH,
            "quot_width": 3,
            "chal_leaf_width": 6,
            "path_depth": trace_log_height,
            "quot_path_depth": quot_log_height,
            "quot_shift": quot_shift,
            "chal_fl_shift": 1,
            "chal_fl_depth": 3,
            "chal_fl_heights": [8, 4],
            "chal_commit_shifts": [2, 3],
            "chal_commit_depths": [2, 1],
            "n": 40,
            "degree_bits": proof.degree_bits,
            "trace_root": trace_root.to_vec(),
            "quot_root": quot_root.to_vec(),
            "first_layer_root": fl_root.to_vec(),
            "fri_commit0": fri0.to_vec(),
            "fri_commit1": fri1.to_vec(),
            "query_index": &chal.query_indices[..40],
            "trace_index": trace_index,
            "quot_index": quot_index,
            "val_mmcs": val_mmcs,
            "quot_mmcs": quot_mmcs,
            "chal_first_layer": chal_first_layer,
            "chal_commit": chal_commit,
            "zeta_next": limbs_u32(zeta_next),
            "lambdas": [limbs_u32(view.lambdas[0]), limbs_u32(view.lambdas[1])],
            "at_x": limbs_u32(at_x),
            "at_y": limbs_u32(at_y),
            "atn_x": limbs_u32(atn_x),
            "atn_y": limbs_u32(atn_y),
            "deep_ro": deep_ro,
            "notes": "FriFsChal N=40 + Trace/Quot ValMmcs + Chal FL/FRI-commit + DeepRo Flatten/fold_y + commit fold_x→FinalPoly; folded into thick_unified_v0; N=40/≡verify_root_proof deferred"
        });

        let out = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../fixtures/e5b/wrap_fri_fs_auth_golden.json");
        std::fs::write(&out, serde_json::to_string_pretty(&golden).unwrap()).expect("write");
        let wrap = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../wqc-snark-wrap/fixtures/e5b3/wrap_fri_fs_auth_golden.json");
        if let Some(parent) = wrap.parent() {
            if parent.exists() {
                let _ = std::fs::write(&wrap, serde_json::to_string_pretty(&golden).unwrap());
            }
        }
    }

    #[test]
    fn lock_fri_fs_auth_golden() {
        use p3_commit::{Pcs, PolynomialSpace};
        use p3_field::PrimeField32;

        use crate::plonky3_stark::recursion::fri_ro::decode_input_proof;

        let golden_path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../fixtures/e5b/wrap_fri_fs_auth_golden.json"
        );
        let raw = std::fs::read_to_string(golden_path).expect("wrap_fri_fs_auth_golden.json");
        let v: serde_json::Value = serde_json::from_str(&raw).expect("golden json");
        assert_eq!(v["statement"].as_str().unwrap(), "thick_fri_fs_auth_v0");
        assert_eq!(v["agg_width"].as_u64().unwrap(), AGG_WIDTH as u64);
        assert_eq!(v["quot_width"].as_u64().unwrap(), 3);
        assert_eq!(v["n"].as_u64().unwrap(), 40);
        assert_eq!(v["path_depth"].as_u64().unwrap(), 3);
        assert_eq!(v["quot_path_depth"].as_u64().unwrap(), 4);
        assert_eq!(v["quot_shift"].as_u64().unwrap(), 0);
        assert_eq!(v["chal_leaf_width"].as_u64().unwrap(), 6);
        assert_eq!(v["chal_fl_shift"].as_u64().unwrap(), 1);
        assert_eq!(v["chal_fl_depth"].as_u64().unwrap(), 3);
        assert_eq!(v["chal_first_layer"].as_array().unwrap().len(), 40);
        assert_eq!(v["chal_commit"].as_array().unwrap().len(), 40);
        assert_eq!(v["deep_ro"].as_array().unwrap().len(), 40);
        assert_eq!(v["lambdas"].as_array().unwrap().len(), 2);
        assert_eq!(v["zeta_next"].as_array().unwrap().len(), 3);
        for q in 0..40 {
            let fx = v["deep_ro"][q]["fold_x"].as_array().expect("fold_x");
            assert_eq!(fx.len(), 2);
            assert_eq!(fx[0]["log_h"].as_u64().unwrap(), 2);
            assert_eq!(fx[1]["log_h"].as_u64().unwrap(), 1);
        }
        // approx_r1cs locked after Go remmeasure (N=40 + fold_x chain)
        assert_eq!(v["approx_r1cs"].as_u64().unwrap(), 125250450);

        let ctx = AggregationContext {
            parent_task_id: "parent",
            compose_label: "L1:0",
            manifest_root_hash: "",
            left_child_hash: [1u8; CHILD_HASH_LEN],
            right_child_hash: [2u8; CHILD_HASH_LEN],
            security_level: "ultra",
        };
        let transcript = generate_aggregation_proof(&ctx).expect("prove");
        let plonky3 = decode_agg_proof_owned(&transcript, &ctx).expect("decode");
        let proof: Proof<WqcStarkConfig> = postcard::from_bytes(&plonky3).expect("postcard");
        let chal = replay_agg_fri_challenges(&proof).expect("replay");
        let view = decode_pcs_view(&proof).expect("pcs");
        let config = circle_config_matching_proof(&proof).expect("cfg");
        let pcs = config.pcs();
        let degree = 1usize << proof.degree_bits;
        let init_trace_domain = <crate::plonky3_stark::config::Pcs as Pcs<
            Challenge,
            crate::plonky3_stark::config::Challenger,
        >>::natural_domain_for_degree(pcs, degree);
        let log_blowup = chal.log_blowup;
        let log_global_max_height = view.fri_proof.commit_phase_commits.len() + log_blowup + 1;
        let trace_height = init_trace_domain.size() << log_blowup;
        let trace_log_height = trace_height.trailing_zeros() as usize;
        let y_shift = log_global_max_height - trace_log_height;
        let num_quot = proof.opened_values.quotient_chunks.len();
        let log_num_quot = num_quot.trailing_zeros() as usize;
        let quot_parent =
            init_trace_domain.create_disjoint_domain(1usize << (proof.degree_bits + log_num_quot));
        let quot_chunk_domains = quot_parent.split_domains(num_quot);
        let quot_h = quot_chunk_domains[0].size() << log_blowup;
        let quot_log_height = quot_h.trailing_zeros() as usize;
        let quot_shift = log_global_max_height - quot_log_height;
        let trace_root = *proof.commitments.trace.roots().first().expect("trace root");
        let quot_root = *proof
            .commitments
            .quotient_chunks
            .roots()
            .first()
            .expect("quot root");

        let bytes = |key: &str| -> Vec<u8> {
            v[key]
                .as_array()
                .unwrap()
                .iter()
                .map(|x| x.as_u64().unwrap() as u8)
                .collect()
        };
        assert_eq!(bytes("trace_root").as_slice(), trace_root.as_slice());
        assert_eq!(bytes("quot_root").as_slice(), quot_root.as_slice());

        let qis = v["query_index"].as_array().unwrap();
        let tis = v["trace_index"].as_array().unwrap();
        let qis_mmcs = v["quot_index"].as_array().unwrap();
        let paths = v["val_mmcs"].as_array().unwrap();
        let quot_paths = v["quot_mmcs"].as_array().unwrap();
        assert_eq!(paths.len(), 40);
        assert_eq!(quot_paths.len(), 40);
        for q in 0..40 {
            let qi = chal.query_indices[q];
            assert_eq!(qis[q].as_u64().unwrap() as usize, qi);
            let t_idx = qi >> y_shift;
            let q_idx = qi >> quot_shift;
            assert_eq!(tis[q].as_u64().unwrap() as usize, t_idx);
            assert_eq!(qis_mmcs[q].as_u64().unwrap() as usize, q_idx);
            let input =
                decode_input_proof(&view.fri_proof.query_proofs[q].input_proof).expect("input");
            let row = &input.input_openings[0].opened_values[0];
            let quot_row = &input.input_openings[1].opened_values[0];
            let leaf_row: Vec<u32> = paths[q]["leaf_row"]
                .as_array()
                .unwrap()
                .iter()
                .map(|x| x.as_u64().unwrap() as u32)
                .collect();
            assert_eq!(leaf_row.len(), AGG_WIDTH);
            for (a, b) in leaf_row.iter().zip(row.iter()) {
                assert_eq!(*a, b.as_canonical_u32());
            }
            let q_leaf: Vec<u32> = quot_paths[q]["leaf_row"]
                .as_array()
                .unwrap()
                .iter()
                .map(|x| x.as_u64().unwrap() as u32)
                .collect();
            assert_eq!(q_leaf.len(), 3);
            for (a, b) in q_leaf.iter().zip(quot_row.iter()) {
                assert_eq!(*a, b.as_canonical_u32());
            }
            let check_sibs = |json: &serde_json::Value, proof: &[[u8; 32]], depth: usize| {
                let sibs = json["siblings"].as_array().unwrap();
                assert_eq!(sibs.len(), depth);
                assert_eq!(sibs.len(), proof.len());
                for (i, sib) in sibs.iter().enumerate() {
                    let b: Vec<u8> = sib
                        .as_array()
                        .unwrap()
                        .iter()
                        .map(|x| x.as_u64().unwrap() as u8)
                        .collect();
                    assert_eq!(b.as_slice(), proof[i].as_slice());
                }
            };
            check_sibs(
                &paths[q],
                &input.input_openings[0].opening_proof,
                trace_log_height,
            );
            check_sibs(
                &quot_paths[q],
                &input.input_openings[1].opening_proof,
                quot_log_height,
            );
            assert_eq!(
                merkle_root_from_path(
                    hash_val_leaf(row),
                    &input.input_openings[0].opening_proof,
                    t_idx
                ),
                trace_root
            );
            assert_eq!(
                merkle_root_from_path(
                    hash_val_leaf(quot_row),
                    &input.input_openings[1].opening_proof,
                    q_idx
                ),
                quot_root
            );
        }
    }

    #[test]
    fn emit_recagg_fs_mmcs_golden() {
        use p3_commit::{Pcs, PolynomialSpace};
        use p3_field::PrimeField32;
        use std::path::PathBuf;

        use crate::plonky3_stark::recursion::air::{REC_AGG_WIDTH, REC_KIND_LEAF};
        use crate::plonky3_stark::recursion::child_binding::STARK_DIGEST_LEN;
        use crate::plonky3_stark::recursion::context::RecursiveAggregationContext;
        use crate::plonky3_stark::recursion::fri_ro::decode_input_proof;
        use crate::plonky3_stark::recursion::prove::generate_recursive_aggregation_proof;
        use crate::plonky3_stark::recursion::transcript_v6::decode_rec_agg_proof_owned_v6;

        let ctx = RecursiveAggregationContext {
            parent_task_id: "parent",
            compose_label: "root",
            manifest_root_hash: "m",
            left_child_hash: [1u8; CHILD_HASH_LEN],
            right_child_hash: [2u8; CHILD_HASH_LEN],
            left_stark_digest: [3u8; STARK_DIGEST_LEN],
            right_stark_digest: [4u8; STARK_DIGEST_LEN],
            left_kind: REC_KIND_LEAF,
            right_kind: REC_KIND_LEAF,
            left_agg_cert: None,
            right_agg_cert: None,
            left_leaf_bundle: None,
            right_leaf_bundle: None,
            security_level: "low",
        };
        let transcript = generate_recursive_aggregation_proof(&ctx).expect("prove");
        let plonky3 = decode_rec_agg_proof_owned_v6(&transcript, &ctx).expect("decode v6");
        let proof: Proof<WqcStarkConfig> = postcard::from_bytes(&plonky3).expect("postcard");
        let chal = replay_rec_agg_fri_challenges(&proof).expect("replay");
        assert_eq!(proof.degree_bits, 2);
        assert_eq!(chal.query_indices.len(), 8);
        assert_eq!(chal.log_blowup, 1);
        assert_eq!(chal.extra_query_index_bits, 1);

        let view = decode_pcs_view(&proof).expect("pcs");
        let config = circle_config_matching_proof(&proof).expect("cfg");
        let pcs = config.pcs();
        let degree = 1usize << proof.degree_bits;
        let init_trace_domain = <crate::plonky3_stark::config::Pcs as Pcs<
            Challenge,
            crate::plonky3_stark::config::Challenger,
        >>::natural_domain_for_degree(pcs, degree);
        let log_blowup = chal.log_blowup;
        let log_global_max_height = view.fri_proof.commit_phase_commits.len() + log_blowup + 1;
        let trace_height = init_trace_domain.size() << log_blowup;
        assert!(trace_height.is_power_of_two());
        let trace_log_height = trace_height.trailing_zeros() as usize;
        let y_shift = log_global_max_height - trace_log_height;
        let num_index_bits = chal.fri_log_max_height + chal.extra_query_index_bits;

        let qi = chal.query_indices[0];
        let input = decode_input_proof(&view.fri_proof.query_proofs[0].input_proof).expect("input");
        let trace_open = &input.input_openings[0];
        let row = &trace_open.opened_values[0];
        assert_eq!(row.len(), REC_AGG_WIDTH);
        let t_idx = qi >> y_shift;
        let trace_root = *proof.commitments.trace.roots().first().expect("trace root");
        assert_eq!(
            merkle_root_from_path(hash_val_leaf(row), &trace_open.opening_proof, t_idx),
            trace_root,
            "q0 RecAgg Trace ValMmcs root"
        );
        assert_eq!(trace_open.opening_proof.len(), trace_log_height);
        assert!(
            trace_log_height <= 4,
            "wrap ThickMmcsMaxDepth=4; got {trace_log_height}"
        );

        let golden = serde_json::json!({
            "statement": "thick_recagg_fs_mmcs_v0",
            "gate": "e5b-3d",
            "source": "RecursiveAggregationAir low-security Trace ValMmcs query 0 (FS-bound)",
            "measured_at": "2026-09-08",
            "approx_r1cs": 2997263,
            "n": 1,
            "leaf_width": REC_AGG_WIDTH,
            "degree_bits": proof.degree_bits,
            "log_blowup": log_blowup,
            "fri_log_max_height": chal.fri_log_max_height,
            "extra_query_index_bits": chal.extra_query_index_bits,
            "num_index_bits": num_index_bits,
            "y_shift": y_shift,
            "path_depth": trace_log_height,
            "query_index": qi as u32,
            "trace_index": t_idx as u32,
            "trace_root": trace_root.to_vec(),
            "leaf_row": row.iter().map(|x| x.as_canonical_u32()).collect::<Vec<_>>(),
            "siblings": trace_open.opening_proof.iter().map(|s| s.to_vec()).collect::<Vec<_>>(),
            "notes": "RecAgg Trace ValMmcs N=1 FS-bound (QI>>y_shift); Observe/Chal/Quot/DeepRo / N=40 FriFsAuth deferred"
        });

        let out = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../fixtures/e5b/wrap_recagg_fs_mmcs_golden.json");
        std::fs::write(&out, serde_json::to_string_pretty(&golden).unwrap()).expect("write");
        let wrap = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../wqc-snark-wrap/fixtures/e5b3/wrap_recagg_fs_mmcs_golden.json");
        if let Some(parent) = wrap.parent() {
            if parent.exists() {
                let _ = std::fs::write(&wrap, serde_json::to_string_pretty(&golden).unwrap());
            }
        }
    }

    #[test]
    fn lock_recagg_fs_mmcs_golden() {
        use p3_mersenne_31::Mersenne31 as Val;

        use crate::plonky3_stark::recursion::air::REC_AGG_WIDTH;

        let golden_path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../fixtures/e5b/wrap_recagg_fs_mmcs_golden.json"
        );
        let raw = std::fs::read_to_string(golden_path).expect("wrap_recagg_fs_mmcs_golden.json");
        let v: serde_json::Value = serde_json::from_str(&raw).expect("golden json");
        assert_eq!(v["statement"].as_str().unwrap(), "thick_recagg_fs_mmcs_v0");
        assert_eq!(v["n"].as_u64().unwrap(), 1);
        assert_eq!(v["leaf_width"].as_u64().unwrap() as usize, REC_AGG_WIDTH);

        let y_shift = v["y_shift"].as_u64().unwrap() as usize;
        let qi = v["query_index"].as_u64().unwrap() as usize;
        let t_idx = v["trace_index"].as_u64().unwrap() as usize;
        assert_eq!(qi >> y_shift, t_idx);

        let row: Vec<Val> = v["leaf_row"]
            .as_array()
            .unwrap()
            .iter()
            .map(|x| Val::from_u32(x.as_u64().unwrap() as u32))
            .collect();
        assert_eq!(row.len(), REC_AGG_WIDTH);
        let siblings: Vec<[u8; 32]> = v["siblings"]
            .as_array()
            .unwrap()
            .iter()
            .map(|s| {
                let bytes: Vec<u8> = s
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(|b| b.as_u64().unwrap() as u8)
                    .collect();
                bytes.try_into().expect("sib 32")
            })
            .collect();
        let root: [u8; 32] = v["trace_root"]
            .as_array()
            .unwrap()
            .iter()
            .map(|b| b.as_u64().unwrap() as u8)
            .collect::<Vec<_>>()
            .try_into()
            .expect("root 32");
        assert_eq!(
            merkle_root_from_path(hash_val_leaf(&row), &siblings, t_idx),
            root
        );
        assert_eq!(siblings.len(), v["path_depth"].as_u64().unwrap() as usize);
        assert_eq!(v["approx_r1cs"].as_u64().unwrap(), 2997263);
    }

    #[test]
    fn emit_recagg_fri_fs_observe_golden() {
        use p3_field::BasedVectorSpace;
        use p3_field::PrimeField32;
        use sha3::{Digest, Keccak256};
        use std::path::PathBuf;

        use crate::plonky3_stark::recursion::air::{REC_AGG_WIDTH, REC_KIND_LEAF};
        use crate::plonky3_stark::recursion::child_binding::STARK_DIGEST_LEN;
        use crate::plonky3_stark::recursion::context::RecursiveAggregationContext;
        use crate::plonky3_stark::recursion::prove::generate_recursive_aggregation_proof;
        use crate::plonky3_stark::recursion::transcript_v6::decode_rec_agg_proof_owned_v6;

        let ctx = RecursiveAggregationContext {
            parent_task_id: "parent",
            compose_label: "root",
            manifest_root_hash: "m",
            left_child_hash: [1u8; CHILD_HASH_LEN],
            right_child_hash: [2u8; CHILD_HASH_LEN],
            left_stark_digest: [3u8; STARK_DIGEST_LEN],
            right_stark_digest: [4u8; STARK_DIGEST_LEN],
            left_kind: REC_KIND_LEAF,
            right_kind: REC_KIND_LEAF,
            left_agg_cert: None,
            right_agg_cert: None,
            left_leaf_bundle: None,
            right_leaf_bundle: None,
            security_level: "ultra",
        };
        let transcript = generate_recursive_aggregation_proof(&ctx).expect("prove");
        let plonky3 = decode_rec_agg_proof_owned_v6(&transcript, &ctx).expect("decode v6");
        let proof: Proof<WqcStarkConfig> = postcard::from_bytes(&plonky3).expect("postcard");
        let chal = replay_rec_agg_fri_challenges(&proof).expect("replay");
        assert_eq!(proof.degree_bits, 2);
        assert_eq!(chal.query_indices.len(), 40);
        assert_eq!(chal.betas.len(), 2);
        assert_eq!(proof.opened_values.trace_local.len(), REC_AGG_WIDTH);

        let degree_bits = proof.degree_bits;
        let trace_root = *proof.commitments.trace.roots().first().expect("trace root");
        let quot_root = *proof
            .commitments
            .quotient_chunks
            .roots()
            .first()
            .expect("quot root");
        let view = decode_pcs_view(&proof).expect("pcs");
        let first_layer = *view
            .first_layer_commitment
            .roots()
            .first()
            .expect("first layer");
        let fri0 = *view.fri_proof.commit_phase_commits[0]
            .roots()
            .first()
            .expect("fri0");
        let fri1 = *view.fri_proof.commit_phase_commits[1]
            .roots()
            .first()
            .expect("fri1");

        fn push_u32(out: &mut Vec<u8>, v: u32) {
            out.extend_from_slice(&v.to_le_bytes());
        }
        fn push_challenge(out: &mut Vec<u8>, c: &Challenge) {
            for limb in BasedVectorSpace::<Val>::as_basis_coefficients_slice(c) {
                push_u32(out, limb.as_canonical_u32());
            }
        }
        fn keccak(msg: &[u8]) -> [u8; 32] {
            Keccak256::digest(msg).into()
        }

        let mut prefix = Vec::new();
        push_u32(&mut prefix, degree_bits as u32);
        push_u32(&mut prefix, degree_bits as u32);
        push_u32(&mut prefix, 0);
        prefix.extend_from_slice(&trace_root);
        assert_eq!(prefix.len(), 44);
        let d1 = keccak(&prefix);

        let mut m2 = Vec::new();
        m2.extend_from_slice(&d1);
        m2.extend_from_slice(&quot_root);
        assert_eq!(m2.len(), 64);
        let d2 = keccak(&m2);

        let mut m3 = Vec::new();
        m3.extend_from_slice(&d2);
        for c in &proof.opened_values.trace_local {
            push_challenge(&mut m3, c);
        }
        for c in proof.opened_values.trace_next.as_ref().unwrap() {
            push_challenge(&mut m3, c);
        }
        assert_eq!(proof.opened_values.quotient_chunks.len(), 1);
        for c in &proof.opened_values.quotient_chunks[0] {
            push_challenge(&mut m3, c);
        }
        // 32 + 330*12*2 + 3*12 = 7988
        assert_eq!(m3.len(), 7988, "RecAgg openings absorb");
        let d3 = keccak(&m3);

        let mut m4 = Vec::new();
        m4.extend_from_slice(&d3);
        m4.extend_from_slice(&first_layer);
        let d4 = keccak(&m4);

        let mut m5 = Vec::new();
        m5.extend_from_slice(&d4);
        m5.extend_from_slice(&fri0);
        let d5 = keccak(&m5);

        let mut m6 = Vec::new();
        m6.extend_from_slice(&d5);
        m6.extend_from_slice(&fri1);
        let chain = keccak(&m6);

        let final_poly = view.fri_proof.final_poly;
        let pow = view.fri_proof.pow_witness.as_canonical_u32();
        let mut m7 = Vec::new();
        m7.extend_from_slice(&chain);
        push_challenge(&mut m7, &final_poly);
        push_u32(&mut m7, pow);
        assert_eq!(m7.len(), 48);
        let d7: [u8; 32] = keccak(&m7);
        let mut off = 0usize;
        let sample_bits = |d: &[u8; 32], off: &mut usize, bits: usize| -> usize {
            let mut b = [0u8; 4];
            for i in 0..4 {
                b[i] = d[31 - *off - i];
            }
            *off += 4;
            let u = u32::from_le_bytes(b) as usize;
            u & ((1 << bits) - 1)
        };
        assert_eq!(sample_bits(&d7, &mut off, 8), 0, "pow");
        // N=40 RecAgg ultra (DEVNET_FRI_NUM_QUERIES): PoW + 40 queries; reflushes when LIFO exhausts.
        let mut dig = d7;
        for (i, &want) in chal.query_indices.iter().enumerate() {
            if off == 32 {
                dig = keccak(&dig);
                off = 0;
            }
            assert_eq!(sample_bits(&dig, &mut off, 4), want, "qi[{i}]");
        }

        let mut trace_local = Vec::new();
        for c in &proof.opened_values.trace_local {
            let limbs: Vec<u32> = BasedVectorSpace::<Val>::as_basis_coefficients_slice(c)
                .iter()
                .map(|x: &Val| x.as_canonical_u32())
                .collect();
            trace_local.push(limbs);
        }
        let mut trace_next = Vec::new();
        for c in proof.opened_values.trace_next.as_ref().unwrap() {
            let limbs: Vec<u32> = BasedVectorSpace::<Val>::as_basis_coefficients_slice(c)
                .iter()
                .map(|x: &Val| x.as_canonical_u32())
                .collect();
            trace_next.push(limbs);
        }
        let mut quot_open = Vec::new();
        for c in &proof.opened_values.quotient_chunks[0] {
            let limbs: Vec<u32> = BasedVectorSpace::<Val>::as_basis_coefficients_slice(c)
                .iter()
                .map(|x: &Val| x.as_canonical_u32())
                .collect();
            quot_open.push(limbs);
        }
        let fp: Vec<u32> = BasedVectorSpace::<Val>::as_basis_coefficients_slice(&final_poly)
            .iter()
            .map(|x: &Val| x.as_canonical_u32())
            .collect();

        let golden = serde_json::json!({
            "statement": "thick_recagg_fri_fs_observe_v0",
            "gate": "e5b-3d",
            "source": "RecursiveAggregationAir HashChallenger 6-flush ChainDigest + query PoW sample_bits (W=330 N=40 ultra)",
            "measured_at": "2026-09-08",
            // placeholder until remmeasure
            "approx_r1cs": 18000000,
            "rec_agg_width": REC_AGG_WIDTH,
            "n": 40,
            "degree_bits": degree_bits,
            "flush_lens": [44, 64, 7988, 64, 64, 64],
            "trace_root": trace_root.to_vec(),
            "quot_root": quot_root.to_vec(),
            "trace_local": trace_local,
            "trace_next": trace_next,
            "quot_open": quot_open,
            "first_layer_root": first_layer.to_vec(),
            "fri_commit0": fri0.to_vec(),
            "fri_commit1": fri1.to_vec(),
            "chain_digest": chain.to_vec(),
            "final_poly": fp,
            "pow_witness": pow,
            "query_index": &chal.query_indices[..40],
            "notes": "Absorb-only mid-state (no in-circuit α/ζ/β); RecAgg ultra N=40 W=330; Chal/FriFsAuth deferred"
        });

        let out = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../fixtures/e5b/wrap_recagg_fri_fs_observe_golden.json");
        std::fs::write(&out, serde_json::to_string_pretty(&golden).unwrap()).expect("write");
        let wrap = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../wqc-snark-wrap/fixtures/e5b3/wrap_recagg_fri_fs_observe_golden.json");
        if let Some(parent) = wrap.parent() {
            if parent.exists() {
                let _ = std::fs::write(&wrap, serde_json::to_string_pretty(&golden).unwrap());
            }
        }
    }

    #[test]
    fn lock_recagg_fri_fs_observe_golden() {
        use sha3::{Digest, Keccak256};

        use crate::plonky3_stark::recursion::air::REC_AGG_WIDTH;

        let golden_path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../fixtures/e5b/wrap_recagg_fri_fs_observe_golden.json"
        );
        let raw =
            std::fs::read_to_string(golden_path).expect("wrap_recagg_fri_fs_observe_golden.json");
        let v: serde_json::Value = serde_json::from_str(&raw).expect("golden json");
        assert_eq!(
            v["statement"].as_str().unwrap(),
            "thick_recagg_fri_fs_observe_v0"
        );
        assert_eq!(v["rec_agg_width"].as_u64().unwrap() as usize, REC_AGG_WIDTH);
        assert_eq!(v["n"].as_u64().unwrap(), 40);
        assert_eq!(v["degree_bits"].as_u64().unwrap(), 2);

        fn bytes(v: &serde_json::Value, key: &str) -> Vec<u8> {
            v[key]
                .as_array()
                .unwrap()
                .iter()
                .map(|x| x.as_u64().unwrap() as u8)
                .collect()
        }
        fn ef3_rows(v: &serde_json::Value, key: &str) -> Vec<[u32; 3]> {
            v[key]
                .as_array()
                .unwrap()
                .iter()
                .map(|row| {
                    let a = row.as_array().unwrap();
                    [
                        a[0].as_u64().unwrap() as u32,
                        a[1].as_u64().unwrap() as u32,
                        a[2].as_u64().unwrap() as u32,
                    ]
                })
                .collect()
        }
        fn push_u32(out: &mut Vec<u8>, x: u32) {
            out.extend_from_slice(&x.to_le_bytes());
        }
        fn keccak(msg: &[u8]) -> [u8; 32] {
            Keccak256::digest(msg).into()
        }

        let degree_bits = v["degree_bits"].as_u64().unwrap() as u32;
        let trace_root = bytes(&v, "trace_root");
        let quot_root = bytes(&v, "quot_root");
        let first_layer = bytes(&v, "first_layer_root");
        let fri0 = bytes(&v, "fri_commit0");
        let fri1 = bytes(&v, "fri_commit1");
        let want_chain = bytes(&v, "chain_digest");
        let trace_local = ef3_rows(&v, "trace_local");
        let trace_next = ef3_rows(&v, "trace_next");
        let quot_open = ef3_rows(&v, "quot_open");
        assert_eq!(trace_local.len(), REC_AGG_WIDTH);
        assert_eq!(trace_next.len(), REC_AGG_WIDTH);
        assert_eq!(quot_open.len(), 3);

        let mut m1 = Vec::new();
        push_u32(&mut m1, degree_bits);
        push_u32(&mut m1, degree_bits);
        push_u32(&mut m1, 0);
        m1.extend_from_slice(&trace_root);
        assert_eq!(m1.len(), 44);
        let d1 = keccak(&m1);

        let mut m2 = Vec::new();
        m2.extend_from_slice(&d1);
        m2.extend_from_slice(&quot_root);
        let d2 = keccak(&m2);

        let mut m3 = Vec::new();
        m3.extend_from_slice(&d2);
        for row in trace_local.iter().chain(trace_next.iter()) {
            for limb in row {
                push_u32(&mut m3, *limb);
            }
        }
        for row in &quot_open {
            for limb in row {
                push_u32(&mut m3, *limb);
            }
        }
        assert_eq!(m3.len(), 7988);
        let d3 = keccak(&m3);

        let d4 = keccak(&[d3.as_slice(), first_layer.as_slice()].concat());
        let d5 = keccak(&[d4.as_slice(), fri0.as_slice()].concat());
        let chain = keccak(&[d5.as_slice(), fri1.as_slice()].concat());
        assert_eq!(chain.to_vec(), want_chain);

        let fp = v["final_poly"]
            .as_array()
            .unwrap()
            .iter()
            .map(|x| x.as_u64().unwrap() as u32)
            .collect::<Vec<_>>();
        let pow = v["pow_witness"].as_u64().unwrap() as u32;
        let mut m7 = Vec::new();
        m7.extend_from_slice(&chain);
        for limb in &fp {
            push_u32(&mut m7, *limb);
        }
        push_u32(&mut m7, pow);
        let d7 = keccak(&m7);
        let mut off = 0usize;
        let mut dig = d7;
        let sample_bits = |d: &[u8; 32], off: &mut usize, bits: usize| -> u32 {
            let mut b = [0u8; 4];
            for i in 0..4 {
                b[i] = d[31 - *off - i];
            }
            *off += 4;
            let u = u32::from_le_bytes(b);
            u & ((1 << bits) - 1)
        };
        assert_eq!(sample_bits(&dig, &mut off, 8), 0);
        let want_qi = v["query_index"]
            .as_array()
            .unwrap()
            .iter()
            .map(|x| x.as_u64().unwrap() as u32)
            .collect::<Vec<_>>();
        assert_eq!(want_qi.len(), 40);
        for (i, &want) in want_qi.iter().enumerate() {
            if off == 32 {
                dig = keccak(&dig);
                off = 0;
            }
            assert_eq!(sample_bits(&dig, &mut off, 4), want, "qi[{i}]");
        }
        // placeholder until remmeasure
        assert_eq!(v["approx_r1cs"].as_u64().unwrap(), 18000000);
    }

    #[test]
    fn emit_recagg_fri_fs_chal_golden() {
        use p3_field::BasedVectorSpace;
        use p3_field::PrimeField32;
        use sha3::{Digest, Keccak256};
        use std::path::PathBuf;

        use crate::plonky3_stark::recursion::air::{REC_AGG_WIDTH, REC_KIND_LEAF};
        use crate::plonky3_stark::recursion::child_binding::STARK_DIGEST_LEN;
        use crate::plonky3_stark::recursion::context::RecursiveAggregationContext;
        use crate::plonky3_stark::recursion::prove::generate_recursive_aggregation_proof;
        use crate::plonky3_stark::recursion::transcript_v6::decode_rec_agg_proof_owned_v6;

        let ctx = RecursiveAggregationContext {
            parent_task_id: "parent",
            compose_label: "root",
            manifest_root_hash: "m",
            left_child_hash: [1u8; CHILD_HASH_LEN],
            right_child_hash: [2u8; CHILD_HASH_LEN],
            left_stark_digest: [3u8; STARK_DIGEST_LEN],
            right_stark_digest: [4u8; STARK_DIGEST_LEN],
            left_kind: REC_KIND_LEAF,
            right_kind: REC_KIND_LEAF,
            left_agg_cert: None,
            right_agg_cert: None,
            left_leaf_bundle: None,
            right_leaf_bundle: None,
            security_level: "ultra",
        };
        let transcript = generate_recursive_aggregation_proof(&ctx).expect("prove");
        let plonky3 = decode_rec_agg_proof_owned_v6(&transcript, &ctx).expect("decode v6");
        let proof: Proof<WqcStarkConfig> = postcard::from_bytes(&plonky3).expect("postcard");
        let chal = replay_rec_agg_fri_challenges(&proof).expect("replay");
        assert_eq!(proof.degree_bits, 2);
        assert_eq!(chal.query_indices.len(), 40);
        assert_eq!(chal.betas.len(), 2);
        assert_eq!(proof.opened_values.trace_local.len(), REC_AGG_WIDTH);

        let degree_bits = proof.degree_bits;
        let trace_root = *proof.commitments.trace.roots().first().expect("trace root");
        let quot_root = *proof
            .commitments
            .quotient_chunks
            .roots()
            .first()
            .expect("quot root");
        let view = decode_pcs_view(&proof).expect("pcs");
        let first_layer = *view
            .first_layer_commitment
            .roots()
            .first()
            .expect("first layer");
        let fri0 = *view.fri_proof.commit_phase_commits[0]
            .roots()
            .first()
            .expect("fri0");
        let fri1 = *view.fri_proof.commit_phase_commits[1]
            .roots()
            .first()
            .expect("fri1");

        fn push_u32(out: &mut Vec<u8>, v: u32) {
            out.extend_from_slice(&v.to_le_bytes());
        }
        fn push_challenge(out: &mut Vec<u8>, c: &Challenge) {
            for limb in BasedVectorSpace::<Val>::as_basis_coefficients_slice(c) {
                push_u32(out, limb.as_canonical_u32());
            }
        }
        fn keccak(msg: &[u8]) -> [u8; 32] {
            Keccak256::digest(msg).into()
        }
        fn sample_base_m31(d: &[u8; 32], off: &mut usize) -> Option<u32> {
            let mut b = [0u8; 4];
            for i in 0..4 {
                b[i] = d[31 - *off - i];
            }
            *off += 4;
            let u = u32::from_le_bytes(b) & 0x7fff_ffff;
            if u == 0x7fff_ffff {
                None
            } else {
                Some(u)
            }
        }
        // Zero-reject path (RecAgg ultra golden): three consecutive accepts from dig start.
        fn sample_algebra(d: &[u8; 32]) -> [u32; 3] {
            let mut off = 0usize;
            [
                sample_base_m31(d, &mut off).expect("limb0"),
                sample_base_m31(d, &mut off).expect("limb1"),
                sample_base_m31(d, &mut off).expect("limb2"),
            ]
        }
        let limbs = |c: &Challenge| -> [u32; 3] {
            let s = BasedVectorSpace::<Val>::as_basis_coefficients_slice(c);
            [
                s[0].as_canonical_u32(),
                s[1].as_canonical_u32(),
                s[2].as_canonical_u32(),
            ]
        };

        let mut prefix = Vec::new();
        push_u32(&mut prefix, degree_bits as u32);
        push_u32(&mut prefix, degree_bits as u32);
        push_u32(&mut prefix, 0);
        prefix.extend_from_slice(&trace_root);
        let d1 = keccak(&prefix);
        let constraint_alpha = sample_algebra(&d1);
        assert_eq!(constraint_alpha, limbs(&chal.constraint_alpha));

        let d2 = keccak(&[d1.as_slice(), quot_root.as_slice()].concat());
        let zeta = sample_algebra(&d2);
        assert_eq!(zeta, limbs(&chal.zeta));

        let mut m3 = Vec::new();
        m3.extend_from_slice(&d2);
        for c in &proof.opened_values.trace_local {
            push_challenge(&mut m3, c);
        }
        for c in proof.opened_values.trace_next.as_ref().unwrap() {
            push_challenge(&mut m3, c);
        }
        assert_eq!(proof.opened_values.quotient_chunks.len(), 1);
        for c in &proof.opened_values.quotient_chunks[0] {
            push_challenge(&mut m3, c);
        }
        assert_eq!(m3.len(), 7988, "RecAgg openings absorb");
        let d3 = keccak(&m3);
        let batch_alpha = sample_algebra(&d3);
        assert_eq!(batch_alpha, limbs(&chal.batch_alpha));

        let d4 = keccak(&[d3.as_slice(), first_layer.as_slice()].concat());
        let bivariate_beta = sample_algebra(&d4);
        assert_eq!(bivariate_beta, limbs(&chal.bivariate_beta));

        let d5 = keccak(&[d4.as_slice(), fri0.as_slice()].concat());
        let beta0 = sample_algebra(&d5);
        assert_eq!(beta0, limbs(&chal.betas[0]));

        let d6 = keccak(&[d5.as_slice(), fri1.as_slice()].concat());
        let beta1 = sample_algebra(&d6);
        assert_eq!(beta1, limbs(&chal.betas[1]));
        let chain = d6; // zero-reject ⇒ QueryChain == absorb D6

        let final_poly = view.fri_proof.final_poly;
        let pow = view.fri_proof.pow_witness.as_canonical_u32();
        let mut m7 = Vec::new();
        m7.extend_from_slice(&chain);
        push_challenge(&mut m7, &final_poly);
        push_u32(&mut m7, pow);
        assert_eq!(m7.len(), 48);
        let d7: [u8; 32] = keccak(&m7);
        let mut off = 0usize;
        let sample_bits = |d: &[u8; 32], off: &mut usize, bits: usize| -> usize {
            let mut b = [0u8; 4];
            for i in 0..4 {
                b[i] = d[31 - *off - i];
            }
            *off += 4;
            let u = u32::from_le_bytes(b) as usize;
            u & ((1 << bits) - 1)
        };
        assert_eq!(sample_bits(&d7, &mut off, 8), 0, "pow");
        let mut dig = d7;
        for (i, &want) in chal.query_indices.iter().enumerate() {
            if off == 32 {
                dig = keccak(&dig);
                off = 0;
            }
            assert_eq!(sample_bits(&dig, &mut off, 4), want, "qi[{i}]");
        }

        let mut trace_local = Vec::new();
        for c in &proof.opened_values.trace_local {
            let row: Vec<u32> = BasedVectorSpace::<Val>::as_basis_coefficients_slice(c)
                .iter()
                .map(|x: &Val| x.as_canonical_u32())
                .collect();
            trace_local.push(row);
        }
        let mut trace_next = Vec::new();
        for c in proof.opened_values.trace_next.as_ref().unwrap() {
            let row: Vec<u32> = BasedVectorSpace::<Val>::as_basis_coefficients_slice(c)
                .iter()
                .map(|x: &Val| x.as_canonical_u32())
                .collect();
            trace_next.push(row);
        }
        let mut quot_open = Vec::new();
        for c in &proof.opened_values.quotient_chunks[0] {
            let row: Vec<u32> = BasedVectorSpace::<Val>::as_basis_coefficients_slice(c)
                .iter()
                .map(|x: &Val| x.as_canonical_u32())
                .collect();
            quot_open.push(row);
        }
        let fp: Vec<u32> = BasedVectorSpace::<Val>::as_basis_coefficients_slice(&final_poly)
            .iter()
            .map(|x: &Val| x.as_canonical_u32())
            .collect();

        let golden = serde_json::json!({
            "statement": "thick_recagg_fri_fs_chal_v0",
            "gate": "e5b-3d",
            "source": "RecursiveAggregationAir HashChallenger D1..D6 sample_algebra + query sponge (W=330 N=40 ultra)",
            "measured_at": "2026-09-08",
            // placeholder until remmeasure
            "approx_r1cs": 22000000,
            "rec_agg_width": REC_AGG_WIDTH,
            "n": 40,
            "degree_bits": degree_bits,
            "flush_lens": [44, 64, 7988, 64, 64, 64],
            "trace_root": trace_root.to_vec(),
            "quot_root": quot_root.to_vec(),
            "trace_local": trace_local,
            "trace_next": trace_next,
            "quot_open": quot_open,
            "first_layer_root": first_layer.to_vec(),
            "fri_commit0": fri0.to_vec(),
            "fri_commit1": fri1.to_vec(),
            "chain_digest": chain.to_vec(),
            "constraint_alpha": constraint_alpha,
            "zeta": zeta,
            "batch_alpha": batch_alpha,
            "bivariate_beta": bivariate_beta,
            "betas": [beta0, beta1],
            "final_poly": fp,
            "pow_witness": pow,
            "query_index": &chal.query_indices[..40],
            "notes": "D1..D6 sample_algebra MaxReflush=3 capacity (RecAgg ultra zero-reject); FriFold Beta=betas[0]; N=40; FriFsAuth deferred"
        });

        let out = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../fixtures/e5b/wrap_recagg_fri_fs_chal_golden.json");
        std::fs::write(&out, serde_json::to_string_pretty(&golden).unwrap()).expect("write");
        let wrap = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../wqc-snark-wrap/fixtures/e5b3/wrap_recagg_fri_fs_chal_golden.json");
        if let Some(parent) = wrap.parent() {
            if parent.exists() {
                let _ = std::fs::write(&wrap, serde_json::to_string_pretty(&golden).unwrap());
            }
        }
    }

    #[test]
    fn lock_recagg_fri_fs_chal_golden() {
        use p3_field::{BasedVectorSpace, PrimeField32};
        use sha3::{Digest, Keccak256};

        use crate::plonky3_stark::recursion::air::{REC_AGG_WIDTH, REC_KIND_LEAF};
        use crate::plonky3_stark::recursion::child_binding::STARK_DIGEST_LEN;
        use crate::plonky3_stark::recursion::context::RecursiveAggregationContext;
        use crate::plonky3_stark::recursion::prove::generate_recursive_aggregation_proof;
        use crate::plonky3_stark::recursion::transcript_v6::decode_rec_agg_proof_owned_v6;

        let golden_path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../fixtures/e5b/wrap_recagg_fri_fs_chal_golden.json"
        );
        let raw =
            std::fs::read_to_string(golden_path).expect("wrap_recagg_fri_fs_chal_golden.json");
        let v: serde_json::Value = serde_json::from_str(&raw).expect("golden json");
        assert_eq!(
            v["statement"].as_str().unwrap(),
            "thick_recagg_fri_fs_chal_v0"
        );
        assert_eq!(v["rec_agg_width"].as_u64().unwrap() as usize, REC_AGG_WIDTH);
        assert_eq!(v["n"].as_u64().unwrap(), 40);

        fn bytes(v: &serde_json::Value, key: &str) -> Vec<u8> {
            v[key]
                .as_array()
                .unwrap()
                .iter()
                .map(|x| x.as_u64().unwrap() as u8)
                .collect()
        }
        fn ef3(v: &serde_json::Value, key: &str) -> [u32; 3] {
            let a = v[key].as_array().unwrap();
            [
                a[0].as_u64().unwrap() as u32,
                a[1].as_u64().unwrap() as u32,
                a[2].as_u64().unwrap() as u32,
            ]
        }
        fn ef3_rows(v: &serde_json::Value, key: &str) -> Vec<[u32; 3]> {
            v[key]
                .as_array()
                .unwrap()
                .iter()
                .map(|row| {
                    let a = row.as_array().unwrap();
                    [
                        a[0].as_u64().unwrap() as u32,
                        a[1].as_u64().unwrap() as u32,
                        a[2].as_u64().unwrap() as u32,
                    ]
                })
                .collect()
        }
        fn push_u32(out: &mut Vec<u8>, x: u32) {
            out.extend_from_slice(&x.to_le_bytes());
        }
        fn keccak(msg: &[u8]) -> [u8; 32] {
            Keccak256::digest(msg).into()
        }
        fn sample_base_m31(d: &[u8; 32], off: &mut usize) -> u32 {
            let mut b = [0u8; 4];
            for i in 0..4 {
                b[i] = d[31 - *off - i];
            }
            *off += 4;
            let u = u32::from_le_bytes(b) & 0x7fff_ffff;
            assert_ne!(u, 0x7fff_ffff, "M31 reject");
            u
        }
        fn sample_algebra(d: &[u8; 32]) -> [u32; 3] {
            let mut off = 0usize;
            [
                sample_base_m31(d, &mut off),
                sample_base_m31(d, &mut off),
                sample_base_m31(d, &mut off),
            ]
        }

        let degree_bits = v["degree_bits"].as_u64().unwrap() as u32;
        let mut m1 = Vec::new();
        push_u32(&mut m1, degree_bits);
        push_u32(&mut m1, degree_bits);
        push_u32(&mut m1, 0);
        m1.extend_from_slice(&bytes(&v, "trace_root"));
        let d1 = keccak(&m1);
        assert_eq!(sample_algebra(&d1), ef3(&v, "constraint_alpha"));

        let d2 = keccak(&[d1.as_slice(), bytes(&v, "quot_root").as_slice()].concat());
        assert_eq!(sample_algebra(&d2), ef3(&v, "zeta"));

        let mut m3 = Vec::new();
        m3.extend_from_slice(&d2);
        for row in ef3_rows(&v, "trace_local")
            .iter()
            .chain(ef3_rows(&v, "trace_next").iter())
            .chain(ef3_rows(&v, "quot_open").iter())
        {
            for limb in row {
                push_u32(&mut m3, *limb);
            }
        }
        assert_eq!(m3.len(), 7988);
        let d3 = keccak(&m3);
        assert_eq!(sample_algebra(&d3), ef3(&v, "batch_alpha"));

        let d4 = keccak(&[d3.as_slice(), bytes(&v, "first_layer_root").as_slice()].concat());
        assert_eq!(sample_algebra(&d4), ef3(&v, "bivariate_beta"));
        let d5 = keccak(&[d4.as_slice(), bytes(&v, "fri_commit0").as_slice()].concat());
        let d6 = keccak(&[d5.as_slice(), bytes(&v, "fri_commit1").as_slice()].concat());
        let betas = v["betas"].as_array().unwrap();
        let b0 = [
            betas[0][0].as_u64().unwrap() as u32,
            betas[0][1].as_u64().unwrap() as u32,
            betas[0][2].as_u64().unwrap() as u32,
        ];
        let b1 = [
            betas[1][0].as_u64().unwrap() as u32,
            betas[1][1].as_u64().unwrap() as u32,
            betas[1][2].as_u64().unwrap() as u32,
        ];
        assert_eq!(sample_algebra(&d5), b0);
        assert_eq!(sample_algebra(&d6), b1);
        assert_eq!(d6.as_slice(), bytes(&v, "chain_digest").as_slice());

        let ctx = RecursiveAggregationContext {
            parent_task_id: "parent",
            compose_label: "root",
            manifest_root_hash: "m",
            left_child_hash: [1u8; CHILD_HASH_LEN],
            right_child_hash: [2u8; CHILD_HASH_LEN],
            left_stark_digest: [3u8; STARK_DIGEST_LEN],
            right_stark_digest: [4u8; STARK_DIGEST_LEN],
            left_kind: REC_KIND_LEAF,
            right_kind: REC_KIND_LEAF,
            left_agg_cert: None,
            right_agg_cert: None,
            left_leaf_bundle: None,
            right_leaf_bundle: None,
            security_level: "ultra",
        };
        let transcript = generate_recursive_aggregation_proof(&ctx).expect("prove");
        let plonky3 = decode_rec_agg_proof_owned_v6(&transcript, &ctx).expect("decode v6");
        let proof: Proof<WqcStarkConfig> = postcard::from_bytes(&plonky3).expect("postcard");
        let chal = replay_rec_agg_fri_challenges(&proof).expect("replay");
        let limbs = |c: &Challenge| -> [u32; 3] {
            let s = BasedVectorSpace::<Val>::as_basis_coefficients_slice(c);
            [
                s[0].as_canonical_u32(),
                s[1].as_canonical_u32(),
                s[2].as_canonical_u32(),
            ]
        };
        assert_eq!(limbs(&chal.constraint_alpha), ef3(&v, "constraint_alpha"));
        assert_eq!(limbs(&chal.zeta), ef3(&v, "zeta"));
        assert_eq!(limbs(&chal.batch_alpha), ef3(&v, "batch_alpha"));
        assert_eq!(limbs(&chal.bivariate_beta), ef3(&v, "bivariate_beta"));
        assert_eq!(limbs(&chal.betas[0]), b0);
        assert_eq!(limbs(&chal.betas[1]), b1);

        // placeholder until remmeasure
        assert_eq!(v["approx_r1cs"].as_u64().unwrap(), 22000000);
    }

    #[test]
    fn emit_recagg_fri_fs_auth_golden() {
        use p3_commit::{Pcs, PolynomialSpace};
        use p3_field::PrimeField32;
        use std::path::PathBuf;

        use crate::plonky3_stark::recursion::air::{REC_AGG_WIDTH, REC_KIND_LEAF};
        use crate::plonky3_stark::recursion::child_binding::STARK_DIGEST_LEN;
        use crate::plonky3_stark::recursion::context::RecursiveAggregationContext;
        use crate::plonky3_stark::recursion::fri_ro::decode_input_proof;
        use crate::plonky3_stark::recursion::prove::generate_recursive_aggregation_proof;
        use crate::plonky3_stark::recursion::transcript_v6::decode_rec_agg_proof_owned_v6;

        let ctx = RecursiveAggregationContext {
            parent_task_id: "parent",
            compose_label: "root",
            manifest_root_hash: "m",
            left_child_hash: [1u8; CHILD_HASH_LEN],
            right_child_hash: [2u8; CHILD_HASH_LEN],
            left_stark_digest: [3u8; STARK_DIGEST_LEN],
            right_stark_digest: [4u8; STARK_DIGEST_LEN],
            left_kind: REC_KIND_LEAF,
            right_kind: REC_KIND_LEAF,
            left_agg_cert: None,
            right_agg_cert: None,
            left_leaf_bundle: None,
            right_leaf_bundle: None,
            security_level: "ultra",
        };
        let transcript = generate_recursive_aggregation_proof(&ctx).expect("prove");
        let plonky3 = decode_rec_agg_proof_owned_v6(&transcript, &ctx).expect("decode v6");
        let proof: Proof<WqcStarkConfig> = postcard::from_bytes(&plonky3).expect("postcard");
        let chal = replay_rec_agg_fri_challenges(&proof).expect("replay");
        assert_eq!(proof.degree_bits, 2);
        assert_eq!(chal.query_indices.len(), 40);
        assert_eq!(
            proof.opened_values.quotient_chunks.len(),
            1,
            "RecAgg single quot chunk"
        );
        assert_eq!(proof.opened_values.trace_local.len(), REC_AGG_WIDTH);

        let view = decode_pcs_view(&proof).expect("pcs");
        let config = circle_config_matching_proof(&proof).expect("cfg");
        let pcs = config.pcs();
        let degree = 1usize << proof.degree_bits;
        let init_trace_domain = <crate::plonky3_stark::config::Pcs as Pcs<
            Challenge,
            crate::plonky3_stark::config::Challenger,
        >>::natural_domain_for_degree(pcs, degree);
        let log_blowup = chal.log_blowup;
        let log_global_max_height = view.fri_proof.commit_phase_commits.len() + log_blowup + 1;
        let trace_height = init_trace_domain.size() << log_blowup;
        assert!(trace_height.is_power_of_two());
        let trace_log_height = trace_height.trailing_zeros() as usize;
        let y_shift = log_global_max_height - trace_log_height;
        assert_eq!(y_shift, 1, "RecAgg ValMmcs index shift");

        let num_quot = proof.opened_values.quotient_chunks.len();
        assert_eq!(num_quot, 1);
        let log_num_quot = num_quot.trailing_zeros() as usize;
        let quot_parent =
            init_trace_domain.create_disjoint_domain(1usize << (proof.degree_bits + log_num_quot));
        let quot_chunk_domains = quot_parent.split_domains(num_quot);
        let quot_h = quot_chunk_domains[0].size() << log_blowup;
        assert!(quot_h.is_power_of_two());
        let quot_log_height = quot_h.trailing_zeros() as usize;
        let quot_shift = log_global_max_height - quot_log_height;
        assert_eq!(quot_h, 16);
        assert_eq!(quot_log_height, 4);
        assert_eq!(quot_shift, 0, "RecAgg quot ValMmcs index shift");
        assert_ne!(quot_shift, y_shift);

        let trace_root = *proof.commitments.trace.roots().first().expect("trace root");
        let quot_root = *proof
            .commitments
            .quotient_chunks
            .roots()
            .first()
            .expect("quot root");
        let mut val_mmcs = Vec::with_capacity(40);
        let mut quot_mmcs = Vec::with_capacity(40);
        let mut trace_index = Vec::with_capacity(40);
        let mut quot_index = Vec::with_capacity(40);
        for q in 0..40 {
            let qi = chal.query_indices[q];
            let input =
                decode_input_proof(&view.fri_proof.query_proofs[q].input_proof).expect("input");
            let trace_open = &input.input_openings[0];
            let quot_open = &input.input_openings[1];
            let row = &trace_open.opened_values[0];
            assert_eq!(row.len(), REC_AGG_WIDTH);
            let quot_row = &quot_open.opened_values[0];
            assert_eq!(quot_row.len(), 3, "EF_DIM");

            let t_idx = qi >> y_shift;
            let q_idx = qi >> quot_shift;
            assert_eq!(q_idx, qi);
            assert_eq!(
                merkle_root_from_path(hash_val_leaf(row), &trace_open.opening_proof, t_idx),
                trace_root,
                "q{q} trace ValMmcs root"
            );
            assert_eq!(
                merkle_root_from_path(hash_val_leaf(quot_row), &quot_open.opening_proof, q_idx),
                quot_root,
                "q{q} quot ValMmcs root"
            );
            assert_eq!(trace_open.opening_proof.len(), trace_log_height);
            assert_eq!(quot_open.opening_proof.len(), quot_log_height);

            trace_index.push(t_idx as u32);
            quot_index.push(q_idx as u32);
            val_mmcs.push(serde_json::json!({
                "leaf_row": row.iter().map(|x| x.as_canonical_u32()).collect::<Vec<_>>(),
                "siblings": trace_open.opening_proof.iter().map(|s| s.to_vec()).collect::<Vec<_>>(),
                "index": t_idx as u32,
            }));
            quot_mmcs.push(serde_json::json!({
                "leaf_row": quot_row.iter().map(|x| x.as_canonical_u32()).collect::<Vec<_>>(),
                "siblings": quot_open.opening_proof.iter().map(|s| s.to_vec()).collect::<Vec<_>>(),
                "index": q_idx as u32,
            }));
        }

        use p3_field::{BasedVectorSpace, PrimeCharacteristicRing};

        use crate::plonky3_stark::recursion::deep_ro_native::{
            deep_ro_recagg_trace_witness, deep_ro_w3_witness, ef_from_projective_line,
        };
        use crate::plonky3_stark::recursion::fri_fold_native::{
            cfft_permute_index, challenge_to_limbs, fold_x_row, fold_x_twiddle_inv, fold_y_row,
            fold_y_twiddle_inv, standard_nth_point,
        };
        use crate::plonky3_stark::recursion::fri_mmcs_bind::fri_chal_mmcs_bundle_from_proof;
        use crate::plonky3_stark::recursion::fri_ro::reconstruct_query_ro;
        use crate::plonky3_stark::recursion::merkle_keccak::compress_digests;

        let fl_root = *view
            .first_layer_commitment
            .roots()
            .first()
            .expect("first layer");
        let fri0 = *view.fri_proof.commit_phase_commits[0]
            .roots()
            .first()
            .expect("fri0");
        let fri1 = *view.fri_proof.commit_phase_commits[1]
            .roots()
            .first()
            .expect("fri1");
        let chal_bundle =
            fri_chal_mmcs_bundle_from_proof(&proof, REC_AGG_WIDTH).expect("chal mmcs");
        assert_eq!(chal_bundle.len(), chal.query_indices.len());
        assert_eq!(view.lambdas.len(), 2, "trace+quot heights");

        let zeta_next = init_trace_domain.next_point(chal.zeta).expect("zeta_next");
        let (at_x, at_y) = ef_from_projective_line(chal.zeta);
        let (atn_x, atn_y) = ef_from_projective_line(zeta_next);
        let limbs_u32 = |c: Challenge| -> Vec<u32> {
            challenge_to_limbs(c)
                .iter()
                .map(|x| x.as_canonical_u32())
                .collect()
        };
        let val_u32 = |v: Val| v.as_canonical_u32();

        let flatten_u32 = |evals: &[Challenge; 2]| -> Vec<u32> {
            let mut out = Vec::with_capacity(6);
            for e in evals {
                for limb in challenge_to_limbs(*e) {
                    out.push(limb.as_canonical_u32());
                }
            }
            out
        };

        let mut chal_first_layer = Vec::with_capacity(40);
        let mut chal_commit = Vec::with_capacity(40);
        let mut deep_ro = Vec::with_capacity(40);
        let trace_next = proof.opened_values.trace_next.as_ref().expect("trace_next");
        let mut px_trace = [Val::ZERO; REC_AGG_WIDTH];
        let mut pz_local = [Challenge::ZERO; REC_AGG_WIDTH];
        let mut pz_next = [Challenge::ZERO; REC_AGG_WIDTH];
        pz_local[..REC_AGG_WIDTH]
            .copy_from_slice(&proof.opened_values.trace_local[..REC_AGG_WIDTH]);
        pz_next[..REC_AGG_WIDTH].copy_from_slice(&trace_next[..REC_AGG_WIDTH]);
        let mut px_quot = [Val::ZERO; 3];
        let mut pz_quot = [Challenge::ZERO; 3];
        pz_quot.copy_from_slice(&proof.opened_values.quotient_chunks[0][..3]);

        for (q, bundle) in chal_bundle.iter().enumerate() {
            let qi = chal.query_indices[q];
            let fl = &bundle.first_layer;
            let fl_idx = qi >> 1;
            assert_eq!(fl.leaf_rows.len(), 2);
            assert_eq!(fl.siblings.len(), 3, "log2(8)");
            let tall: Vec<u32> = fl.leaf_rows[0]
                .iter()
                .map(|x| x.as_canonical_u32())
                .collect();
            let short: Vec<u32> = fl.leaf_rows[1]
                .iter()
                .map(|x| x.as_canonical_u32())
                .collect();
            assert_eq!(tall.len(), 6);
            assert_eq!(short.len(), 6);
            let mut dig = hash_val_leaf(&fl.leaf_rows[0]);
            let mut idx = fl_idx;
            dig = if idx.is_multiple_of(2) {
                compress_digests(dig, fl.siblings[0])
            } else {
                compress_digests(fl.siblings[0], dig)
            };
            idx /= 2;
            dig = compress_digests(dig, hash_val_leaf(&fl.leaf_rows[1]));
            for s in &fl.siblings[1..] {
                dig = if idx.is_multiple_of(2) {
                    compress_digests(dig, *s)
                } else {
                    compress_digests(*s, dig)
                };
                idx /= 2;
            }
            assert_eq!(dig, fl_root, "q{q} first-layer root");

            let (_, fold_ys) =
                reconstruct_query_ro(&proof, &chal, &view, q, REC_AGG_WIDTH).expect("ro");
            assert_eq!(fold_ys.len(), 2, "short+tall");
            let short_flat = flatten_u32(&[fold_ys[0].v0, fold_ys[0].v1]);
            let tall_flat = flatten_u32(&[fold_ys[1].v0, fold_ys[1].v1]);
            assert_eq!(short_flat, short, "q{q} Flatten(fold_y short)==FL short");
            assert_eq!(tall_flat, tall, "q{q} Flatten(fold_y tall)==FL tall");

            let input =
                decode_input_proof(&view.fri_proof.query_proofs[q].input_proof).expect("input");
            px_trace[..REC_AGG_WIDTH]
                .copy_from_slice(&input.input_openings[0].opened_values[0][..REC_AGG_WIDTH]);
            px_quot.copy_from_slice(&input.input_openings[1].opened_values[0][..3]);
            let orig_t = cfft_permute_index(qi >> y_shift, trace_log_height);
            let pt = standard_nth_point(trace_log_height, orig_t);
            let orig_q = cfft_permute_index(qi >> quot_shift, quot_log_height);
            let pq = standard_nth_point(quot_log_height, orig_q);
            let tw = deep_ro_recagg_trace_witness(
                chal.batch_alpha,
                pt.x,
                pt.y,
                chal.zeta,
                zeta_next,
                &px_trace,
                &pz_local,
                &pz_next,
                view.lambdas[0],
                proof.degree_bits,
            )
            .expect("deep_ro recagg");
            let qw = deep_ro_w3_witness(
                chal.batch_alpha,
                pq.x,
                pq.y,
                chal.zeta,
                px_quot,
                pz_quot,
                view.lambdas[1],
                proof.degree_bits + 1, // quot orig_size = log_h - blowup = 3
            );
            let pair_short = (qi >> y_shift) & 1;
            let pair_tall = (qi >> quot_shift) & 1;
            let lc_short = if pair_short == 0 {
                fold_ys[0].v0
            } else {
                fold_ys[0].v1
            };
            let lc_tall = if pair_tall == 0 {
                fold_ys[1].v0
            } else {
                fold_ys[1].v1
            };
            assert_eq!(tw.out, lc_short, "q{q} DeepRo trace == FL λc short");
            assert_eq!(qw.out, lc_tall, "q{q} DeepRo quot == FL λc tall");
            assert_eq!(tw.at_x, at_x);
            assert_eq!(tw.at_y, at_y);
            assert_eq!(qw.at_x, at_x);
            assert_eq!(qw.at_y, at_y);

            let t_inv_short = fold_y_twiddle_inv(fold_ys[0].index, fold_ys[0].log_folded_height);
            let t_inv_tall = fold_y_twiddle_inv(fold_ys[1].index, fold_ys[1].log_folded_height);
            let out_short = fold_y_row(
                fold_ys[0].index,
                fold_ys[0].log_folded_height,
                chal.bivariate_beta,
                fold_ys[0].v0,
                fold_ys[0].v1,
            );
            let out_tall = fold_y_row(
                fold_ys[1].index,
                fold_ys[1].log_folded_height,
                chal.bivariate_beta,
                fold_ys[1].v0,
                fold_ys[1].v1,
            );

            let qp = &view.fri_proof.query_proofs[q];
            let openings = &qp.commit_phase_openings;
            assert_eq!(openings.len(), 2);
            let mut index = qi >> chal.extra_query_index_bits;
            let mut log_current = openings.len() + chal.log_blowup;
            let mut folded_eval = Challenge::ZERO;
            let (reduced, _) =
                reconstruct_query_ro(&proof, &chal, &view, q, REC_AGG_WIDTH).expect("ro");
            let mut ro_iter = reduced.iter().peekable();
            let commit_roots = [fri0, fri1];
            let mut rounds = Vec::with_capacity(2);
            let mut fold_xs = Vec::with_capacity(2);
            for (round, opening) in openings.iter().enumerate() {
                if let Some(&&(lh, ro)) = ro_iter.peek() {
                    if lh == log_current {
                        folded_eval += ro;
                        ro_iter.next();
                    }
                }
                let sibling = opening.sibling_values[0];
                let index_in_group = index % 2;
                let mut evals = [Challenge::ZERO; 2];
                evals[index_in_group] = folded_eval;
                evals[index_in_group ^ 1] = sibling;
                let log_folded = log_current - 1;
                index >>= 1;
                let row = flatten_u32(&evals);
                let row_m31: Vec<_> = evals
                    .iter()
                    .flat_map(|e| {
                        BasedVectorSpace::<Val>::as_basis_coefficients_slice(e)
                            .iter()
                            .copied()
                    })
                    .collect();
                assert_eq!(
                    merkle_root_from_path(hash_val_leaf(&row_m31), &opening.opening_proof, index),
                    commit_roots[round],
                    "q{q} commit{round} root"
                );
                assert_eq!(bundle.commit_indices[round] as usize, index);
                rounds.push(serde_json::json!({
                    "leaf_row": row,
                    "siblings": opening.opening_proof.iter().map(|s| s.to_vec()).collect::<Vec<_>>(),
                    "index": index as u32,
                }));
                let out = fold_x_row(index, log_folded, chal.betas[round], evals[0], evals[1]);
                let t_inv = fold_x_twiddle_inv(index, log_folded);
                fold_xs.push(serde_json::json!({
                    "index": index as u32,
                    "log_h": log_folded as u32,
                    "t_inv": t_inv.as_canonical_u32(),
                    "out": limbs_u32(out),
                }));
                folded_eval = out;
                log_current = log_folded;
            }
            assert_eq!(
                folded_eval, view.fri_proof.final_poly,
                "q{q} fold_x → FinalPoly"
            );
            assert!(ro_iter.next().is_none(), "q{q} unused RO");
            chal_commit.push(serde_json::json!(rounds));

            deep_ro.push(serde_json::json!({
                "sx_trace": val_u32(pt.x),
                "sy_trace": val_u32(pt.y),
                "sx_quot": val_u32(pq.x),
                "sy_quot": val_u32(pq.y),
                "v_n_trace": val_u32(tw.v_n),
                "v_n_quot": val_u32(qw.v_n),
                "out_pre_trace0": limbs_u32(tw.deep0.out_pre),
                "out_pre_trace1": limbs_u32(tw.deep1.out_pre),
                "out_pre_quot": limbs_u32(qw.out_pre),
                "deep_out_trace": limbs_u32(tw.out),
                "deep_out_quot": limbs_u32(qw.out),
                "fold_y_short": {
                    "index": fold_ys[0].index as u32,
                    "log_h": fold_ys[0].log_folded_height as u32,
                    "t_inv": t_inv_short.as_canonical_u32(),
                    "out": limbs_u32(out_short),
                },
                "fold_y_tall": {
                    "index": fold_ys[1].index as u32,
                    "log_h": fold_ys[1].log_folded_height as u32,
                    "t_inv": t_inv_tall.as_canonical_u32(),
                    "out": limbs_u32(out_tall),
                },
                "fold_x": fold_xs,
            }));

            chal_first_layer.push(serde_json::json!({
                "tall_row": tall,
                "short_row": short,
                "siblings": fl.siblings.iter().map(|s| s.to_vec()).collect::<Vec<_>>(),
                "index": fl_idx as u32,
                "inject_after_step": 0,
            }));
        }

        let golden = serde_json::json!({
            "statement": "thick_recagg_fri_fs_auth_v0",
            "gate": "e5b-3d",
            "source": "RecursiveAggregationAir ultra-security Trace/Quot ValMmcs + Chal Mmcs + DeepRo→FL Flatten/fold_y + commit-phase fold_x→FinalPoly (W=330 N=40)",
            "measured_at": "2026-09-08",
            // locked by WQC_THICK_HUGE Compile-only remmeasure
            "approx_r1cs": 254259074,
            "rec_agg_width": REC_AGG_WIDTH,
            "quot_width": 3,
            "chal_leaf_width": 6,
            "path_depth": trace_log_height,
            "quot_path_depth": quot_log_height,
            "quot_shift": quot_shift,
            "chal_fl_shift": 1,
            "chal_fl_depth": 3,
            "chal_fl_heights": [8, 4],
            "chal_commit_shifts": [2, 3],
            "chal_commit_depths": [2, 1],
            "n": 40,
            "degree_bits": proof.degree_bits,
            "trace_root": trace_root.to_vec(),
            "quot_root": quot_root.to_vec(),
            "first_layer_root": fl_root.to_vec(),
            "fri_commit0": fri0.to_vec(),
            "fri_commit1": fri1.to_vec(),
            "query_index": &chal.query_indices[..40],
            "trace_index": trace_index,
            "quot_index": quot_index,
            "val_mmcs": val_mmcs,
            "quot_mmcs": quot_mmcs,
            "chal_first_layer": chal_first_layer,
            "chal_commit": chal_commit,
            "zeta_next": limbs_u32(zeta_next),
            "lambdas": [limbs_u32(view.lambdas[0]), limbs_u32(view.lambdas[1])],
            "at_x": limbs_u32(at_x),
            "at_y": limbs_u32(at_y),
            "atn_x": limbs_u32(atn_x),
            "atn_y": limbs_u32(atn_y),
            "deep_ro": deep_ro,
            "notes": "FriFsChal N=40 ultra + Trace/Quot ValMmcs W=330 + Chal FL/FRI-commit + DeepRo Flatten/fold_y + commit fold_x→FinalPoly; approx_r1cs locked by WQC_THICK_HUGE Compile-only remmeasure (2026-09-08, ~44.9min); ≡verify_root_proof deferred"
        });

        let out = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../fixtures/e5b/wrap_recagg_fri_fs_auth_golden.json");
        std::fs::write(&out, serde_json::to_string_pretty(&golden).unwrap()).expect("write");
        let wrap = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../wqc-snark-wrap/fixtures/e5b3/wrap_recagg_fri_fs_auth_golden.json");
        if let Some(parent) = wrap.parent() {
            if parent.exists() {
                let _ = std::fs::write(&wrap, serde_json::to_string_pretty(&golden).unwrap());
            }
        }
    }

    #[test]
    fn lock_recagg_fri_fs_auth_golden() {
        use p3_commit::{Pcs, PolynomialSpace};
        use p3_field::PrimeField32;

        use crate::plonky3_stark::recursion::air::{REC_AGG_WIDTH, REC_KIND_LEAF};
        use crate::plonky3_stark::recursion::child_binding::STARK_DIGEST_LEN;
        use crate::plonky3_stark::recursion::context::RecursiveAggregationContext;
        use crate::plonky3_stark::recursion::deep_ro_native::{
            deep_ro_recagg_trace_witness, deep_ro_w3_witness,
        };
        use crate::plonky3_stark::recursion::fri_fold_native::{
            cfft_permute_index, challenge_to_limbs, standard_nth_point,
        };
        use crate::plonky3_stark::recursion::fri_ro::{decode_input_proof, reconstruct_query_ro};
        use crate::plonky3_stark::recursion::prove::generate_recursive_aggregation_proof;
        use crate::plonky3_stark::recursion::transcript_v6::decode_rec_agg_proof_owned_v6;

        let golden_path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../fixtures/e5b/wrap_recagg_fri_fs_auth_golden.json"
        );
        let raw =
            std::fs::read_to_string(golden_path).expect("wrap_recagg_fri_fs_auth_golden.json");
        let v: serde_json::Value = serde_json::from_str(&raw).expect("golden json");
        assert_eq!(
            v["statement"].as_str().unwrap(),
            "thick_recagg_fri_fs_auth_v0"
        );
        assert_eq!(v["rec_agg_width"].as_u64().unwrap() as usize, REC_AGG_WIDTH);
        assert_eq!(v["quot_width"].as_u64().unwrap(), 3);
        assert_eq!(v["n"].as_u64().unwrap(), 40);
        assert_eq!(v["path_depth"].as_u64().unwrap(), 3);
        assert_eq!(v["quot_path_depth"].as_u64().unwrap(), 4);
        assert_eq!(v["quot_shift"].as_u64().unwrap(), 0);
        assert_eq!(v["chal_leaf_width"].as_u64().unwrap(), 6);
        assert_eq!(v["chal_fl_shift"].as_u64().unwrap(), 1);
        assert_eq!(v["chal_fl_depth"].as_u64().unwrap(), 3);
        assert_eq!(v["chal_first_layer"].as_array().unwrap().len(), 40);
        assert_eq!(v["chal_commit"].as_array().unwrap().len(), 40);
        assert_eq!(v["deep_ro"].as_array().unwrap().len(), 40);
        assert_eq!(v["lambdas"].as_array().unwrap().len(), 2);
        assert_eq!(v["zeta_next"].as_array().unwrap().len(), 3);
        for q in 0..40 {
            let fx = v["deep_ro"][q]["fold_x"].as_array().expect("fold_x");
            assert_eq!(fx.len(), 2);
            assert_eq!(fx[0]["log_h"].as_u64().unwrap(), 2);
            assert_eq!(fx[1]["log_h"].as_u64().unwrap(), 1);
        }
        // approx_r1cs locked by WQC_THICK_HUGE Compile-only remmeasure (N=40 RecAgg ultra)
        assert_eq!(v["approx_r1cs"].as_u64().unwrap(), 254259074);

        let ctx = RecursiveAggregationContext {
            parent_task_id: "parent",
            compose_label: "root",
            manifest_root_hash: "m",
            left_child_hash: [1u8; CHILD_HASH_LEN],
            right_child_hash: [2u8; CHILD_HASH_LEN],
            left_stark_digest: [3u8; STARK_DIGEST_LEN],
            right_stark_digest: [4u8; STARK_DIGEST_LEN],
            left_kind: REC_KIND_LEAF,
            right_kind: REC_KIND_LEAF,
            left_agg_cert: None,
            right_agg_cert: None,
            left_leaf_bundle: None,
            right_leaf_bundle: None,
            security_level: "ultra",
        };
        let transcript = generate_recursive_aggregation_proof(&ctx).expect("prove");
        let plonky3 = decode_rec_agg_proof_owned_v6(&transcript, &ctx).expect("decode v6");
        let proof: Proof<WqcStarkConfig> = postcard::from_bytes(&plonky3).expect("postcard");
        let chal = replay_rec_agg_fri_challenges(&proof).expect("replay");
        let view = decode_pcs_view(&proof).expect("pcs");
        let config = circle_config_matching_proof(&proof).expect("cfg");
        let pcs = config.pcs();
        let degree = 1usize << proof.degree_bits;
        let init_trace_domain = <crate::plonky3_stark::config::Pcs as Pcs<
            Challenge,
            crate::plonky3_stark::config::Challenger,
        >>::natural_domain_for_degree(pcs, degree);
        let log_blowup = chal.log_blowup;
        let log_global_max_height = view.fri_proof.commit_phase_commits.len() + log_blowup + 1;
        let trace_height = init_trace_domain.size() << log_blowup;
        let trace_log_height = trace_height.trailing_zeros() as usize;
        let y_shift = log_global_max_height - trace_log_height;
        let num_quot = proof.opened_values.quotient_chunks.len();
        let log_num_quot = num_quot.trailing_zeros() as usize;
        let quot_parent =
            init_trace_domain.create_disjoint_domain(1usize << (proof.degree_bits + log_num_quot));
        let quot_chunk_domains = quot_parent.split_domains(num_quot);
        let quot_h = quot_chunk_domains[0].size() << log_blowup;
        let quot_log_height = quot_h.trailing_zeros() as usize;
        let quot_shift = log_global_max_height - quot_log_height;
        let trace_root = *proof.commitments.trace.roots().first().expect("trace root");
        let quot_root = *proof
            .commitments
            .quotient_chunks
            .roots()
            .first()
            .expect("quot root");
        let zeta_next = init_trace_domain.next_point(chal.zeta).expect("zeta_next");

        let bytes = |key: &str| -> Vec<u8> {
            v[key]
                .as_array()
                .unwrap()
                .iter()
                .map(|x| x.as_u64().unwrap() as u8)
                .collect()
        };
        assert_eq!(bytes("trace_root").as_slice(), trace_root.as_slice());
        assert_eq!(bytes("quot_root").as_slice(), quot_root.as_slice());

        let qis = v["query_index"].as_array().unwrap();
        let tis = v["trace_index"].as_array().unwrap();
        let qis_mmcs = v["quot_index"].as_array().unwrap();
        let paths = v["val_mmcs"].as_array().unwrap();
        let quot_paths = v["quot_mmcs"].as_array().unwrap();
        let deep_ros = v["deep_ro"].as_array().unwrap();
        assert_eq!(paths.len(), 40);
        assert_eq!(quot_paths.len(), 40);

        let limbs_u32 = |c: Challenge| -> Vec<u32> {
            challenge_to_limbs(c)
                .iter()
                .map(|x| x.as_canonical_u32())
                .collect()
        };
        let trace_next = proof.opened_values.trace_next.as_ref().expect("trace_next");
        let mut pz_local = [Challenge::ZERO; REC_AGG_WIDTH];
        let mut pz_next = [Challenge::ZERO; REC_AGG_WIDTH];
        pz_local[..REC_AGG_WIDTH]
            .copy_from_slice(&proof.opened_values.trace_local[..REC_AGG_WIDTH]);
        pz_next[..REC_AGG_WIDTH].copy_from_slice(&trace_next[..REC_AGG_WIDTH]);
        let mut pz_quot = [Challenge::ZERO; 3];
        pz_quot.copy_from_slice(&proof.opened_values.quotient_chunks[0][..3]);

        for q in 0..40 {
            let qi = chal.query_indices[q];
            assert_eq!(qis[q].as_u64().unwrap() as usize, qi);
            let t_idx = qi >> y_shift;
            let q_idx = qi >> quot_shift;
            assert_eq!(tis[q].as_u64().unwrap() as usize, t_idx);
            assert_eq!(qis_mmcs[q].as_u64().unwrap() as usize, q_idx);
            let input =
                decode_input_proof(&view.fri_proof.query_proofs[q].input_proof).expect("input");
            let row = &input.input_openings[0].opened_values[0];
            let quot_row = &input.input_openings[1].opened_values[0];
            let leaf_row: Vec<u32> = paths[q]["leaf_row"]
                .as_array()
                .unwrap()
                .iter()
                .map(|x| x.as_u64().unwrap() as u32)
                .collect();
            assert_eq!(leaf_row.len(), REC_AGG_WIDTH);
            for (a, b) in leaf_row.iter().zip(row.iter()) {
                assert_eq!(*a, b.as_canonical_u32());
            }
            let q_leaf: Vec<u32> = quot_paths[q]["leaf_row"]
                .as_array()
                .unwrap()
                .iter()
                .map(|x| x.as_u64().unwrap() as u32)
                .collect();
            assert_eq!(q_leaf.len(), 3);
            for (a, b) in q_leaf.iter().zip(quot_row.iter()) {
                assert_eq!(*a, b.as_canonical_u32());
            }
            let check_sibs = |json: &serde_json::Value, proof: &[[u8; 32]], depth: usize| {
                let sibs = json["siblings"].as_array().unwrap();
                assert_eq!(sibs.len(), depth);
                assert_eq!(sibs.len(), proof.len());
                for (i, sib) in sibs.iter().enumerate() {
                    let b: Vec<u8> = sib
                        .as_array()
                        .unwrap()
                        .iter()
                        .map(|x| x.as_u64().unwrap() as u8)
                        .collect();
                    assert_eq!(b.as_slice(), proof[i].as_slice());
                }
            };
            check_sibs(
                &paths[q],
                &input.input_openings[0].opening_proof,
                trace_log_height,
            );
            check_sibs(
                &quot_paths[q],
                &input.input_openings[1].opening_proof,
                quot_log_height,
            );
            assert_eq!(
                merkle_root_from_path(
                    hash_val_leaf(row),
                    &input.input_openings[0].opening_proof,
                    t_idx
                ),
                trace_root
            );
            assert_eq!(
                merkle_root_from_path(
                    hash_val_leaf(quot_row),
                    &input.input_openings[1].opening_proof,
                    q_idx
                ),
                quot_root
            );

            // DeepRo consistency vs golden out limbs.
            let mut px_trace = [Val::ZERO; REC_AGG_WIDTH];
            px_trace.copy_from_slice(&row[..REC_AGG_WIDTH]);
            let mut px_quot = [Val::ZERO; 3];
            px_quot.copy_from_slice(&quot_row[..3]);
            let orig_t = cfft_permute_index(qi >> y_shift, trace_log_height);
            let pt = standard_nth_point(trace_log_height, orig_t);
            let orig_q = cfft_permute_index(qi >> quot_shift, quot_log_height);
            let pq = standard_nth_point(quot_log_height, orig_q);
            let tw = deep_ro_recagg_trace_witness(
                chal.batch_alpha,
                pt.x,
                pt.y,
                chal.zeta,
                zeta_next,
                &px_trace,
                &pz_local,
                &pz_next,
                view.lambdas[0],
                proof.degree_bits,
            )
            .expect("deep_ro");
            let qw = deep_ro_w3_witness(
                chal.batch_alpha,
                pq.x,
                pq.y,
                chal.zeta,
                px_quot,
                pz_quot,
                view.lambdas[1],
                proof.degree_bits + 1,
            );
            let g_out_t: Vec<u32> = deep_ros[q]["deep_out_trace"]
                .as_array()
                .unwrap()
                .iter()
                .map(|x| x.as_u64().unwrap() as u32)
                .collect();
            let g_out_q: Vec<u32> = deep_ros[q]["deep_out_quot"]
                .as_array()
                .unwrap()
                .iter()
                .map(|x| x.as_u64().unwrap() as u32)
                .collect();
            assert_eq!(g_out_t, limbs_u32(tw.out));
            assert_eq!(g_out_q, limbs_u32(qw.out));
            let (_, fold_ys) =
                reconstruct_query_ro(&proof, &chal, &view, q, REC_AGG_WIDTH).expect("ro");
            let pair_short = (qi >> y_shift) & 1;
            let pair_tall = (qi >> quot_shift) & 1;
            let lc_short = if pair_short == 0 {
                fold_ys[0].v0
            } else {
                fold_ys[0].v1
            };
            let lc_tall = if pair_tall == 0 {
                fold_ys[1].v0
            } else {
                fold_ys[1].v1
            };
            assert_eq!(tw.out, lc_short);
            assert_eq!(qw.out, lc_tall);
        }
    }

    #[test]
    fn emit_leaf_fri_fs_auth_golden() {
        use p3_commit::{Pcs, PolynomialSpace};
        use p3_field::PrimeField32;
        use std::path::PathBuf;

        use crate::plonky3_stark::generate_plonky3_proof;
        use crate::plonky3_stark::recursion::fri_ro::{decode_input_proof, reconstruct_query_ro};
        use crate::plonky3_stark::recursion::pcs_geom::UNITARY_TRACE_WIDTH;
        use crate::plonky3_stark::transcript_v2::decode_proof_v2_plonky3_bytes;
        use crate::trace_spec::idle_qubit0_trace;
        use crate::transcript::StarkContext;

        let ctx = StarkContext {
            circuit_id: "c-leaf",
            sub_task_id: "sub-leaf-fri-fs-auth",
            node_id: "n1",
            slice_id: "0",
            output_hash: "out",
            terminal_statevector_digest: "",
            measurement_spec_hash: "",
            security_level: "low",
        };
        let trace = idle_qubit0_trace();
        let transcript = generate_plonky3_proof(&ctx, &trace).expect("prove");
        let plonky3 = decode_proof_v2_plonky3_bytes(&transcript, &ctx).expect("decode");
        let proof: Proof<WqcStarkConfig> = postcard::from_bytes(&plonky3).expect("postcard");
        let chal = replay_fri_challenges(&proof, UNITARY_TRACE_WIDTH).expect("replay");
        assert_eq!(proof.opened_values.trace_local.len(), UNITARY_TRACE_WIDTH);
        assert_eq!(chal.query_indices.len(), 8, "low ladder FRI queries");
        assert_eq!(chal.log_blowup, 1);

        let view = decode_pcs_view(&proof).expect("pcs");
        let config = circle_config_matching_proof(&proof).expect("cfg");
        let pcs = config.pcs();
        let degree = 1usize << proof.degree_bits;
        let init_trace_domain = <crate::plonky3_stark::config::Pcs as Pcs<
            Challenge,
            crate::plonky3_stark::config::Challenger,
        >>::natural_domain_for_degree(pcs, degree);
        let log_blowup = chal.log_blowup;
        let commit_rounds = view.fri_proof.commit_phase_commits.len();
        let log_global_max_height = commit_rounds + log_blowup + 1;
        let trace_height = init_trace_domain.size() << log_blowup;
        assert!(trace_height.is_power_of_two());
        let trace_log_height = trace_height.trailing_zeros() as usize;
        let y_shift = log_global_max_height - trace_log_height;
        let num_index_bits = chal.fri_log_max_height + chal.extra_query_index_bits;
        let num_quot = proof.opened_values.quotient_chunks.len();

        let (_, fold_ys0) =
            reconstruct_query_ro(&proof, &chal, &view, 0, UNITARY_TRACE_WIDTH).expect("ro q0");
        let input0 =
            decode_input_proof(&view.fri_proof.query_proofs[0].input_proof).expect("input");
        // Prefer full Auth only when Agg-like: single quot chunk + measurable two-matrix FL.
        let full_auth_geometry = num_quot == 1 && fold_ys0.len() == 2;

        let qi = chal.query_indices[0];
        let trace_open = &input0.input_openings[0];
        let row = &trace_open.opened_values[0];
        assert_eq!(row.len(), UNITARY_TRACE_WIDTH);
        let t_idx = qi >> y_shift;
        let trace_root = *proof.commitments.trace.roots().first().expect("trace root");
        assert_eq!(
            merkle_root_from_path(hash_val_leaf(row), &trace_open.opening_proof, t_idx),
            trace_root,
            "q0 Unitary Trace ValMmcs root"
        );
        assert_eq!(trace_open.opening_proof.len(), trace_log_height);
        assert!(
            trace_log_height <= 4,
            "wrap ThickMmcsMaxDepth=4; got {trace_log_height}"
        );

        // Idle multi-chunk Quot ValMmcs: equal-height concat batch (16×EF3 → W=48).
        assert_eq!(num_quot, 16, "idle unitary num_quot");
        let log_num_quot = num_quot.trailing_zeros() as usize;
        let quot_parent =
            init_trace_domain.create_disjoint_domain(1usize << (proof.degree_bits + log_num_quot));
        let quot_chunk_domains = quot_parent.split_domains(num_quot);
        let quot_h = quot_chunk_domains[0].size() << log_blowup;
        assert!(quot_h.is_power_of_two());
        let quot_log_height = quot_h.trailing_zeros() as usize;
        let quot_shift = log_global_max_height - quot_log_height;
        assert_eq!(quot_h, 8);
        assert_eq!(quot_log_height, 3);
        assert_eq!(quot_shift, 0, "idle Quot ValMmcs index shift");
        assert!(
            quot_log_height <= 4,
            "wrap ThickMmcsMaxDepth=4; got {quot_log_height}"
        );

        let quot_open = &input0.input_openings[1];
        assert_eq!(quot_open.opened_values.len(), num_quot);
        let mut quot_concat = Vec::with_capacity(num_quot * 3);
        for qrow in &quot_open.opened_values {
            assert_eq!(qrow.len(), 3, "EF_DIM");
            quot_concat.extend_from_slice(qrow);
        }
        assert_eq!(quot_concat.len(), 48, "16×EF3 concat leaf");
        let q_idx = qi >> quot_shift;
        let quot_root = *proof
            .commitments
            .quotient_chunks
            .roots()
            .first()
            .expect("quot root");
        assert_eq!(
            merkle_root_from_path(hash_val_leaf(&quot_concat), &quot_open.opening_proof, q_idx),
            quot_root,
            "q0 Unitary Quot ValMmcs batch root"
        );
        assert_eq!(quot_open.opening_proof.len(), quot_log_height);

        let notes = if full_auth_geometry {
            "Unitary leaf FriFsAuth N=1 full spine (single quot + two-matrix FL)"
        } else {
            "Unitary Trace ValMmcs N=1 + Quot ValMmcs concat batch W=48 (num_quot=16); Chal/FL/DeepRo/fold deferred — Partial leaf FriFsAuth"
        };

        let golden = serde_json::json!({
            "statement": "thick_leaf_fri_fs_auth_v0",
            "gate": "e5b-3d",
            "source": "idle_qubit0_trace UnitaryAir low-security Trace+Quot ValMmcs query 0 (FS-bound)",
            "measured_at": "2026-09-09",
            // Locked by Go CompileThickLeafFriFsAuth remmeasure (Trace+Quot W=48).
            "approx_r1cs": 1108267,
            "n": 1,
            "leaf_width": UNITARY_TRACE_WIDTH,
            "quot_width": 48,
            "degree_bits": proof.degree_bits,
            "log_blowup": log_blowup,
            "fri_log_max_height": chal.fri_log_max_height,
            "extra_query_index_bits": chal.extra_query_index_bits,
            "num_index_bits": num_index_bits,
            "y_shift": y_shift,
            "quot_shift": quot_shift,
            "path_depth": trace_log_height,
            "quot_path_depth": quot_log_height,
            "num_quot": num_quot,
            "fold_ys_len": fold_ys0.len(),
            "fl_siblings_len": input0.first_layer_siblings.len(),
            "commit_rounds": commit_rounds,
            "full_auth_geometry": full_auth_geometry,
            "query_index": qi as u32,
            "trace_index": t_idx as u32,
            "quot_index": q_idx as u32,
            "trace_root": trace_root.to_vec(),
            "quot_root": quot_root.to_vec(),
            "leaf_row": row.iter().map(|x| x.as_canonical_u32()).collect::<Vec<_>>(),
            "siblings": trace_open.opening_proof.iter().map(|s| s.to_vec()).collect::<Vec<_>>(),
            "quot_leaf_row": quot_concat.iter().map(|x| x.as_canonical_u32()).collect::<Vec<_>>(),
            "quot_siblings": quot_open.opening_proof.iter().map(|s| s.to_vec()).collect::<Vec<_>>(),
            "deferred": if full_auth_geometry {
                serde_json::json!([])
            } else {
                serde_json::json!([
                    "FriFsChal",
                    "FL / Chal commit",
                    "DeepRo",
                    "fold_y / fold_x"
                ])
            },
            "notes": notes
        });

        let out = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../fixtures/e5b/wrap_leaf_fri_fs_auth_golden.json");
        std::fs::write(&out, serde_json::to_string_pretty(&golden).unwrap()).expect("write");
        let wrap = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../wqc-snark-wrap/fixtures/e5b3/wrap_leaf_fri_fs_auth_golden.json");
        if let Some(parent) = wrap.parent() {
            if parent.exists() {
                let _ = std::fs::write(&wrap, serde_json::to_string_pretty(&golden).unwrap());
            }
        }
    }

    #[test]
    #[allow(clippy::bool_assert_comparison)]
    fn lock_leaf_fri_fs_auth_golden() {
        use p3_mersenne_31::Mersenne31 as Val;

        use crate::plonky3_stark::recursion::pcs_geom::UNITARY_TRACE_WIDTH;

        let golden_path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../fixtures/e5b/wrap_leaf_fri_fs_auth_golden.json"
        );
        let raw = std::fs::read_to_string(golden_path).expect("wrap_leaf_fri_fs_auth_golden.json");
        let v: serde_json::Value = serde_json::from_str(&raw).expect("golden json");
        assert_eq!(
            v["statement"].as_str().unwrap(),
            "thick_leaf_fri_fs_auth_v0"
        );
        assert_eq!(v["n"].as_u64().unwrap(), 1);
        assert_eq!(
            v["leaf_width"].as_u64().unwrap() as usize,
            UNITARY_TRACE_WIDTH
        );
        assert_eq!(v["quot_width"].as_u64().unwrap(), 48);

        let y_shift = v["y_shift"].as_u64().unwrap() as usize;
        let quot_shift = v["quot_shift"].as_u64().unwrap() as usize;
        let qi = v["query_index"].as_u64().unwrap() as usize;
        let t_idx = v["trace_index"].as_u64().unwrap() as usize;
        let q_idx = v["quot_index"].as_u64().unwrap() as usize;
        assert_eq!(qi >> y_shift, t_idx);
        assert_eq!(qi >> quot_shift, q_idx);

        fn digest_path(v: &serde_json::Value, key: &str) -> Vec<[u8; 32]> {
            v[key]
                .as_array()
                .unwrap()
                .iter()
                .map(|s| {
                    let bytes: Vec<u8> = s
                        .as_array()
                        .unwrap()
                        .iter()
                        .map(|b| b.as_u64().unwrap() as u8)
                        .collect();
                    bytes.try_into().expect("sib 32")
                })
                .collect()
        }
        fn digest32(v: &serde_json::Value, key: &str) -> [u8; 32] {
            v[key]
                .as_array()
                .unwrap()
                .iter()
                .map(|b| b.as_u64().unwrap() as u8)
                .collect::<Vec<_>>()
                .try_into()
                .expect("root 32")
        }
        fn m31_row(v: &serde_json::Value, key: &str) -> Vec<Val> {
            v[key]
                .as_array()
                .unwrap()
                .iter()
                .map(|x| Val::from_u32(x.as_u64().unwrap() as u32))
                .collect()
        }

        let row = m31_row(&v, "leaf_row");
        assert_eq!(row.len(), UNITARY_TRACE_WIDTH);
        let siblings = digest_path(&v, "siblings");
        let root = digest32(&v, "trace_root");
        assert_eq!(
            merkle_root_from_path(hash_val_leaf(&row), &siblings, t_idx),
            root
        );
        assert_eq!(siblings.len(), v["path_depth"].as_u64().unwrap() as usize);

        let quot_row = m31_row(&v, "quot_leaf_row");
        assert_eq!(quot_row.len(), 48);
        let quot_siblings = digest_path(&v, "quot_siblings");
        let quot_root = digest32(&v, "quot_root");
        assert_eq!(
            merkle_root_from_path(hash_val_leaf(&quot_row), &quot_siblings, q_idx),
            quot_root
        );
        assert_eq!(
            quot_siblings.len(),
            v["quot_path_depth"].as_u64().unwrap() as usize
        );
        // Remeasured after Go CompileThickLeafFriFsAuth (Trace W=21 + Quot W=48).
        assert_eq!(v["approx_r1cs"].as_u64().unwrap(), 1108267);
        assert_eq!(v["full_auth_geometry"].as_bool().unwrap(), false);
        assert_eq!(v["num_quot"].as_u64().unwrap(), 16);
        assert_eq!(v["fold_ys_len"].as_u64().unwrap(), 1);
        assert_eq!(v["y_shift"].as_u64().unwrap(), 0);
        assert_eq!(v["quot_shift"].as_u64().unwrap(), 0);
        assert_eq!(v["path_depth"].as_u64().unwrap(), 3);
        assert_eq!(v["quot_path_depth"].as_u64().unwrap(), 3);
        assert_eq!(v["commit_rounds"].as_u64().unwrap(), 1);
        let deferred = v["deferred"].as_array().unwrap();
        assert!(deferred
            .iter()
            .all(|d| d.as_str().unwrap() != "Quot ValMmcs"));
    }
}

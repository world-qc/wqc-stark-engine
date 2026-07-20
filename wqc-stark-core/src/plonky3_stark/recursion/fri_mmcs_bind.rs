//! R3-M3d: prove/bind FRI ValMmcs + ChallengeMmcs paths for AggregationAir.

use p3_commit::{Mmcs, Pcs, PolynomialSpace};
use p3_field::PrimeCharacteristicRing;
use p3_matrix::Dimensions;
use p3_mersenne_31::Mersenne31;
use p3_uni_stark::{Proof, StarkGenericConfig};

use crate::plonky3_stark::aggregation_air::AGG_WIDTH;
use crate::plonky3_stark::config::{
    devnet_circle_config, Challenge, ChallengeMmcs, Val, ValMmcs, WqcStarkConfig,
};

use super::fri_fold_bind::AGG_FRI_PROVEN_QUERIES;
use super::fri_fold_native::{challenge_to_limbs, fold_x_row};
use super::fri_fs_replay::{decode_pcs_view, replay_agg_fri_challenges};
use super::fri_mmcs_path::{
    generate_fri_mmcs_path_proof, verify_fri_mmcs_path_proof, FriMmcsPathProof, FRI_MMCS_MAX_DEPTH,
};
use super::fri_ro::{decode_input_proof, reconstruct_agg_query_ro};
use super::keccak256_air::{
    prove_compress, prove_val_leaf, verify_compress_digest, verify_val_leaf_digest,
    Keccak256StarkProof,
};
use super::keccak_f_native::keccak256_compress;
use super::merkle_keccak::hash_val_leaf;

fn log2_strict(n: usize) -> Result<usize, String> {
    if n == 0 || !n.is_power_of_two() {
        return Err(format!("expected power-of-two height, got {n}"));
    }
    Ok(n.trailing_zeros() as usize)
}

fn commitment_root_val(com: &<ValMmcs as Mmcs<Val>>::Commitment) -> Result<[u8; 32], String> {
    com.roots()
        .first()
        .copied()
        .ok_or_else(|| "empty ValMmcs MerkleCap".into())
}

fn commitment_root_chal(
    com: &<ChallengeMmcs as Mmcs<Challenge>>::Commitment,
) -> Result<[u8; 32], String> {
    com.roots()
        .first()
        .copied()
        .ok_or_else(|| "empty ChallengeMmcs MerkleCap".into())
}

fn flatten_challenge_row(evals: &[Challenge]) -> Vec<Mersenne31> {
    let mut out = Vec::with_capacity(evals.len() * 3);
    for &e in evals {
        out.extend_from_slice(&challenge_to_limbs(e));
    }
    out
}

const EF_DIM: usize = 3;
const CHAL_LEAF_WIDTH: usize = 2 * EF_DIM; // 6

/// Per-query ValMmcs paths (trace + quotient).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FriValMmcsQueryProof {
    pub trace_index: u32,
    pub quot_index: u32,
    pub trace_siblings: Vec<[u8; 32]>,
    pub quot_siblings: Vec<[u8; 32]>,
    pub trace_path: FriMmcsPathProof,
    pub quot_path: FriMmcsPathProof,
}

/// First-layer ChallengeMmcs multi-matrix path (binary, cap_height=0).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FriChalBatchPathProof {
    pub index: u32,
    pub siblings: Vec<[u8; 32]>,
    /// Leaf Keccak for each matrix (tallest-first order), flattened Val rows.
    pub leaf_rows: Vec<Vec<Mersenne31>>,
    pub leaf_keccs: Vec<Keccak256StarkProof>,
    pub leaf_digests: Vec<[u8; 32]>,
    /// Sibling-layer compress STARKs (one per proof sibling).
    pub sib_compresses: Vec<Keccak256StarkProof>,
    pub sib_layer_digests: Vec<[u8; 32]>,
    /// Injection compress STARKs (when a shorter matrix joins).
    pub inject_compresses: Vec<Keccak256StarkProof>,
    pub inject_digests: Vec<[u8; 32]>,
    pub inject_leaf_indices: Vec<u32>,
}

/// Per-query ChallengeMmcs: first-layer batch + commit-phase single paths.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FriChalMmcsQueryProof {
    pub first_layer: FriChalBatchPathProof,
    pub commit_indices: Vec<u32>,
    pub commit_siblings: Vec<Vec<[u8; 32]>>,
    pub commit_paths: Vec<FriMmcsPathProof>,
}

#[derive(Debug, Clone)]
pub struct AggFriMmcsBundle {
    pub val: Vec<FriValMmcsQueryProof>,
    pub chal: Vec<FriChalMmcsQueryProof>,
}

/// Prove binary multi-matrix Mmcs path matching Plonky3 MerkleTreeMmcs (N=2, cap=0).
fn generate_chal_batch_path(
    opened_vals: &[Vec<Mersenne31>],
    dimensions: &[Dimensions],
    mut index: usize,
    siblings: &[[u8; 32]],
    expected_root: &[u8; 32],
) -> Result<FriChalBatchPathProof, String> {
    if dimensions.len() != opened_vals.len() || dimensions.is_empty() {
        return Err("batch shape mismatch".into());
    }
    if siblings.len() > FRI_MMCS_MAX_DEPTH {
        return Err("too many batch siblings".into());
    }
    let max_height = dimensions
        .iter()
        .map(|d| d.height)
        .max()
        .ok_or_else(|| "empty dims".to_string())?;
    if !max_height.is_power_of_two() {
        return Err("max height not power of two".into());
    }
    if index >= max_height {
        return Err("index out of bounds".into());
    }

    // Sort matrix indices tallest-first (stable by original index).
    let mut order: Vec<usize> = (0..dimensions.len()).collect();
    order.sort_by_key(|&i| std::cmp::Reverse(dimensions[i].height));

    let mut leaf_rows = Vec::new();
    let mut leaf_keccs = Vec::new();
    let mut leaf_digests = Vec::new();
    for &i in &order {
        if opened_vals[i].len() != dimensions[i].width {
            return Err("opened width mismatch".into());
        }
        let k = prove_val_leaf(&opened_vals[i])?;
        if k.digest != hash_val_leaf(&opened_vals[i]) {
            return Err("batch leaf digest mismatch".into());
        }
        leaf_rows.push(opened_vals[i].clone());
        leaf_digests.push(k.digest);
        leaf_keccs.push(k);
    }

    // Map original matrix index -> leaf digest index in tallest-first list.
    let mut digest_of = vec![0usize; dimensions.len()];
    for (pos, &i) in order.iter().enumerate() {
        digest_of[i] = pos;
    }

    let leaf_height_npt = max_height.next_power_of_two();
    let mut remaining: Vec<usize> = order.clone();
    let mut at_leaf: Vec<usize> = Vec::new();
    remaining.retain(|&i| {
        if dimensions[i].height.next_power_of_two() == leaf_height_npt {
            at_leaf.push(i);
            false
        } else {
            true
        }
    });
    // Initial digest = H(concat rows at max height) — FieldHash over concatenated slices.
    let mut concat: Vec<Mersenne31> = Vec::new();
    for &i in &at_leaf {
        concat.extend_from_slice(&opened_vals[i]);
    }
    let mut digest = hash_val_leaf(&concat);
    // Prove concat leaf if multi-row at same height; else reuse single leaf digest.
    if at_leaf.len() == 1 {
        digest = leaf_digests[digest_of[at_leaf[0]]];
    } else {
        let k = prove_val_leaf(&concat)?;
        if k.digest != digest {
            return Err("multi-leaf hash mismatch".into());
        }
        // Track as extra leaf (append).
        leaf_rows.push(concat);
        leaf_digests.push(k.digest);
        leaf_keccs.push(k);
    }

    let mut sib_compresses = Vec::new();
    let mut sib_layer_digests = Vec::new();
    let mut inject_compresses = Vec::new();
    let mut inject_digests = Vec::new();
    let mut inject_leaf_indices = Vec::new();
    let mut proof_pos = 0usize;
    let mut curr_height = max_height;
    let expected_steps = log2_strict(max_height)?;

    for _step in 0..expected_steps {
        if proof_pos >= siblings.len() {
            return Err("ran out of siblings".into());
        }
        let sib = siblings[proof_pos];
        proof_pos += 1;
        let (left, right) = if index.is_multiple_of(2) {
            (digest, sib)
        } else {
            (sib, digest)
        };
        let c = prove_compress(left, right)?;
        if c.digest != keccak256_compress(left, right) {
            return Err("sib compress mismatch".into());
        }
        digest = c.digest;
        sib_layer_digests.push(digest);
        sib_compresses.push(c);
        index /= 2;
        curr_height /= 2;

        // Inject matrices whose height matches curr_height.
        let inject_idxs: Vec<usize> = remaining
            .iter()
            .copied()
            .filter(|&i| dimensions[i].height == curr_height)
            .collect();
        if !inject_idxs.is_empty() {
            remaining.retain(|i| !inject_idxs.contains(i));
            let mut inj_concat = Vec::new();
            for &i in &inject_idxs {
                inj_concat.extend_from_slice(&opened_vals[i]);
            }
            let inj_digest = if inject_idxs.len() == 1 {
                leaf_digests[digest_of[inject_idxs[0]]]
            } else {
                let k = prove_val_leaf(&inj_concat)?;
                if k.digest != hash_val_leaf(&inj_concat) {
                    return Err("inject leaf mismatch".into());
                }
                leaf_rows.push(inj_concat);
                leaf_digests.push(k.digest);
                leaf_keccs.push(k);
                leaf_digests[leaf_digests.len() - 1]
            };
            let c = prove_compress(digest, inj_digest)?;
            if c.digest != keccak256_compress(digest, inj_digest) {
                return Err("inject compress mismatch".into());
            }
            digest = c.digest;
            inject_digests.push(digest);
            inject_compresses.push(c);
            inject_leaf_indices.push(digest_of[inject_idxs[0]] as u32);
        }
    }
    if proof_pos != siblings.len() {
        return Err(format!(
            "sibling count mismatch: used {proof_pos}, have {}",
            siblings.len()
        ));
    }
    if &digest != expected_root {
        return Err("batch root mismatch".into());
    }
    Ok(FriChalBatchPathProof {
        index: index as u32, // after walk this is cap index (0)
        siblings: siblings.to_vec(),
        leaf_rows,
        leaf_keccs,
        leaf_digests,
        sib_compresses,
        sib_layer_digests,
        inject_compresses,
        inject_digests,
        inject_leaf_indices,
    })
}

fn verify_chal_batch_path_replay(
    opened_vals: &[Vec<Mersenne31>],
    dimensions: &[Dimensions],
    mut index: usize,
    expected_root: &[u8; 32],
    proof: &FriChalBatchPathProof,
) -> bool {
    if dimensions.len() != opened_vals.len() {
        return false;
    }
    let max_height = match dimensions.iter().map(|d| d.height).max() {
        Some(h) if h.is_power_of_two() => h,
        _ => return false,
    };
    if index >= max_height || proof.siblings.len() != log2_strict(max_height).unwrap_or(0) {
        // sibling count == log2(max_height) for power-of-two single tree; AggAir first-layer = 3.
    }
    let mut order: Vec<usize> = (0..dimensions.len()).collect();
    order.sort_by_key(|&i| std::cmp::Reverse(dimensions[i].height));
    if proof.leaf_keccs.len() < dimensions.len() {
        return false;
    }
    for (i, &oi) in order.iter().enumerate() {
        if i >= proof.leaf_rows.len()
            || proof.leaf_rows[i].as_slice() != opened_vals[oi].as_slice()
            || !verify_val_leaf_digest(
                &proof.leaf_rows[i],
                &proof.leaf_digests[i],
                &proof.leaf_keccs[i],
            )
        {
            eprintln!("[FriChalBatch] leaf {i}");
            return false;
        }
    }
    let mut digest_of = vec![0usize; dimensions.len()];
    for (pos, &i) in order.iter().enumerate() {
        digest_of[i] = pos;
    }
    let leaf_height_npt = max_height.next_power_of_two();
    let mut remaining: Vec<usize> = order.clone();
    let mut at_leaf = Vec::new();
    remaining.retain(|&i| {
        if dimensions[i].height.next_power_of_two() == leaf_height_npt {
            at_leaf.push(i);
            false
        } else {
            true
        }
    });
    let mut digest = if at_leaf.len() == 1 {
        proof.leaf_digests[digest_of[at_leaf[0]]]
    } else {
        let mut concat = Vec::new();
        for &i in &at_leaf {
            concat.extend_from_slice(&opened_vals[i]);
        }
        // Find matching extra leaf in proof
        let expect = hash_val_leaf(&concat);
        let mut found = None;
        for i in dimensions.len()..proof.leaf_rows.len() {
            if proof.leaf_digests[i] == expect
                && verify_val_leaf_digest(
                    &proof.leaf_rows[i],
                    &proof.leaf_digests[i],
                    &proof.leaf_keccs[i],
                )
            {
                found = Some(expect);
                break;
            }
        }
        match found {
            Some(d) => d,
            None => {
                eprintln!("[FriChalBatch] multi leaf");
                return false;
            }
        }
    };

    let mut sib_i = 0usize;
    let mut inj_i = 0usize;
    let mut curr_height = max_height;
    let steps = match log2_strict(max_height) {
        Ok(s) => s,
        Err(_) => return false,
    };
    for _ in 0..steps {
        if sib_i >= proof.siblings.len() || sib_i >= proof.sib_compresses.len() {
            eprintln!("[FriChalBatch] sib overrun");
            return false;
        }
        let sib = proof.siblings[sib_i];
        let (left, right) = if index.is_multiple_of(2) {
            (digest, sib)
        } else {
            (sib, digest)
        };
        let expect = proof.sib_layer_digests[sib_i];
        if !verify_compress_digest(left, right, &expect, &proof.sib_compresses[sib_i]) {
            eprintln!("[FriChalBatch] sib compress {sib_i}");
            return false;
        }
        digest = expect;
        sib_i += 1;
        index /= 2;
        curr_height /= 2;

        let inject_idxs: Vec<usize> = remaining
            .iter()
            .copied()
            .filter(|&i| dimensions[i].height == curr_height)
            .collect();
        if !inject_idxs.is_empty() {
            remaining.retain(|i| !inject_idxs.contains(i));
            let inj_digest = if inject_idxs.len() == 1 {
                proof.leaf_digests[digest_of[inject_idxs[0]]]
            } else {
                let mut concat = Vec::new();
                for &i in &inject_idxs {
                    concat.extend_from_slice(&opened_vals[i]);
                }
                hash_val_leaf(&concat)
            };
            if inj_i >= proof.inject_compresses.len() {
                eprintln!("[FriChalBatch] inject overrun");
                return false;
            }
            let expect = proof.inject_digests[inj_i];
            if !verify_compress_digest(digest, inj_digest, &expect, &proof.inject_compresses[inj_i])
            {
                eprintln!("[FriChalBatch] inject compress {inj_i}");
                return false;
            }
            digest = expect;
            inj_i += 1;
        }
    }
    if sib_i != proof.siblings.len() || &digest != expected_root {
        eprintln!("[FriChalBatch] final root/sib");
        return false;
    }
    true
}

/// Prove ValMmcs openings for all FRI queries.
pub fn fri_val_mmcs_bundle_from_agg_proof(
    proof: &Proof<WqcStarkConfig>,
) -> Result<Vec<FriValMmcsQueryProof>, String> {
    let chal = replay_agg_fri_challenges(proof)?;
    let view = decode_pcs_view(proof)?;
    let config = devnet_circle_config();
    let pcs = config.pcs();
    let degree = 1usize << proof.degree_bits;
    let init_trace_domain = <crate::plonky3_stark::config::Pcs as Pcs<
        Challenge,
        crate::plonky3_stark::config::Challenger,
    >>::natural_domain_for_degree(pcs, degree);
    let quotient_domain = init_trace_domain.create_disjoint_domain(degree);
    let log_blowup = chal.log_blowup;
    let log_global_max_height = view.fri_proof.commit_phase_commits.len() + log_blowup + 1;
    let trace_height = init_trace_domain.size() << log_blowup;
    let quot_height = quotient_domain.size() << log_blowup;
    let trace_log_height = log2_strict(trace_height)?;
    let quot_log_height = log2_strict(quot_height)?;
    let trace_root = commitment_root_val(&proof.commitments.trace)?;
    let quot_root = commitment_root_val(&proof.commitments.quotient_chunks)?;

    let mut out = Vec::with_capacity(AGG_FRI_PROVEN_QUERIES);
    for q in 0..AGG_FRI_PROVEN_QUERIES {
        let query_index = chal.query_indices[q];
        let input = decode_input_proof(&view.fri_proof.query_proofs[q].input_proof)?;
        let trace_open = &input.input_openings[0];
        let quot_open = &input.input_openings[1];
        let trace_row = trace_open
            .opened_values
            .first()
            .ok_or_else(|| format!("q{q}: empty trace"))?;
        let quot_row = quot_open
            .opened_values
            .first()
            .ok_or_else(|| format!("q{q}: empty quot"))?;
        if trace_row.len() != AGG_WIDTH {
            return Err(format!("q{q}: trace width"));
        }
        if quot_row.len() != EF_DIM {
            return Err(format!("q{q}: quot width"));
        }
        let t_idx = query_index >> (log_global_max_height - trace_log_height);
        let q_idx = query_index >> (log_global_max_height - quot_log_height);
        let trace_path =
            generate_fri_mmcs_path_proof(trace_row, &trace_open.opening_proof, t_idx, &trace_root)
                .map_err(|e| format!("q{q} trace path: {e}"))?;
        let quot_path =
            generate_fri_mmcs_path_proof(quot_row, &quot_open.opening_proof, q_idx, &quot_root)
                .map_err(|e| format!("q{q} quot path: {e}"))?;
        out.push(FriValMmcsQueryProof {
            trace_index: t_idx as u32,
            quot_index: q_idx as u32,
            trace_siblings: trace_open.opening_proof.clone(),
            quot_siblings: quot_open.opening_proof.clone(),
            trace_path,
            quot_path,
        });
    }
    Ok(out)
}

pub fn bind_fri_val_mmcs_bundle(
    proof: &Proof<WqcStarkConfig>,
    bundle: &[FriValMmcsQueryProof],
) -> Result<(), String> {
    if bundle.len() != AGG_FRI_PROVEN_QUERIES {
        return Err(format!(
            "val mmcs len {}, want {AGG_FRI_PROVEN_QUERIES}",
            bundle.len()
        ));
    }
    let chal = replay_agg_fri_challenges(proof)?;
    let view = decode_pcs_view(proof)?;
    let config = devnet_circle_config();
    let pcs = config.pcs();
    let degree = 1usize << proof.degree_bits;
    let init_trace_domain = <crate::plonky3_stark::config::Pcs as Pcs<
        Challenge,
        crate::plonky3_stark::config::Challenger,
    >>::natural_domain_for_degree(pcs, degree);
    let quotient_domain = init_trace_domain.create_disjoint_domain(degree);
    let log_blowup = chal.log_blowup;
    let log_global_max_height = view.fri_proof.commit_phase_commits.len() + log_blowup + 1;
    let trace_height = init_trace_domain.size() << log_blowup;
    let quot_height = quotient_domain.size() << log_blowup;
    let trace_log_height = log2_strict(trace_height)?;
    let quot_log_height = log2_strict(quot_height)?;
    let trace_root = commitment_root_val(&proof.commitments.trace)?;
    let quot_root = commitment_root_val(&proof.commitments.quotient_chunks)?;

    for (q, qp) in bundle.iter().enumerate() {
        let query_index = chal.query_indices[q];
        let input = decode_input_proof(&view.fri_proof.query_proofs[q].input_proof)?;
        let trace_row = &input.input_openings[0].opened_values[0];
        let quot_row = &input.input_openings[1].opened_values[0];
        let t_idx = query_index >> (log_global_max_height - trace_log_height);
        let q_idx = query_index >> (log_global_max_height - quot_log_height);
        if qp.trace_index as usize != t_idx || qp.quot_index as usize != q_idx {
            return Err(format!("q{q}: index mismatch"));
        }
        if qp.trace_siblings != input.input_openings[0].opening_proof
            || qp.quot_siblings != input.input_openings[1].opening_proof
        {
            return Err(format!("q{q}: siblings mismatch"));
        }
        if !verify_fri_mmcs_path_proof(
            trace_row,
            &qp.trace_siblings,
            t_idx,
            &trace_root,
            &qp.trace_path,
        ) {
            return Err(format!("q{q}: trace path verify failed"));
        }
        if !verify_fri_mmcs_path_proof(
            quot_row,
            &qp.quot_siblings,
            q_idx,
            &quot_root,
            &qp.quot_path,
        ) {
            return Err(format!("q{q}: quot path verify failed"));
        }
    }
    Ok(())
}

/// Prove ChallengeMmcs openings for all FRI queries.
pub fn fri_chal_mmcs_bundle_from_agg_proof(
    proof: &Proof<WqcStarkConfig>,
) -> Result<Vec<FriChalMmcsQueryProof>, String> {
    let chal = replay_agg_fri_challenges(proof)?;
    let view = decode_pcs_view(proof)?;
    let config = devnet_circle_config();
    let pcs = config.pcs();
    let fri_mmcs = &pcs.fri_params.mmcs;
    let fl_root = commitment_root_chal(&view.first_layer_commitment)?;

    let mut out = Vec::with_capacity(AGG_FRI_PROVEN_QUERIES);
    for q in 0..AGG_FRI_PROVEN_QUERIES {
        let query_index = chal.query_indices[q];
        let qp = &view.fri_proof.query_proofs[q];
        let input = decode_input_proof(&qp.input_proof)?;
        let (_reduced, fold_ys) = reconstruct_agg_query_ro(proof, &chal, &view, q)?;
        if fold_ys.len() != input.first_layer_siblings.len() {
            return Err(format!("q{q}: first-layer sibling count"));
        }

        let fl_dims: Vec<Dimensions> = fold_ys
            .iter()
            .map(|w| Dimensions {
                width: CHAL_LEAF_WIDTH,
                height: 1 << w.log_folded_height,
            })
            .collect();
        // ExtensionMmcs flattens EF width 2 → Val width 6; Dimensions for ValMmcs use flat width.
        // But generate_chal_batch_path uses Val rows directly — pass flat dims matching opened vals.
        let fl_opened: Vec<Vec<Mersenne31>> = fold_ys
            .iter()
            .map(|w| flatten_challenge_row(&[w.v0, w.v1]))
            .collect();
        let fl_dims_flat: Vec<Dimensions> = fold_ys
            .iter()
            .map(|w| Dimensions {
                width: CHAL_LEAF_WIDTH,
                height: 1 << w.log_folded_height,
            })
            .collect();
        let _ = fl_dims;
        let first_layer = generate_chal_batch_path(
            &fl_opened,
            &fl_dims_flat,
            query_index >> 1,
            &input.first_layer_proof,
            &fl_root,
        )
        .map_err(|e| format!("q{q} first-layer: {e}"))?;

        // Commit-phase single-matrix paths.
        let mut commit_indices = Vec::new();
        let mut commit_siblings = Vec::new();
        let mut commit_paths = Vec::new();
        let openings = &qp.commit_phase_openings;
        let betas = &chal.betas;
        let commits = &view.fri_proof.commit_phase_commits;
        let mut index = query_index >> chal.extra_query_index_bits;
        let mut log_current = openings.len() + chal.log_blowup;
        let mut folded_eval = Challenge::ZERO;
        let (reduced, _) = reconstruct_agg_query_ro(proof, &chal, &view, q)?;
        let mut ro_iter = reduced.iter().peekable();

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
            let row = flatten_challenge_row(&evals);
            let root = commitment_root_chal(&commits[round])?;
            let path = generate_fri_mmcs_path_proof(&row, &opening.opening_proof, index, &root)
                .map_err(|e| format!("q{q} commit {round}: {e}"))?;
            commit_indices.push(index as u32);
            commit_siblings.push(opening.opening_proof.clone());
            commit_paths.push(path);

            folded_eval = fold_x_row(index, log_folded, betas[round], evals[0], evals[1]);
            log_current = log_folded;
            let _ = fri_mmcs;
        }

        out.push(FriChalMmcsQueryProof {
            first_layer,
            commit_indices,
            commit_siblings,
            commit_paths,
        });
    }
    Ok(out)
}

pub fn bind_fri_chal_mmcs_bundle(
    proof: &Proof<WqcStarkConfig>,
    bundle: &[FriChalMmcsQueryProof],
) -> Result<(), String> {
    if bundle.len() != AGG_FRI_PROVEN_QUERIES {
        return Err(format!(
            "chal mmcs len {}, want {AGG_FRI_PROVEN_QUERIES}",
            bundle.len()
        ));
    }
    let chal = replay_agg_fri_challenges(proof)?;
    let view = decode_pcs_view(proof)?;
    let fl_root = commitment_root_chal(&view.first_layer_commitment)?;

    for (q, qp_proof) in bundle.iter().enumerate() {
        let query_index = chal.query_indices[q];
        let qp = &view.fri_proof.query_proofs[q];
        let input = decode_input_proof(&qp.input_proof)?;
        let (reduced, fold_ys) = reconstruct_agg_query_ro(proof, &chal, &view, q)?;
        let fl_opened: Vec<Vec<Mersenne31>> = fold_ys
            .iter()
            .map(|w| flatten_challenge_row(&[w.v0, w.v1]))
            .collect();
        let fl_dims: Vec<Dimensions> = fold_ys
            .iter()
            .map(|w| Dimensions {
                width: CHAL_LEAF_WIDTH,
                height: 1 << w.log_folded_height,
            })
            .collect();
        if qp_proof.first_layer.siblings != input.first_layer_proof {
            return Err(format!("q{q}: first-layer siblings mismatch"));
        }
        if !verify_chal_batch_path_replay(
            &fl_opened,
            &fl_dims,
            query_index >> 1,
            &fl_root,
            &qp_proof.first_layer,
        ) {
            return Err(format!("q{q}: first-layer path verify failed"));
        }

        let openings = &qp.commit_phase_openings;
        let betas = &chal.betas;
        let commits = &view.fri_proof.commit_phase_commits;
        if qp_proof.commit_paths.len() != openings.len() {
            return Err(format!("q{q}: commit path count"));
        }
        let mut index = query_index >> chal.extra_query_index_bits;
        let mut log_current = openings.len() + chal.log_blowup;
        let mut folded_eval = Challenge::ZERO;
        let mut ro_iter = reduced.iter().peekable();
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
            let row = flatten_challenge_row(&evals);
            let root = commitment_root_chal(&commits[round])?;
            if qp_proof.commit_siblings[round] != opening.opening_proof
                || qp_proof.commit_indices[round] as usize != index
            {
                return Err(format!("q{q} round {round}: commit meta mismatch"));
            }
            if !verify_fri_mmcs_path_proof(
                &row,
                &qp_proof.commit_siblings[round],
                index,
                &root,
                &qp_proof.commit_paths[round],
            ) {
                return Err(format!("q{q} round {round}: commit path verify failed"));
            }
            folded_eval = fold_x_row(index, log_folded, betas[round], evals[0], evals[1]);
            log_current = log_folded;
        }
    }
    Ok(())
}

pub fn fri_mmcs_bundle_from_agg_proof(
    proof: &Proof<WqcStarkConfig>,
) -> Result<AggFriMmcsBundle, String> {
    Ok(AggFriMmcsBundle {
        val: fri_val_mmcs_bundle_from_agg_proof(proof)?,
        chal: fri_chal_mmcs_bundle_from_agg_proof(proof)?,
    })
}

pub fn bind_fri_mmcs_bundle_to_proof(
    proof: &Proof<WqcStarkConfig>,
    bundle: &AggFriMmcsBundle,
) -> Result<(), String> {
    bind_fri_val_mmcs_bundle(proof, &bundle.val)?;
    bind_fri_chal_mmcs_bundle(proof, &bundle.chal)?;
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
    fn fri_mmcs_query0_val_and_chal() {
        let ctx = AggregationContext {
            parent_task_id: "parent",
            compose_label: "L1:0",
            manifest_root_hash: "",
            left_child_hash: [61u8; CHILD_HASH_LEN],
            right_child_hash: [63u8; CHILD_HASH_LEN],
        };
        let transcript = generate_aggregation_proof(&ctx).expect("prove");
        let plonky3 = decode_agg_proof_owned(&transcript, &ctx).expect("decode");
        let proof: Proof<WqcStarkConfig> = postcard::from_bytes(&plonky3).expect("postcard");

        // Prove only query 0 by temporarily using full bundle APIs' internals.
        let chal = replay_agg_fri_challenges(&proof).expect("fs");
        let view = decode_pcs_view(&proof).expect("pcs");
        let config = devnet_circle_config();
        let pcs = config.pcs();
        let degree = 1usize << proof.degree_bits;
        let init_trace_domain = <crate::plonky3_stark::config::Pcs as Pcs<
            Challenge,
            crate::plonky3_stark::config::Challenger,
        >>::natural_domain_for_degree(pcs, degree);
        let quotient_domain = init_trace_domain.create_disjoint_domain(degree);
        let log_blowup = chal.log_blowup;
        let log_global_max_height = view.fri_proof.commit_phase_commits.len() + log_blowup + 1;
        let trace_height = init_trace_domain.size() << log_blowup;
        let quot_height = quotient_domain.size() << log_blowup;
        let t_idx =
            chal.query_indices[0] >> (log_global_max_height - log2_strict(trace_height).unwrap());
        let q_idx =
            chal.query_indices[0] >> (log_global_max_height - log2_strict(quot_height).unwrap());
        let input = decode_input_proof(&view.fri_proof.query_proofs[0].input_proof).expect("input");
        let trace_root = commitment_root_val(&proof.commitments.trace).unwrap();
        let quot_root = commitment_root_val(&proof.commitments.quotient_chunks).unwrap();
        let tp = generate_fri_mmcs_path_proof(
            &input.input_openings[0].opened_values[0],
            &input.input_openings[0].opening_proof,
            t_idx,
            &trace_root,
        )
        .expect("trace path");
        assert!(verify_fri_mmcs_path_proof(
            &input.input_openings[0].opened_values[0],
            &input.input_openings[0].opening_proof,
            t_idx,
            &trace_root,
            &tp
        ));
        let qp = generate_fri_mmcs_path_proof(
            &input.input_openings[1].opened_values[0],
            &input.input_openings[1].opening_proof,
            q_idx,
            &quot_root,
        )
        .expect("quot path");
        assert!(verify_fri_mmcs_path_proof(
            &input.input_openings[1].opened_values[0],
            &input.input_openings[1].opening_proof,
            q_idx,
            &quot_root,
            &qp
        ));

        let (_reduced, fold_ys) = reconstruct_agg_query_ro(&proof, &chal, &view, 0).expect("ro");
        let fl_opened: Vec<Vec<Mersenne31>> = fold_ys
            .iter()
            .map(|w| flatten_challenge_row(&[w.v0, w.v1]))
            .collect();
        let fl_dims: Vec<Dimensions> = fold_ys
            .iter()
            .map(|w| Dimensions {
                width: CHAL_LEAF_WIDTH,
                height: 1 << w.log_folded_height,
            })
            .collect();
        let fl_root = commitment_root_chal(&view.first_layer_commitment).unwrap();
        let fl = generate_chal_batch_path(
            &fl_opened,
            &fl_dims,
            chal.query_indices[0] >> 1,
            &input.first_layer_proof,
            &fl_root,
        )
        .expect("first-layer");
        assert!(verify_chal_batch_path_replay(
            &fl_opened,
            &fl_dims,
            chal.query_indices[0] >> 1,
            &fl_root,
            &fl
        ));

        // Commit round 0
        let openings = &view.fri_proof.query_proofs[0].commit_phase_openings;
        let (reduced, _) = reconstruct_agg_query_ro(&proof, &chal, &view, 0).unwrap();
        let mut index = chal.query_indices[0] >> chal.extra_query_index_bits;
        let log_current = openings.len() + chal.log_blowup;
        let mut folded_eval = Challenge::ZERO;
        let mut ro_iter = reduced.iter().peekable();
        if let Some(&&(lh, ro)) = ro_iter.peek() {
            if lh == log_current {
                folded_eval += ro;
                let _ = ro_iter.next();
            }
        }
        let sibling = openings[0].sibling_values[0];
        let index_in_group = index % 2;
        let mut evals = [Challenge::ZERO; 2];
        evals[index_in_group] = folded_eval;
        evals[index_in_group ^ 1] = sibling;
        index >>= 1;
        let row = flatten_challenge_row(&evals);
        let root = commitment_root_chal(&view.fri_proof.commit_phase_commits[0]).unwrap();
        let cp = generate_fri_mmcs_path_proof(&row, &openings[0].opening_proof, index, &root)
            .expect("commit0");
        assert!(verify_fri_mmcs_path_proof(
            &row,
            &openings[0].opening_proof,
            index,
            &root,
            &cp
        ));
    }
}

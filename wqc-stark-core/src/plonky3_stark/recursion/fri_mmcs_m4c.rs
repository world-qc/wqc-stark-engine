//! R3-M4c: fold eligible leaf Mmcs paths into M4b groups and strip nested STARKs from the wire.

use p3_commit::{Mmcs, Pcs, PolynomialSpace};
use p3_field::PrimeCharacteristicRing;
use p3_matrix::Dimensions;
use p3_mersenne_31::Mersenne31;
use p3_uni_stark::{Proof, StarkGenericConfig};

use crate::plonky3_stark::config::{Challenge, ChallengeMmcs, Val, ValMmcs, WqcStarkConfig};

use super::fri_fold_bind::LEAF_FRI_PROVEN_QUERIES;
use super::fri_fold_native::{challenge_to_limbs, fold_x_row};
use super::fri_fs_replay::{decode_pcs_view, replay_fri_challenges};
use super::fri_mmcs_bind::{
    AggFriMmcsBundle, FriChalBatchPathProof, FriChalMmcsQueryProof, FriValMmcsQueryProof,
};
use super::fri_mmcs_group_m4b::{
    generate_keccak_group_fold_proof, m4b_group_chunk, verify_keccak_group_fold_proof,
    KeccakGroupFoldProof, MmcsPathStatement,
};
use super::fri_mmcs_path::FriMmcsPathProof;
use super::fri_ro::{decode_input_proof, reconstruct_query_ro};
use super::keccak_f_native::{keccak256_compress, keccak256_val_leaf, KECCAK_RATE};
use super::merkle_keccak::hash_val_leaf;

/// Leaf PCS Mmcs wire version (after `kind` byte in V6 leaf cert).
/// v2: adds `val_quot_batch` + `chal_first_layer` equal-height / single-matrix batch folds.
/// v3: each homogeneous category holds a `Vec` of chunked group STARKs (peak-RAM
///     tunable via `WQC_M4B_GROUP_CHUNK`) instead of a single optional group.
pub const LEAF_MMCS_FOLD_V: u8 = 3;

const EF_DIM: usize = 3;
const CHAL_LEAF_WIDTH: usize = 6;

/// Group folds attached to a leaf PCS certificate (M4c / batch fold).
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct LeafMmcsFoldGroups {
    /// Chunked group STARKs per category (v3). Empty = category not folded;
    /// multiple entries = paths split into `WQC_M4B_GROUP_CHUNK`-sized chunks
    /// proven sequentially. Chunk boundaries are recovered from each group's
    /// `path_count` on verify (env-independent).
    pub val_trace: Vec<KeccakGroupFoldProof>,
    pub val_quot: Vec<KeccakGroupFoldProof>,
    /// Equal-height multi-chunk Val quot Merkle (concat leaf → M4b).
    pub val_quot_batch: Vec<KeccakGroupFoldProof>,
    /// Single-matrix Chal first_layer (idle unitary) → M4b.
    pub chal_first_layer: Vec<KeccakGroupFoldProof>,
    /// Commit-phase groups; ordered by ascending depth, then chunk within depth.
    pub chal_commit: Vec<KeccakGroupFoldProof>,
}

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

/// True when M4b can prove a path for this leaf width (1–2 Keccak perms).
pub fn m4b_width_eligible(leaf_width: usize) -> bool {
    let msg_len = leaf_width.saturating_mul(4);
    (12..=2 * KECCAK_RATE).contains(&msg_len) && msg_len.is_multiple_of(4)
}

/// Drop nested uni-STARK bytes from a batch path; keep rows/digests for host checks.
pub fn strip_chal_batch_starks(batch: &mut FriChalBatchPathProof) {
    for k in &mut batch.leaf_keccs {
        k.stark.clear();
    }
    for c in &mut batch.sib_compresses {
        c.stark.clear();
    }
    for c in &mut batch.inject_compresses {
        c.stark.clear();
    }
}

pub fn batch_starks_stripped(batch: &FriChalBatchPathProof) -> bool {
    batch.leaf_keccs.iter().all(|k| k.stark.is_empty())
        && batch.sib_compresses.iter().all(|c| c.stark.is_empty())
        && batch.inject_compresses.iter().all(|c| c.stark.is_empty())
}

/// Drop nested uni-STARK bytes; keep digests / shape for wire + host digest checks.
pub fn strip_fri_mmcs_path_starks(path: &mut FriMmcsPathProof) {
    path.fold_stark.clear();
    path.leaf_keccak.stark.clear();
    for c in &mut path.compress_starks {
        c.stark.clear();
    }
}

pub fn path_starks_stripped(path: &FriMmcsPathProof) -> bool {
    path.fold_stark.is_empty()
        && path.leaf_keccak.stark.is_empty()
        && path.compress_starks.iter().all(|c| c.stark.is_empty())
}

/// Native digest binding without nested STARKs (used when path is grouped).
pub fn verify_fri_mmcs_path_digests(
    row: &[Mersenne31],
    siblings: &[[u8; 32]],
    index: usize,
    expected_root: &[u8; 32],
    path: &FriMmcsPathProof,
) -> bool {
    let depth = path.depth as usize;
    if siblings.len() != depth
        || path.layer_digests.len() != depth
        || path.compress_starks.len() != depth
        || row.len() as u32 != path.leaf_width
        || depth == 0
    {
        return false;
    }
    let leaf = keccak256_val_leaf(row);
    if leaf != path.leaf_digest || leaf != hash_val_leaf(row) || leaf != path.leaf_keccak.digest {
        return false;
    }
    let mut digest = leaf;
    let mut idx = index;
    for (i, sib) in siblings.iter().enumerate() {
        let (left, right) = if idx.is_multiple_of(2) {
            (digest, *sib)
        } else {
            (*sib, digest)
        };
        let next = keccak256_compress(left, right);
        if next != path.layer_digests[i] {
            return false;
        }
        digest = next;
        idx /= 2;
    }
    &digest == expected_root
}

fn collect_val_trace_stmts(
    proof: &Proof<WqcStarkConfig>,
    trace_width: usize,
    bundle: &[FriValMmcsQueryProof],
) -> Result<Vec<MmcsPathStatement>, String> {
    let chal = replay_fri_challenges(proof, trace_width)?;
    let view = decode_pcs_view(proof)?;
    let config = crate::plonky3_stark::config::devnet_circle_config();
    let pcs = config.pcs();
    let degree = 1usize << proof.degree_bits;
    let init_trace_domain = <crate::plonky3_stark::config::Pcs as Pcs<
        Challenge,
        crate::plonky3_stark::config::Challenger,
    >>::natural_domain_for_degree(pcs, degree);
    let log_blowup = chal.log_blowup;
    let log_global_max_height = view.fri_proof.commit_phase_commits.len() + log_blowup + 1;
    let trace_height = init_trace_domain.size() << log_blowup;
    let trace_log_height = log2_strict(trace_height)?;
    let trace_root = commitment_root_val(&proof.commitments.trace)?;

    let mut stmts = Vec::with_capacity(LEAF_FRI_PROVEN_QUERIES);
    for (q, qp) in bundle.iter().enumerate() {
        let query_index = chal.query_indices[q];
        let input = decode_input_proof(&view.fri_proof.query_proofs[q].input_proof)?;
        let row = input.input_openings[0]
            .opened_values
            .first()
            .ok_or_else(|| format!("q{q}: empty trace"))?
            .clone();
        if row.len() != trace_width {
            return Err(format!("q{q}: trace width"));
        }
        let t_idx = query_index >> (log_global_max_height - trace_log_height);
        if qp.trace_index as usize != t_idx
            || qp.trace_siblings != input.input_openings[0].opening_proof
        {
            return Err(format!("q{q}: trace meta mismatch for group"));
        }
        stmts.push(MmcsPathStatement {
            row,
            siblings: qp.trace_siblings.clone(),
            index: t_idx,
            root: trace_root,
        });
    }
    Ok(stmts)
}

fn collect_val_quot_stmts(
    proof: &Proof<WqcStarkConfig>,
    trace_width: usize,
    bundle: &[FriValMmcsQueryProof],
) -> Result<Option<Vec<MmcsPathStatement>>, String> {
    if bundle.iter().any(|q| q.quot_batch.is_some()) {
        return Ok(None);
    }
    let chal = replay_fri_challenges(proof, trace_width)?;
    let view = decode_pcs_view(proof)?;
    let config = crate::plonky3_stark::config::devnet_circle_config();
    let pcs = config.pcs();
    let degree = 1usize << proof.degree_bits;
    let init_trace_domain = <crate::plonky3_stark::config::Pcs as Pcs<
        Challenge,
        crate::plonky3_stark::config::Challenger,
    >>::natural_domain_for_degree(pcs, degree);
    let log_blowup = chal.log_blowup;
    let log_global_max_height = view.fri_proof.commit_phase_commits.len() + log_blowup + 1;
    let num_quot = proof.opened_values.quotient_chunks.len();
    if num_quot != 1 {
        return Ok(None);
    }
    let quot_parent = init_trace_domain.create_disjoint_domain(1usize << proof.degree_bits);
    let quot_chunk_domains = quot_parent.split_domains(1);
    let quot_h = quot_chunk_domains[0].size() << log_blowup;
    let quot_log_height = log2_strict(quot_h)?;
    let quot_root = commitment_root_val(&proof.commitments.quotient_chunks)?;

    let mut stmts = Vec::with_capacity(LEAF_FRI_PROVEN_QUERIES);
    for (q, qp) in bundle.iter().enumerate() {
        let query_index = chal.query_indices[q];
        let input = decode_input_proof(&view.fri_proof.query_proofs[q].input_proof)?;
        let row = input.input_openings[1].opened_values[0].clone();
        if row.len() != EF_DIM {
            return Err(format!("q{q}: quot width"));
        }
        let q_idx = query_index >> (log_global_max_height - quot_log_height);
        if qp.quot_index as usize != q_idx
            || qp.quot_siblings != input.input_openings[1].opening_proof
        {
            return Err(format!("q{q}: quot meta mismatch for group"));
        }
        stmts.push(MmcsPathStatement {
            row,
            siblings: qp.quot_siblings.clone(),
            index: q_idx,
            root: quot_root,
        });
    }
    Ok(Some(stmts))
}

fn collect_chal_commit_stmts_by_depth(
    proof: &Proof<WqcStarkConfig>,
    trace_width: usize,
    bundle: &[FriChalMmcsQueryProof],
) -> Result<Vec<(usize, Vec<MmcsPathStatement>)>, String> {
    let chal = replay_fri_challenges(proof, trace_width)?;
    let view = decode_pcs_view(proof)?;
    let mut by_depth: Vec<(usize, Vec<MmcsPathStatement>)> = Vec::new();

    for (q, qp_proof) in bundle.iter().enumerate() {
        let query_index = chal.query_indices[q];
        let qp = &view.fri_proof.query_proofs[q];
        let openings = &qp.commit_phase_openings;
        let betas = &chal.betas;
        let commits = &view.fri_proof.commit_phase_commits;
        if qp_proof.commit_paths.len() != openings.len() {
            return Err(format!("q{q}: commit path count"));
        }
        let mut index = query_index >> chal.extra_query_index_bits;
        let mut log_current = openings.len() + chal.log_blowup;
        let mut folded_eval = Challenge::ZERO;
        let (reduced, _) = reconstruct_query_ro(proof, &chal, &view, q, trace_width)?;
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
            let depth = opening.opening_proof.len();
            if qp_proof.commit_siblings[round] != opening.opening_proof
                || qp_proof.commit_indices[round] as usize != index
                || qp_proof.commit_paths[round].depth as usize != depth
            {
                return Err(format!("q{q} round {round}: commit meta for group"));
            }
            let stmt = MmcsPathStatement {
                row,
                siblings: qp_proof.commit_siblings[round].clone(),
                index,
                root,
            };
            if let Some((_, stmts)) = by_depth.iter_mut().find(|(d, _)| *d == depth) {
                stmts.push(stmt);
            } else {
                by_depth.push((depth, vec![stmt]));
            }

            folded_eval = fold_x_row(index, log_folded, betas[round], evals[0], evals[1]);
            log_current = log_folded;
        }
    }
    by_depth.sort_by_key(|(d, _)| *d);
    Ok(by_depth)
}

/// True when a homogeneous statement set is eligible for M4b group folding.
fn group_eligible(stmts: &[MmcsPathStatement]) -> bool {
    if stmts.is_empty() {
        return false;
    }
    let width = stmts[0].row.len();
    let depth = stmts[0].siblings.len();
    if depth == 0 || !m4b_width_eligible(width) {
        return false;
    }
    stmts
        .iter()
        .all(|s| s.row.len() == width && s.siblings.len() == depth)
}

/// Fold eligible paths into one group STARK per `WQC_M4B_GROUP_CHUNK`-sized chunk.
/// Returns an empty Vec when the set is ineligible (host falls back to nested/native).
fn try_group_chunked(stmts: &[MmcsPathStatement]) -> Result<Vec<KeccakGroupFoldProof>, String> {
    if !group_eligible(stmts) {
        return Ok(Vec::new());
    }
    let chunk = m4b_group_chunk();
    let mut groups = Vec::with_capacity(stmts.len().div_ceil(chunk));
    for c in stmts.chunks(chunk) {
        groups.push(generate_keccak_group_fold_proof(c)?);
    }
    Ok(groups)
}

/// Equal-height multi-matrix batch → concat leaf path statement (no injects).
fn eq_height_batch_stmt(
    opened_vals: &[Vec<Mersenne31>],
    dimensions: &[Dimensions],
    index: usize,
    siblings: &[[u8; 32]],
    root: [u8; 32],
    batch: &FriChalBatchPathProof,
) -> Option<MmcsPathStatement> {
    if dimensions.is_empty() || dimensions.len() != opened_vals.len() {
        return None;
    }
    let h0 = dimensions[0].height;
    if !dimensions.iter().all(|d| d.height == h0) || !batch.inject_compresses.is_empty() {
        return None;
    }
    let mut order: Vec<usize> = (0..dimensions.len()).collect();
    order.sort_by_key(|&i| std::cmp::Reverse(dimensions[i].height));
    let mut concat = Vec::new();
    for &i in &order {
        if opened_vals[i].len() != dimensions[i].width {
            return None;
        }
        concat.extend_from_slice(&opened_vals[i]);
    }
    if !m4b_width_eligible(concat.len()) || siblings.is_empty() {
        return None;
    }
    Some(MmcsPathStatement {
        row: concat,
        siblings: siblings.to_vec(),
        index,
        root,
    })
}

fn collect_val_quot_batch_stmts(
    proof: &Proof<WqcStarkConfig>,
    trace_width: usize,
    bundle: &[FriValMmcsQueryProof],
) -> Result<Option<Vec<MmcsPathStatement>>, String> {
    if bundle.iter().any(|q| q.quot_batch.is_none()) {
        return Ok(None);
    }
    let chal = replay_fri_challenges(proof, trace_width)?;
    let view = decode_pcs_view(proof)?;
    let config = crate::plonky3_stark::config::devnet_circle_config();
    let pcs = config.pcs();
    let degree = 1usize << proof.degree_bits;
    let init_trace_domain = <crate::plonky3_stark::config::Pcs as Pcs<
        Challenge,
        crate::plonky3_stark::config::Challenger,
    >>::natural_domain_for_degree(pcs, degree);
    let log_blowup = chal.log_blowup;
    let log_global_max_height = view.fri_proof.commit_phase_commits.len() + log_blowup + 1;
    let num_quot = proof.opened_values.quotient_chunks.len();
    let log_num_quot = num_quot.trailing_zeros() as usize;
    let quot_parent =
        init_trace_domain.create_disjoint_domain(1usize << (proof.degree_bits + log_num_quot));
    let quot_chunk_domains = quot_parent.split_domains(num_quot);
    let quot_root = commitment_root_val(&proof.commitments.quotient_chunks)?;

    let mut stmts = Vec::with_capacity(LEAF_FRI_PROVEN_QUERIES);
    for (q, qp) in bundle.iter().enumerate() {
        let batch = qp.quot_batch.as_ref().unwrap();
        let query_index = chal.query_indices[q];
        let input = decode_input_proof(&view.fri_proof.query_proofs[q].input_proof)?;
        let mut max_log = 0usize;
        let fl_dims: Vec<Dimensions> = quot_chunk_domains
            .iter()
            .map(|d| {
                let h = d.size() << log_blowup;
                max_log = max_log.max(log2_strict(h).unwrap_or(0));
                Dimensions {
                    width: EF_DIM,
                    height: h,
                }
            })
            .collect();
        let q_idx = query_index >> (log_global_max_height - max_log);
        let Some(stmt) = eq_height_batch_stmt(
            &input.input_openings[1].opened_values,
            &fl_dims,
            q_idx,
            &qp.quot_siblings,
            quot_root,
            batch,
        ) else {
            return Ok(None);
        };
        stmts.push(stmt);
    }
    Ok(Some(stmts))
}

fn collect_chal_first_layer_stmts(
    proof: &Proof<WqcStarkConfig>,
    trace_width: usize,
    bundle: &[FriChalMmcsQueryProof],
) -> Result<Option<Vec<MmcsPathStatement>>, String> {
    let chal = replay_fri_challenges(proof, trace_width)?;
    let view = decode_pcs_view(proof)?;
    let fl_root = commitment_root_chal(&view.first_layer_commitment)?;

    let mut stmts = Vec::with_capacity(LEAF_FRI_PROVEN_QUERIES);
    for (q, qp_proof) in bundle.iter().enumerate() {
        let query_index = chal.query_indices[q];
        let (_reduced, fold_ys) = reconstruct_query_ro(proof, &chal, &view, q, trace_width)?;
        // Single-matrix first_layer only (idle unitary).
        if fold_ys.len() != 1 {
            return Ok(None);
        }
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
        let Some(stmt) = eq_height_batch_stmt(
            &fl_opened,
            &fl_dims,
            query_index >> 1,
            &qp_proof.first_layer.siblings,
            fl_root,
            &qp_proof.first_layer,
        ) else {
            return Ok(None);
        };
        // Single matrix: stmt.row is the flattened chal leaf (W=6).
        stmts.push(stmt);
    }
    Ok(Some(stmts))
}

/// After nested Mmcs prove+bind: fold eligible paths into groups and strip nested STARKs.
pub fn apply_leaf_mmcs_m4c_folds(
    proof: &Proof<WqcStarkConfig>,
    trace_width: usize,
    bundle: &mut AggFriMmcsBundle,
) -> Result<LeafMmcsFoldGroups, String> {
    let mut groups = LeafMmcsFoldGroups::default();

    let trace_stmts = collect_val_trace_stmts(proof, trace_width, &bundle.val)?;
    let trace_groups = try_group_chunked(&trace_stmts)?;
    if !trace_groups.is_empty() {
        for qp in &mut bundle.val {
            strip_fri_mmcs_path_starks(&mut qp.trace_path);
        }
        groups.val_trace = trace_groups;
    }

    if let Some(quot_stmts) = collect_val_quot_stmts(proof, trace_width, &bundle.val)? {
        let quot_groups = try_group_chunked(&quot_stmts)?;
        if !quot_groups.is_empty() {
            for qp in &mut bundle.val {
                strip_fri_mmcs_path_starks(&mut qp.quot_path);
            }
            groups.val_quot = quot_groups;
        }
    } else {
        // Multi-chunk stub path — strip always.
        for qp in &mut bundle.val {
            if qp.quot_batch.is_some() {
                strip_fri_mmcs_path_starks(&mut qp.quot_path);
            }
        }
        if let Some(batch_stmts) = collect_val_quot_batch_stmts(proof, trace_width, &bundle.val)? {
            let batch_groups = try_group_chunked(&batch_stmts)?;
            if !batch_groups.is_empty() {
                for qp in &mut bundle.val {
                    if let Some(ref mut batch) = qp.quot_batch {
                        strip_chal_batch_starks(batch);
                    }
                }
                groups.val_quot_batch = batch_groups;
            }
        }
    }

    if let Some(fl_stmts) = collect_chal_first_layer_stmts(proof, trace_width, &bundle.chal)? {
        let fl_groups = try_group_chunked(&fl_stmts)?;
        if !fl_groups.is_empty() {
            for qp in &mut bundle.chal {
                strip_chal_batch_starks(&mut qp.first_layer);
            }
            groups.chal_first_layer = fl_groups;
        }
    } else {
        // Inject / multi-height first_layer: strip nested STARKs (host digest verify).
        for qp in &mut bundle.chal {
            if !qp.first_layer.inject_compresses.is_empty() {
                strip_chal_batch_starks(&mut qp.first_layer);
            }
        }
    }

    let chal_by_depth = collect_chal_commit_stmts_by_depth(proof, trace_width, &bundle.chal)?;
    for (depth, stmts) in chal_by_depth {
        let depth_groups = try_group_chunked(&stmts)?;
        if !depth_groups.is_empty() {
            for qp in &mut bundle.chal {
                for path in &mut qp.commit_paths {
                    if path.depth as usize == depth {
                        strip_fri_mmcs_path_starks(path);
                    }
                }
            }
            groups.chal_commit.extend(depth_groups);
        }
    }

    Ok(groups)
}

/// Bind leaf Mmcs openings using M4c groups where present; nested verify otherwise.
pub fn bind_leaf_mmcs_with_groups(
    proof: &Proof<WqcStarkConfig>,
    bundle: &AggFriMmcsBundle,
    groups: &LeafMmcsFoldGroups,
    trace_width: usize,
) -> Result<(), String> {
    use super::fri_mmcs_bind::{bind_fri_chal_mmcs_bundle_width, bind_fri_val_mmcs_bundle_width};

    let val_needs_custom = !groups.val_trace.is_empty()
        || !groups.val_quot.is_empty()
        || !groups.val_quot_batch.is_empty()
        || bundle.val.iter().any(|q| {
            path_starks_stripped(&q.trace_path)
                || path_starks_stripped(&q.quot_path)
                || q.quot_batch.as_ref().is_some_and(batch_starks_stripped)
        });
    if val_needs_custom {
        bind_val_with_groups(proof, &bundle.val, groups, trace_width)?;
    } else {
        bind_fri_val_mmcs_bundle_width(proof, &bundle.val, trace_width)?;
    }

    let chal_needs_custom = !groups.chal_first_layer.is_empty()
        || !groups.chal_commit.is_empty()
        || bundle.chal.iter().any(|q| {
            batch_starks_stripped(&q.first_layer) || q.commit_paths.iter().any(path_starks_stripped)
        });
    if chal_needs_custom {
        bind_chal_with_groups(proof, &bundle.chal, groups, trace_width)?;
    } else {
        bind_fri_chal_mmcs_bundle_width(proof, &bundle.chal, trace_width)?;
    }
    Ok(())
}

/// Verify a chunked category: each group covers the next `path_count` statements,
/// and the chunks must exactly partition `stmts` (order-preserving, env-independent).
fn verify_group_chunks(
    stmts: &[MmcsPathStatement],
    groups: &[KeccakGroupFoldProof],
    label: &str,
) -> Result<(), String> {
    let mut off = 0usize;
    for g in groups {
        let n = g.path_count as usize;
        let end = off
            .checked_add(n)
            .filter(|&e| e <= stmts.len())
            .ok_or_else(|| format!("{label} chunk [{off}+{n}] exceeds {} stmts", stmts.len()))?;
        if !verify_keccak_group_fold_proof(&stmts[off..end], g) {
            return Err(format!("{label} group verify failed (chunk at {off})"));
        }
        off = end;
    }
    if off != stmts.len() {
        return Err(format!(
            "{label} groups cover {off} of {} stmts",
            stmts.len()
        ));
    }
    Ok(())
}

fn bind_val_with_groups(
    proof: &Proof<WqcStarkConfig>,
    bundle: &[FriValMmcsQueryProof],
    groups: &LeafMmcsFoldGroups,
    trace_width: usize,
) -> Result<(), String> {
    use super::fri_mmcs_bind::{verify_chal_batch_path_digests, verify_chal_batch_path_replay};

    if bundle.len() != LEAF_FRI_PROVEN_QUERIES {
        return Err(format!(
            "val mmcs len {}, want {LEAF_FRI_PROVEN_QUERIES}",
            bundle.len()
        ));
    }
    let chal = replay_fri_challenges(proof, trace_width)?;
    let view = decode_pcs_view(proof)?;
    let config = crate::plonky3_stark::config::devnet_circle_config();
    let pcs = config.pcs();
    let degree = 1usize << proof.degree_bits;
    let init_trace_domain = <crate::plonky3_stark::config::Pcs as Pcs<
        Challenge,
        crate::plonky3_stark::config::Challenger,
    >>::natural_domain_for_degree(pcs, degree);
    let log_blowup = chal.log_blowup;
    let log_global_max_height = view.fri_proof.commit_phase_commits.len() + log_blowup + 1;
    let trace_height = init_trace_domain.size() << log_blowup;
    let trace_log_height = log2_strict(trace_height)?;
    let trace_root = commitment_root_val(&proof.commitments.trace)?;
    let quot_root = commitment_root_val(&proof.commitments.quotient_chunks)?;
    let num_quot = proof.opened_values.quotient_chunks.len();
    let log_num_quot = num_quot.trailing_zeros() as usize;
    let quot_parent =
        init_trace_domain.create_disjoint_domain(1usize << (proof.degree_bits + log_num_quot));
    let quot_chunk_domains = quot_parent.split_domains(num_quot);

    if !groups.val_trace.is_empty() {
        let stmts = collect_val_trace_stmts(proof, trace_width, bundle)?;
        verify_group_chunks(&stmts, &groups.val_trace, "val trace")?;
        for (q, qp) in bundle.iter().enumerate() {
            let query_index = chal.query_indices[q];
            let input = decode_input_proof(&view.fri_proof.query_proofs[q].input_proof)?;
            let row = &input.input_openings[0].opened_values[0];
            let t_idx = query_index >> (log_global_max_height - trace_log_height);
            if !verify_fri_mmcs_path_digests(
                row,
                &qp.trace_siblings,
                t_idx,
                &trace_root,
                &qp.trace_path,
            ) {
                return Err(format!("q{q}: stripped trace digests"));
            }
        }
    }

    if !groups.val_quot.is_empty() {
        let stmts = collect_val_quot_stmts(proof, trace_width, bundle)?
            .ok_or_else(|| "val quot group present but statements unavailable".to_string())?;
        verify_group_chunks(&stmts, &groups.val_quot, "val quot")?;
    }

    if !groups.val_quot_batch.is_empty() {
        let stmts = collect_val_quot_batch_stmts(proof, trace_width, bundle)?
            .ok_or_else(|| "val quot batch group present but statements unavailable".to_string())?;
        verify_group_chunks(&stmts, &groups.val_quot_batch, "val quot batch")?;
    }

    for (q, qp) in bundle.iter().enumerate() {
        let query_index = chal.query_indices[q];
        let input = decode_input_proof(&view.fri_proof.query_proofs[q].input_proof)?;
        let trace_row = &input.input_openings[0].opened_values[0];
        if trace_row.len() != trace_width {
            return Err(format!("q{q}: opened trace width"));
        }
        let t_idx = query_index >> (log_global_max_height - trace_log_height);
        if qp.trace_index as usize != t_idx {
            return Err(format!("q{q}: trace index mismatch"));
        }
        if qp.trace_siblings != input.input_openings[0].opening_proof
            || qp.quot_siblings != input.input_openings[1].opening_proof
        {
            return Err(format!("q{q}: siblings mismatch"));
        }

        if groups.val_trace.is_empty() {
            if path_starks_stripped(&qp.trace_path) {
                // Early drop_nested / M4c miss: host Merkle digests only.
                if !verify_fri_mmcs_path_digests(
                    trace_row,
                    &qp.trace_siblings,
                    t_idx,
                    &trace_root,
                    &qp.trace_path,
                ) {
                    return Err(format!("q{q}: stripped trace digests (no group)"));
                }
            } else if !super::fri_mmcs_path::verify_fri_mmcs_path_proof(
                trace_row,
                &qp.trace_siblings,
                t_idx,
                &trace_root,
                &qp.trace_path,
            ) {
                return Err(format!("q{q}: trace path verify failed"));
            }
        }

        if let Some(ref batch) = qp.quot_batch {
            let mut max_log = 0usize;
            let fl_dims: Vec<Dimensions> = quot_chunk_domains
                .iter()
                .map(|d| {
                    let h = d.size() << log_blowup;
                    max_log = max_log.max(log2_strict(h).unwrap_or(0));
                    Dimensions {
                        width: EF_DIM,
                        height: h,
                    }
                })
                .collect();
            let q_idx = query_index >> (log_global_max_height - max_log);
            if qp.quot_index as usize != q_idx {
                return Err(format!("q{q}: quot batch index mismatch"));
            }
            if !groups.val_quot_batch.is_empty() {
                if !verify_chal_batch_path_digests(
                    &input.input_openings[1].opened_values,
                    &fl_dims,
                    q_idx,
                    &quot_root,
                    batch,
                ) {
                    return Err(format!("q{q}: quot batch digests failed"));
                }
            } else if batch_starks_stripped(batch) {
                if !verify_chal_batch_path_digests(
                    &input.input_openings[1].opened_values,
                    &fl_dims,
                    q_idx,
                    &quot_root,
                    batch,
                ) {
                    return Err(format!("q{q}: quot batch stripped digests failed"));
                }
            } else if !verify_chal_batch_path_replay(
                &input.input_openings[1].opened_values,
                &fl_dims,
                q_idx,
                &quot_root,
                batch,
            ) {
                return Err(format!("q{q}: quot batch verify failed"));
            }
        } else if !groups.val_quot.is_empty() {
            let quot_h = quot_chunk_domains[0].size() << log_blowup;
            let quot_log_height = log2_strict(quot_h)?;
            let quot_row = &input.input_openings[1].opened_values[0];
            let q_idx = query_index >> (log_global_max_height - quot_log_height);
            if !verify_fri_mmcs_path_digests(
                quot_row,
                &qp.quot_siblings,
                q_idx,
                &quot_root,
                &qp.quot_path,
            ) {
                return Err(format!("q{q}: stripped quot digests"));
            }
        } else {
            let quot_h = quot_chunk_domains[0].size() << log_blowup;
            let quot_log_height = log2_strict(quot_h)?;
            let quot_row = &input.input_openings[1].opened_values[0];
            let q_idx = query_index >> (log_global_max_height - quot_log_height);
            if qp.quot_index as usize != q_idx {
                return Err(format!("q{q}: quot index mismatch"));
            }
            if path_starks_stripped(&qp.quot_path) {
                if !verify_fri_mmcs_path_digests(
                    quot_row,
                    &qp.quot_siblings,
                    q_idx,
                    &quot_root,
                    &qp.quot_path,
                ) {
                    return Err(format!("q{q}: stripped quot digests (no group)"));
                }
            } else if !super::fri_mmcs_path::verify_fri_mmcs_path_proof(
                quot_row,
                &qp.quot_siblings,
                q_idx,
                &quot_root,
                &qp.quot_path,
            ) {
                return Err(format!("q{q}: quot path verify failed"));
            }
        }
    }
    Ok(())
}

fn bind_chal_with_groups(
    proof: &Proof<WqcStarkConfig>,
    bundle: &[FriChalMmcsQueryProof],
    groups: &LeafMmcsFoldGroups,
    trace_width: usize,
) -> Result<(), String> {
    if bundle.len() != LEAF_FRI_PROVEN_QUERIES {
        return Err(format!(
            "chal mmcs len {}, want {LEAF_FRI_PROVEN_QUERIES}",
            bundle.len()
        ));
    }
    let chal = replay_fri_challenges(proof, trace_width)?;
    let view = decode_pcs_view(proof)?;
    let fl_root = commitment_root_chal(&view.first_layer_commitment)?;

    if !groups.chal_first_layer.is_empty() {
        let stmts =
            collect_chal_first_layer_stmts(proof, trace_width, bundle)?.ok_or_else(|| {
                "chal first_layer group present but statements unavailable".to_string()
            })?;
        verify_group_chunks(&stmts, &groups.chal_first_layer, "chal first_layer")?;
    }

    // Verify commit groups first (same order as apply: ascending depth, then chunk).
    let by_depth = collect_chal_commit_stmts_by_depth(proof, trace_width, bundle)?;
    let mut group_iter = groups.chal_commit.iter().peekable();
    for (depth, stmts) in &by_depth {
        let eligible =
            m4b_width_eligible(CHAL_LEAF_WIDTH) && stmts.iter().all(|s| s.siblings.len() == *depth);
        if eligible && !stmts.is_empty() {
            let mut off = 0usize;
            while off < stmts.len() {
                let g = group_iter
                    .next()
                    .ok_or_else(|| format!("missing chal commit group for depth {depth}"))?;
                if g.depth as usize != *depth {
                    return Err(format!(
                        "chal commit group depth {} != expected {depth}",
                        g.depth
                    ));
                }
                let n = g.path_count as usize;
                let end = off
                    .checked_add(n)
                    .filter(|&e| e <= stmts.len())
                    .ok_or_else(|| format!("chal commit depth {depth} chunk overflow"))?;
                if !verify_keccak_group_fold_proof(&stmts[off..end], g) {
                    return Err(format!("chal commit group depth {depth} verify failed"));
                }
                off = end;
            }
        }
    }
    if group_iter.next().is_some() {
        return Err("extra chal commit groups".into());
    }

    for (q, qp_proof) in bundle.iter().enumerate() {
        let query_index = chal.query_indices[q];
        let qp = &view.fri_proof.query_proofs[q];
        let input = decode_input_proof(&qp.input_proof)?;
        let (reduced, fold_ys) = reconstruct_query_ro(proof, &chal, &view, q, trace_width)?;
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
        if !groups.chal_first_layer.is_empty() {
            if !super::fri_mmcs_bind::verify_chal_batch_path_digests(
                &fl_opened,
                &fl_dims,
                query_index >> 1,
                &fl_root,
                &qp_proof.first_layer,
            ) {
                return Err(format!("q{q}: first-layer digests failed"));
            }
        } else if batch_starks_stripped(&qp_proof.first_layer) {
            // Inject / multi-RO: nested STARKs stripped; native Merkle digest replay.
            if !super::fri_mmcs_bind::verify_chal_batch_path_digests(
                &fl_opened,
                &fl_dims,
                query_index >> 1,
                &fl_root,
                &qp_proof.first_layer,
            ) {
                return Err(format!("q{q}: first-layer stripped digests failed"));
            }
        } else if !super::fri_mmcs_bind::verify_chal_batch_path_replay(
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
            let path = &qp_proof.commit_paths[round];
            let grouped = groups
                .chal_commit
                .iter()
                .any(|g| g.depth as usize == path.depth as usize);
            if grouped {
                if !verify_fri_mmcs_path_digests(
                    &row,
                    &qp_proof.commit_siblings[round],
                    index,
                    &root,
                    path,
                ) {
                    return Err(format!("q{q} round {round}: stripped commit digests"));
                }
            } else if path_starks_stripped(path) {
                if !verify_fri_mmcs_path_digests(
                    &row,
                    &qp_proof.commit_siblings[round],
                    index,
                    &root,
                    path,
                ) {
                    return Err(format!(
                        "q{q} round {round}: stripped commit digests (no group)"
                    ));
                }
            } else if !super::fri_mmcs_path::verify_fri_mmcs_path_proof(
                &row,
                &qp_proof.commit_siblings[round],
                index,
                &root,
                path,
            ) {
                return Err(format!("q{q} round {round}: commit path verify failed"));
            }
            folded_eval = fold_x_row(index, log_folded, betas[round], evals[0], evals[1]);
            log_current = log_folded;
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::plonky3_stark::recursion::keccak256_air::Keccak256StarkProof;

    #[test]
    fn strip_path_clears_starks() {
        let mut path = FriMmcsPathProof {
            depth: 1,
            leaf_width: 3,
            leaf_digest: [1u8; 32],
            layer_digests: vec![[2u8; 32]],
            fold_stark: vec![9, 9, 9],
            leaf_keccak: Keccak256StarkProof {
                msg_len: 12,
                digest: [1u8; 32],
                stark: vec![1, 2, 3],
            },
            compress_starks: vec![Keccak256StarkProof {
                msg_len: 64,
                digest: [2u8; 32],
                stark: vec![4, 5],
            }],
        };
        assert!(!path_starks_stripped(&path));
        strip_fri_mmcs_path_starks(&mut path);
        assert!(path_starks_stripped(&path));
        assert_eq!(path.compress_starks.len(), 1);
        assert!(path.compress_starks[0].stark.is_empty());
    }

    #[test]
    fn strip_batch_clears_starks() {
        use crate::plonky3_stark::recursion::keccak256_air::Keccak256StarkProof;
        let mut batch = FriChalBatchPathProof {
            index: 0,
            siblings: vec![[1u8; 32]],
            leaf_rows: vec![vec![Mersenne31::from_u32(1); 3]],
            leaf_keccs: vec![Keccak256StarkProof {
                msg_len: 12,
                digest: [2u8; 32],
                stark: vec![1, 2, 3],
            }],
            leaf_digests: vec![[2u8; 32]],
            sib_compresses: vec![Keccak256StarkProof {
                msg_len: 64,
                digest: [3u8; 32],
                stark: vec![4],
            }],
            sib_layer_digests: vec![[3u8; 32]],
            inject_compresses: vec![],
            inject_digests: vec![],
            inject_leaf_indices: vec![],
        };
        assert!(!batch_starks_stripped(&batch));
        strip_chal_batch_starks(&mut batch);
        assert!(batch_starks_stripped(&batch));
    }

    #[test]
    fn m4b_width_gate() {
        assert!(m4b_width_eligible(3));
        assert!(m4b_width_eligible(21));
        assert!(m4b_width_eligible(34)); // 136 B = 1-perm max
        assert!(m4b_width_eligible(48)); // 192 B = idle quot concat
        assert!(m4b_width_eligible(68)); // 272 B = 2-perm max
        assert!(!m4b_width_eligible(69));
        assert!(!m4b_width_eligible(0));
    }
}

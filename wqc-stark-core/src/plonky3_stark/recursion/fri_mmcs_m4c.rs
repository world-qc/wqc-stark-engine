//! R3-M4c: fold eligible leaf Mmcs paths into M4b groups and strip nested STARKs from the wire.

use p3_commit::{Mmcs, Pcs, PolynomialSpace};
use p3_field::PrimeCharacteristicRing;
use p3_matrix::Dimensions;
use p3_mersenne_31::Mersenne31;
use p3_uni_stark::{Proof, StarkGenericConfig};

use crate::plonky3_stark::config::{Challenge, ChallengeMmcs, Val, ValMmcs, WqcStarkConfig};

use super::fri_fold_bind::LEAF_FRI_PROVEN_QUERIES;
use super::fri_fold_native::{challenge_to_limbs, fold_x_row};
use super::fri_fs_replay::fri_queries_from_proof;
use super::fri_fs_replay::{decode_pcs_view, replay_fri_challenges};
use super::fri_mmcs_bind::{
    AggFriMmcsBundle, FriChalBatchPathProof, FriChalMmcsQueryProof, FriValMmcsQueryProof,
};
use super::fri_mmcs_group_m4b::{
    generate_keccak_group_fold_proof, m4b_group_chunk, verify_keccak_group_fold_proof,
    MmcsPathStatement,
};
use super::fri_mmcs_path::FriMmcsPathProof;
use super::fri_ro::{decode_input_proof, reconstruct_query_ro};
use super::keccak_f_native::KECCAK_RATE;
use super::merkle_keccak::{compress_digests, hash_val_leaf};
use super::mmcs_group_fold::{poseidon_group_width_supported, MmcsGroupFoldProof};
use super::poseidon2_group_m4b::{
    generate_poseidon_group_fold_proof, generate_poseidon_group_fold_proof_with_queries,
    verify_poseidon_group_fold_proof,
};

/// Leaf PCS Mmcs wire version (after `kind` byte in V6 leaf cert).
/// v2: adds `val_quot_batch` + `chal_first_layer` equal-height / single-matrix batch folds.
/// v3: each homogeneous category holds a `Vec` of chunked group STARKs (peak-RAM
///     tunable via `WQC_PCS_MMCS_GROUP_CHUNK`) instead of a single optional group.
/// v5: per-group `hash_tag` byte (Keccak / Poseidon); leaf/layer digests dropped
///     from the wire and recomputed from the path statements at verify time.
/// Wire v6: Mmcs path / chal-batch digests + empty Keccak stubs omitted (recomputed at verify).
pub const LEAF_MMCS_FOLD_V: u8 = 6;

const EF_DIM: usize = 3;
const CHAL_LEAF_WIDTH: usize = 6;

/// Collected Mmcs path statements per category (pre-chunk), for benchmarks / replay.
#[derive(Debug, Clone, Default)]
pub struct LeafMmcsGroupStatements {
    pub val_trace: Vec<MmcsPathStatement>,
    pub val_quot: Option<Vec<MmcsPathStatement>>,
    pub val_quot_batch: Option<Vec<MmcsPathStatement>>,
    pub chal_first_layer: Option<Vec<MmcsPathStatement>>,
    pub chal_commit: Vec<(usize, Vec<MmcsPathStatement>)>,
}

/// Group folds attached to a leaf PCS certificate (M4c / batch fold).
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct LeafMmcsFoldGroups {
    /// Chunked group STARKs per category (v3/v4). Empty = category not folded.
    pub val_trace: Vec<MmcsGroupFoldProof>,
    pub val_quot: Vec<MmcsGroupFoldProof>,
    pub val_quot_batch: Vec<MmcsGroupFoldProof>,
    pub chal_first_layer: Vec<MmcsGroupFoldProof>,
    pub chal_commit: Vec<MmcsGroupFoldProof>,
    /// Prove-time flag: `val_trace` covers val + chal paths (chal_* empty).
    /// Not on the wire — verify reconstructs via path-count equality.
    pub pcs_combined: bool,
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

/// True when leaf/layer digests were omitted from the PCS wire (v6+).
pub fn path_digests_stripped(path: &FriMmcsPathProof) -> bool {
    path.layer_digests.is_empty() && path.compress_starks.is_empty()
}

/// Native digest binding without nested STARKs (used when path is grouped).
///
/// When digests are omitted (`path_digests_stripped`), only the Merkle root is checked
/// against `row` + `siblings` (wire v6). Otherwise intermediate digests are cross-checked.
pub fn verify_fri_mmcs_path_digests(
    row: &[Mersenne31],
    siblings: &[[u8; 32]],
    index: usize,
    expected_root: &[u8; 32],
    path: &FriMmcsPathProof,
) -> bool {
    let depth = path.depth as usize;
    if siblings.len() != depth || row.len() as u32 != path.leaf_width || depth == 0 {
        return false;
    }
    let leaf = hash_val_leaf(row);
    if path_digests_stripped(path) {
        return super::merkle_keccak::merkle_root_from_path(leaf, siblings, index)
            == *expected_root;
    }
    if path.layer_digests.len() != depth || path.compress_starks.len() != depth {
        return false;
    }
    if leaf != path.leaf_digest || leaf != path.leaf_keccak.digest {
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
        let next = compress_digests(left, right);
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
    let config = super::fri_fs_replay::circle_config_matching_proof(proof)?;
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
    let config = super::fri_fs_replay::circle_config_matching_proof(proof)?;
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

/// True when a same-width statement set is eligible for M4b group folding.
/// Depths may differ (Poseidon mixed-depth); Keccak still requires homogeneity
/// in [`try_group_chunked`].
fn group_eligible(stmts: &[MmcsPathStatement]) -> bool {
    if stmts.is_empty() {
        return false;
    }
    let width = stmts[0].row.len();
    if !m4b_width_eligible(width) {
        return false;
    }
    stmts
        .iter()
        .all(|s| s.row.len() == width && !s.siblings.is_empty())
}

fn group_fold_path_count(groups: &[MmcsGroupFoldProof]) -> usize {
    groups.iter().map(|g| g.path_count() as usize).sum()
}

/// `val_trace` holds val+chal when chal categories are empty and path counts match.
fn pcs_val_chal_merged(groups: &LeafMmcsFoldGroups, val_n: usize, chal_n: usize) -> bool {
    chal_n > 0
        && val_n > 0
        && groups.chal_commit.is_empty()
        && groups.chal_first_layer.is_empty()
        && groups.val_quot.is_empty()
        && groups.val_quot_batch.is_empty()
        && !groups.val_trace.is_empty()
        && group_fold_path_count(&groups.val_trace) == val_n + chal_n
}

/// Collect homogeneous Mmcs path statements (no prove) for size benchmarks.
pub fn collect_leaf_mmcs_group_statements(
    proof: &Proof<WqcStarkConfig>,
    trace_width: usize,
    bundle: &AggFriMmcsBundle,
) -> Result<LeafMmcsGroupStatements, String> {
    let mut out = LeafMmcsGroupStatements {
        val_trace: collect_val_trace_stmts(proof, trace_width, &bundle.val)?,
        val_quot: collect_val_quot_stmts(proof, trace_width, &bundle.val)?,
        val_quot_batch: None,
        chal_first_layer: collect_chal_first_layer_stmts(proof, trace_width, &bundle.chal)?,
        chal_commit: collect_chal_commit_stmts_by_depth(proof, trace_width, &bundle.chal)?,
    };
    if out.val_quot.is_none() {
        out.val_quot_batch = collect_val_quot_batch_stmts(proof, trace_width, &bundle.val)?
            .filter(|s| !s.is_empty());
    }
    Ok(out)
}

fn sum_keccak_group_bytes(groups: &[MmcsGroupFoldProof]) -> u64 {
    groups
        .iter()
        .filter_map(|g| g.keccak())
        .map(|g| g.group_stark.len() as u64)
        .sum()
}

fn try_poseidon_group_chunked(
    stmts: &[MmcsPathStatement],
    num_queries: usize,
) -> Result<Vec<MmcsGroupFoldProof>, String> {
    if !group_eligible(stmts)
        || !stmts
            .iter()
            .all(|s| poseidon_group_width_supported(s.row.len()))
    {
        return Ok(Vec::new());
    }
    let chunk = m4b_group_chunk();
    let mut groups = Vec::with_capacity(stmts.len().div_ceil(chunk));
    for c in stmts.chunks(chunk) {
        groups.push(MmcsGroupFoldProof::Poseidon(
            generate_poseidon_group_fold_proof_with_queries(c, num_queries)?,
        ));
    }
    groups.shrink_to_fit();
    Ok(groups)
}

fn sum_group_fold_bytes(groups: &[MmcsGroupFoldProof]) -> u64 {
    groups.iter().map(|g| g.group_stark_len() as u64).sum()
}

/// Per-category Mmcs group byte breakdown (Keccak measured + Poseidon spike re-prove).
#[derive(Debug, Clone, PartialEq, Eq, Default, serde::Serialize, serde::Deserialize)]
pub struct PoseidonMmcsBenchmarkReport {
    pub keccak_total: u64,
    pub poseidon_measured: u64,
    pub poseidon_extrapolated: u64,
    pub poseidon_total_estimate: u64,
    pub keccak_groups: u32,
    pub poseidon_groups_measured: u32,
    pub poseidon_groups_skipped_wide: u32,
}

fn benchmark_category(
    stmts: &[MmcsPathStatement],
    keccak_groups: &[MmcsGroupFoldProof],
    ratio_num: u64,
    ratio_den: u64,
    report: &mut PoseidonMmcsBenchmarkReport,
) -> Result<(), String> {
    report.keccak_total += sum_keccak_group_bytes(keccak_groups);
    report.keccak_groups += keccak_groups.len() as u32;

    if stmts.is_empty() {
        return Ok(());
    }
    if stmts
        .iter()
        .all(|s| poseidon_group_width_supported(s.row.len()))
    {
        let p_groups = try_poseidon_group_chunked(
            stmts,
            crate::plonky3_stark::config::DEVNET_FRI_NUM_QUERIES,
        )?;
        let bytes = sum_group_fold_bytes(&p_groups);
        report.poseidon_measured += bytes;
        report.poseidon_groups_measured += p_groups.len() as u32;
    } else {
        report.poseidon_groups_skipped_wide += keccak_groups.len() as u32;
        for g in keccak_groups {
            let k = g.group_stark_len() as u64;
            report.poseidon_extrapolated += k.saturating_mul(ratio_num) / ratio_den.max(1);
        }
    }
    Ok(())
}

/// Re-prove collected statements with Poseidon2 groups; extrapolate wide widths via W=3 ratio.
pub fn benchmark_poseidon_mmcs_groups(
    stmts: &LeafMmcsGroupStatements,
    keccak: &LeafMmcsFoldGroups,
) -> Result<PoseidonMmcsBenchmarkReport, String> {
    let ratio = poseidon_keccak_group_size_ratio_w3()?;
    let mut report = PoseidonMmcsBenchmarkReport::default();

    benchmark_category(
        &stmts.val_trace,
        &keccak.val_trace,
        ratio.0,
        ratio.1,
        &mut report,
    )?;
    if let Some(q) = &stmts.val_quot {
        benchmark_category(q, &keccak.val_quot, ratio.0, ratio.1, &mut report)?;
    }
    if let Some(qb) = &stmts.val_quot_batch {
        benchmark_category(qb, &keccak.val_quot_batch, ratio.0, ratio.1, &mut report)?;
    }
    if let Some(fl) = &stmts.chal_first_layer {
        benchmark_category(fl, &keccak.chal_first_layer, ratio.0, ratio.1, &mut report)?;
    }
    let mut g_off = 0usize;
    for (_depth, depth_stmts) in &stmts.chal_commit {
        let mut stmt_off = 0usize;
        while stmt_off < depth_stmts.len() && g_off < keccak.chal_commit.len() {
            let n = keccak.chal_commit[g_off].path_count() as usize;
            let end = (stmt_off + n).min(depth_stmts.len());
            benchmark_category(
                &depth_stmts[stmt_off..end],
                std::slice::from_ref(&keccak.chal_commit[g_off]),
                ratio.0,
                ratio.1,
                &mut report,
            )?;
            stmt_off += n;
            g_off += 1;
        }
    }

    report.poseidon_total_estimate = report.poseidon_measured + report.poseidon_extrapolated;
    Ok(report)
}

/// Reference Keccak/Poseidon group STARK size ratio at W=3 depth=1 (2 paths).
fn poseidon_keccak_group_size_ratio_w3() -> Result<(u64, u64), String> {
    use super::merkle_keccak::{compress_digests_keccak, hash_val_leaf_keccak};
    use p3_field::PrimeCharacteristicRing;
    use p3_mersenne_31::Mersenne31;

    let row = vec![
        Mersenne31::from_u32(1),
        Mersenne31::from_u32(2),
        Mersenne31::from_u32(3),
    ];
    let sibling = crate::plonky3_stark::config_poseidon::pack_digest([Mersenne31::from_u32(9); 8]);
    let keccak_stmts: Vec<_> = (0usize..2)
        .map(|i| {
            let leaf = hash_val_leaf_keccak(&row);
            let root = if i.is_multiple_of(2) {
                compress_digests_keccak(leaf, sibling)
            } else {
                compress_digests_keccak(sibling, leaf)
            };
            MmcsPathStatement {
                row: row.clone(),
                siblings: vec![sibling],
                index: i,
                root,
            }
        })
        .collect();
    let poseidon_stmts: Vec<_> = (0usize..2)
        .map(|i| {
            let leaf = hash_val_leaf(&row);
            let root = if i.is_multiple_of(2) {
                compress_digests(leaf, sibling)
            } else {
                compress_digests(sibling, leaf)
            };
            MmcsPathStatement {
                row: row.clone(),
                siblings: vec![sibling],
                index: i,
                root,
            }
        })
        .collect();
    let k = generate_keccak_group_fold_proof(&keccak_stmts)?;
    let p = generate_poseidon_group_fold_proof(&poseidon_stmts)?;
    let kn = k.group_stark.len() as u64;
    let pn = p.group_stark.len() as u64;
    if kn == 0 {
        return Err("reference keccak group size zero".into());
    }
    Ok((pn, kn))
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
    let config = super::fri_fs_replay::circle_config_matching_proof(proof)?;
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

/// After nested Mmcs path prove: strip nested path STARKs for host digest verify.
///
/// **Host-only Mmcs (E5b shrink):** Poseidon/Keccak group STARKs dominated nested PCS
/// bytes. Opened rows are bound to the parent FRI proof; Merkle membership is checked
/// from retained siblings via digest verify. Empty [`LeafMmcsFoldGroups`] skips sibling
/// strip so those paths stay on the wire (cheaper than nested Circle openings at 40q).
pub fn apply_leaf_mmcs_m4c_folds(
    proof: &Proof<WqcStarkConfig>,
    trace_width: usize,
    bundle: &mut AggFriMmcsBundle,
) -> Result<LeafMmcsFoldGroups, String> {
    let _ = (proof, trace_width);
    for qp in &mut bundle.val {
        strip_fri_mmcs_path_starks(&mut qp.trace_path);
        strip_fri_mmcs_path_starks(&mut qp.quot_path);
        if let Some(ref mut batch) = qp.quot_batch {
            strip_chal_batch_starks(batch);
        }
    }
    for qp in &mut bundle.chal {
        strip_chal_batch_starks(&mut qp.first_layer);
        for path in &mut qp.commit_paths {
            strip_fri_mmcs_path_starks(path);
        }
    }
    Ok(LeafMmcsFoldGroups::default())
}

/// Env gate for post-bind Mmcs sibling stripping on the PCS wire (`WQC_PCS_STRIP_MMCS_SIBLINGS=1`).
pub const PCS_STRIP_MMCS_SIBLINGS_ENV: &str = "WQC_PCS_STRIP_MMCS_SIBLINGS";

pub fn mmcs_sibling_strip_enabled() -> bool {
    std::env::var(PCS_STRIP_MMCS_SIBLINGS_ENV)
        .map(|v| v == "1" || v.eq_ignore_ascii_case("true"))
        .unwrap_or(true)
}

/// Bytes removable from Val Mmcs query proofs when categories are group-folded.
pub fn val_mmcs_sibling_wire_bytes(bundle: &[FriValMmcsQueryProof]) -> usize {
    bundle
        .iter()
        .map(|q| {
            q.trace_siblings.len() * 32
                + q.quot_siblings.len() * 32
                + q.quot_batch
                    .as_ref()
                    .map(|b| b.siblings.len() * 32)
                    .unwrap_or(0)
        })
        .sum()
}

/// Clear redundant Merkle siblings from Val queries covered by M4c groups (post-bind wire shrink).
pub fn strip_val_mmcs_siblings_for_groups(
    bundle: &mut [FriValMmcsQueryProof],
    groups: &LeafMmcsFoldGroups,
) -> usize {
    if !mmcs_sibling_strip_enabled() {
        return 0;
    }
    let before = val_mmcs_sibling_wire_bytes(bundle);
    if !groups.val_trace.is_empty() {
        for qp in bundle.iter_mut() {
            qp.trace_siblings.clear();
        }
    }
    if !groups.val_quot.is_empty() {
        for qp in bundle.iter_mut() {
            qp.quot_siblings.clear();
        }
    }
    // `val_quot_batch` uses `FriChalBatchPathProof::siblings` — hydrate not wired yet; skip strip.
    before.saturating_sub(val_mmcs_sibling_wire_bytes(bundle))
}

/// Refill stripped Val siblings from the embedded uni-STARK FRI openings before host bind.
pub fn hydrate_val_mmcs_siblings_from_proof(
    proof: &Proof<WqcStarkConfig>,
    bundle: &mut [FriValMmcsQueryProof],
    trace_width: usize,
) -> Result<(), String> {
    use super::fri_fs_replay::{
        circle_config_matching_proof, decode_pcs_view, replay_fri_challenges,
    };
    use super::fri_ro::decode_input_proof;
    use p3_commit::{Pcs, PolynomialSpace};

    let n = fri_queries_from_proof(proof)?;
    if bundle.len() != n {
        return Err(format!("val mmcs len {}, want {n}", bundle.len()));
    }
    let chal = replay_fri_challenges(proof, trace_width)?;
    let view = decode_pcs_view(proof)?;
    let config = circle_config_matching_proof(proof)?;
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

    for (q, qp) in bundle.iter_mut().enumerate() {
        let query_index = chal.query_indices[q];
        let input = decode_input_proof(&view.fri_proof.query_proofs[q].input_proof)?;
        let t_idx = query_index >> (log_global_max_height - trace_log_height);
        if qp.trace_siblings.is_empty() {
            qp.trace_siblings = input.input_openings[0].opening_proof.clone();
        }
        if qp.quot_siblings.is_empty() {
            qp.quot_siblings = input.input_openings[1].opening_proof.clone();
        }
        if qp.trace_index as usize != t_idx {
            return Err(format!("q{q}: trace index mismatch after hydrate"));
        }
        if qp.trace_siblings != input.input_openings[0].opening_proof
            || qp.quot_siblings != input.input_openings[1].opening_proof
        {
            return Err(format!("q{q}: hydrated siblings mismatch FRI opening"));
        }
    }
    Ok(())
}

/// Bytes removable from Chal Mmcs query proofs when categories are group-folded.
pub fn chal_mmcs_sibling_wire_bytes(bundle: &[FriChalMmcsQueryProof]) -> usize {
    bundle
        .iter()
        .map(|q| {
            q.first_layer.siblings.len() * 32
                + q.commit_siblings
                    .iter()
                    .map(|s| s.len() * 32)
                    .sum::<usize>()
        })
        .sum()
}

/// Clear redundant Merkle siblings from Chal queries covered by M4c groups (post-bind wire shrink).
pub fn strip_chal_mmcs_siblings_for_groups(
    bundle: &mut [FriChalMmcsQueryProof],
    groups: &LeafMmcsFoldGroups,
) -> usize {
    if !mmcs_sibling_strip_enabled() {
        return 0;
    }
    let before = chal_mmcs_sibling_wire_bytes(bundle);
    let merged_fl_commit = groups.chal_first_layer.is_empty() && !groups.chal_commit.is_empty();
    let pcs_combined = groups.pcs_combined;
    if !groups.chal_first_layer.is_empty() || merged_fl_commit || pcs_combined {
        for qp in bundle.iter_mut() {
            qp.first_layer.siblings.clear();
        }
    }
    if !groups.chal_commit.is_empty() || pcs_combined {
        if merged_fl_commit || pcs_combined {
            for qp in bundle.iter_mut() {
                for sibs in qp.commit_siblings.iter_mut() {
                    sibs.clear();
                }
            }
        } else {
            let grouped_depths: Vec<usize> = {
                let mut d: Vec<_> = groups
                    .chal_commit
                    .iter()
                    .map(|g| g.depth() as usize)
                    .collect();
                d.sort_unstable();
                d.dedup();
                d
            };
            for qp in bundle.iter_mut() {
                for (i, path) in qp.commit_paths.iter().enumerate() {
                    if grouped_depths.contains(&(path.depth as usize)) {
                        if let Some(sibs) = qp.commit_siblings.get_mut(i) {
                            sibs.clear();
                        }
                    }
                }
            }
        }
    }
    before.saturating_sub(chal_mmcs_sibling_wire_bytes(bundle))
}

/// Refill stripped Chal siblings from the embedded uni-STARK FRI openings before host bind.
pub fn hydrate_chal_mmcs_siblings_from_proof(
    proof: &Proof<WqcStarkConfig>,
    bundle: &mut [FriChalMmcsQueryProof],
    trace_width: usize,
) -> Result<(), String> {
    use super::fri_fs_replay::decode_pcs_view;
    use super::fri_ro::decode_input_proof;

    let _ = trace_width;
    let n = fri_queries_from_proof(proof)?;
    if bundle.len() != n {
        return Err(format!("chal mmcs len {}, want {n}", bundle.len()));
    }
    let view = decode_pcs_view(proof)?;

    for (q, qp) in bundle.iter_mut().enumerate() {
        let fri_qp = &view.fri_proof.query_proofs[q];
        let input = decode_input_proof(&fri_qp.input_proof)?;
        if qp.first_layer.siblings.is_empty() {
            qp.first_layer.siblings = input.first_layer_proof.clone();
        }
        if qp.first_layer.siblings != input.first_layer_proof {
            return Err(format!("q{q}: hydrated first_layer siblings mismatch"));
        }
        let openings = &fri_qp.commit_phase_openings;
        if qp.commit_siblings.len() != openings.len() {
            return Err(format!(
                "q{q}: commit_siblings len {}, want {}",
                qp.commit_siblings.len(),
                openings.len()
            ));
        }
        for (round, opening) in openings.iter().enumerate() {
            if qp.commit_siblings[round].is_empty() {
                qp.commit_siblings[round] = opening.opening_proof.clone();
            }
            if qp.commit_siblings[round] != opening.opening_proof {
                return Err(format!(
                    "q{q} round {round}: hydrated commit siblings mismatch"
                ));
            }
        }
    }
    Ok(())
}

/// Bind leaf Mmcs openings using M4c groups where present; nested verify otherwise.
pub fn bind_leaf_mmcs_with_groups(
    proof: &Proof<WqcStarkConfig>,
    bundle: &AggFriMmcsBundle,
    groups: &LeafMmcsFoldGroups,
    trace_width: usize,
) -> Result<(), String> {
    use super::fri_mmcs_bind::{bind_fri_chal_mmcs_bundle_width, bind_fri_val_mmcs_bundle_width};

    let pcs_combined = {
        let trace_stmts = collect_val_trace_stmts(proof, trace_width, &bundle.val)?;
        let batch_n = collect_val_quot_batch_stmts(proof, trace_width, &bundle.val)?
            .map(|s| s.len())
            .unwrap_or(0);
        let quot_n = if batch_n == 0 {
            collect_val_quot_stmts(proof, trace_width, &bundle.val)?
                .map(|s| s.len())
                .unwrap_or(0)
        } else {
            0
        };
        let val_n = if batch_n > 0 {
            trace_stmts.len() + batch_n
        } else {
            trace_stmts.len() + quot_n
        };
        let fl_len = collect_chal_first_layer_stmts(proof, trace_width, &bundle.chal)?
            .map(|s| s.len())
            .unwrap_or(0);
        let commit_len: usize =
            collect_chal_commit_stmts_by_depth(proof, trace_width, &bundle.chal)?
                .iter()
                .map(|(_, s)| s.len())
                .sum();
        groups.pcs_combined || pcs_val_chal_merged(groups, val_n, fl_len + commit_len)
    };

    if pcs_combined {
        let mut pcs_all = Vec::new();
        let trace_stmts = collect_val_trace_stmts(proof, trace_width, &bundle.val)?;
        pcs_all.extend_from_slice(&trace_stmts);
        if let Some(batch) = collect_val_quot_batch_stmts(proof, trace_width, &bundle.val)? {
            pcs_all.extend(batch);
        } else if let Some(quot) = collect_val_quot_stmts(proof, trace_width, &bundle.val)? {
            pcs_all.extend(quot);
        }
        if let Some(fl) = collect_chal_first_layer_stmts(proof, trace_width, &bundle.chal)? {
            pcs_all.extend(fl);
        }
        for (_, stmts) in collect_chal_commit_stmts_by_depth(proof, trace_width, &bundle.chal)? {
            pcs_all.extend(stmts);
        }
        verify_group_chunks(&pcs_all, &groups.val_trace, "val+chal pcs")?;
    }

    let val_needs_custom = !groups.val_trace.is_empty()
        || !groups.val_quot.is_empty()
        || !groups.val_quot_batch.is_empty()
        || bundle.val.iter().any(|q| {
            path_starks_stripped(&q.trace_path)
                || path_starks_stripped(&q.quot_path)
                || q.quot_batch.as_ref().is_some_and(batch_starks_stripped)
        });
    if val_needs_custom {
        bind_val_with_groups(proof, &bundle.val, groups, trace_width, pcs_combined)?;
    } else {
        bind_fri_val_mmcs_bundle_width(proof, &bundle.val, trace_width)?;
    }

    let chal_needs_custom = pcs_combined
        || !groups.chal_first_layer.is_empty()
        || !groups.chal_commit.is_empty()
        || bundle.chal.iter().any(|q| {
            batch_starks_stripped(&q.first_layer) || q.commit_paths.iter().any(path_starks_stripped)
        });
    if chal_needs_custom {
        bind_chal_with_groups(proof, &bundle.chal, groups, trace_width, pcs_combined)?;
    } else {
        bind_fri_chal_mmcs_bundle_width(proof, &bundle.chal, trace_width)?;
    }
    Ok(())
}

/// Verify a chunked category: each group covers the next `path_count` statements,
/// and the chunks must exactly partition `stmts` (order-preserving, env-independent).
fn verify_group_chunks(
    stmts: &[MmcsPathStatement],
    groups: &[MmcsGroupFoldProof],
    label: &str,
) -> Result<(), String> {
    let mut off = 0usize;
    for g in groups {
        let n = g.path_count() as usize;
        let end = off
            .checked_add(n)
            .filter(|&e| e <= stmts.len())
            .ok_or_else(|| format!("{label} chunk [{off}+{n}] exceeds {} stmts", stmts.len()))?;
        let chunk = &stmts[off..end];
        let ok = match g {
            MmcsGroupFoldProof::Keccak(p) => verify_keccak_group_fold_proof(chunk, p),
            MmcsGroupFoldProof::Poseidon(p) => verify_poseidon_group_fold_proof(chunk, p),
        };
        if !ok {
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
    pcs_combined: bool,
) -> Result<(), String> {
    use super::fri_mmcs_bind::{verify_chal_batch_path_digests, verify_chal_batch_path_replay};

    let n = fri_queries_from_proof(proof)?;
    if bundle.len() != n {
        return Err(format!("val mmcs len {}, want {n}", bundle.len()));
    }
    let chal = replay_fri_challenges(proof, trace_width)?;
    let view = decode_pcs_view(proof)?;
    let config = super::fri_fs_replay::circle_config_matching_proof(proof)?;
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

    let trace_stmts = collect_val_trace_stmts(proof, trace_width, bundle)?;
    let batch_opt = collect_val_quot_batch_stmts(proof, trace_width, bundle)?;
    let batch_n = batch_opt.as_ref().map(|s| s.len()).unwrap_or(0);
    let val_trace_n: usize = groups
        .val_trace
        .iter()
        .map(|g| g.path_count() as usize)
        .sum();
    // When `pcs_combined`, the shared group STARK is verified in `bind_leaf` before
    // this call; here we only check host digests (treat like val_merged for quot).
    let val_merged = pcs_combined
        || (groups.val_quot_batch.is_empty()
            && groups.val_quot.is_empty()
            && !groups.val_trace.is_empty()
            && batch_n > 0
            && val_trace_n == trace_stmts.len() + batch_n);

    if pcs_combined {
        // Group STARK already verified against val‖chal; bind digests only.
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
    } else if val_merged {
        let mut all = Vec::with_capacity(trace_stmts.len() + batch_n);
        all.extend_from_slice(&trace_stmts);
        all.extend_from_slice(batch_opt.as_ref().unwrap());
        verify_group_chunks(&all, &groups.val_trace, "val trace+quot_batch")?;
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
    } else if !groups.val_trace.is_empty() {
        verify_group_chunks(&trace_stmts, &groups.val_trace, "val trace")?;
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
        let stmts = batch_opt
            .clone()
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
            if !groups.val_quot_batch.is_empty() || val_merged {
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
    pcs_combined: bool,
) -> Result<(), String> {
    let n = fri_queries_from_proof(proof)?;
    if bundle.len() != n {
        return Err(format!("chal mmcs len {}, want {n}", bundle.len()));
    }
    let chal = replay_fri_challenges(proof, trace_width)?;
    let view = decode_pcs_view(proof)?;
    let fl_root = commitment_root_chal(&view.first_layer_commitment)?;

    let fl_opt = collect_chal_first_layer_stmts(proof, trace_width, bundle)?;
    let by_depth = collect_chal_commit_stmts_by_depth(proof, trace_width, bundle)?;
    let fl_len = fl_opt.as_ref().map(|s| s.len()).unwrap_or(0);
    let commit_len: usize = by_depth.iter().map(|(_, s)| s.len()).sum();
    let chal_commit_n: usize = groups
        .chal_commit
        .iter()
        .map(|g| g.path_count() as usize)
        .sum();
    let chal_merged = !pcs_combined
        && groups.chal_first_layer.is_empty()
        && !groups.chal_commit.is_empty()
        && chal_commit_n == fl_len + commit_len;

    if pcs_combined {
        // Shared val+chal group already verified in `bind_leaf`.
    } else if chal_merged {
        let mut chal_all = Vec::with_capacity(fl_len + commit_len);
        if let Some(ref fl) = fl_opt {
            chal_all.extend_from_slice(fl);
        }
        for (_, stmts) in &by_depth {
            chal_all.extend_from_slice(stmts);
        }
        verify_group_chunks(&chal_all, &groups.chal_commit, "chal fl+commit")?;
    } else {
        if !groups.chal_first_layer.is_empty() {
            let stmts = fl_opt.as_ref().ok_or_else(|| {
                "chal first_layer group present but statements unavailable".to_string()
            })?;
            verify_group_chunks(stmts, &groups.chal_first_layer, "chal first_layer")?;
        }

        // Host-only Mmcs: no commit groups — digests checked per query below.
        if !groups.chal_commit.is_empty() {
            let mut group_iter = groups.chal_commit.iter().peekable();
            for (depth, stmts) in &by_depth {
                let eligible = m4b_width_eligible(CHAL_LEAF_WIDTH)
                    && stmts.iter().all(|s| s.siblings.len() == *depth);
                if eligible && !stmts.is_empty() {
                    let mut off = 0usize;
                    while off < stmts.len() {
                        let g = group_iter.next().ok_or_else(|| {
                            format!("missing chal commit group for depth {depth}")
                        })?;
                        if g.depth() as usize != *depth {
                            return Err(format!(
                                "chal commit group depth {} != expected {depth}",
                                g.depth()
                            ));
                        }
                        let n = g.path_count() as usize;
                        let end = off
                            .checked_add(n)
                            .filter(|&e| e <= stmts.len())
                            .ok_or_else(|| format!("chal commit depth {depth} chunk overflow"))?;
                        verify_group_chunks(
                            &stmts[off..end],
                            std::slice::from_ref(g),
                            "chal commit",
                        )?;
                        off = end;
                    }
                }
            }
            if group_iter.next().is_some() {
                return Err("extra chal commit groups".into());
            }
        }
    }

    let chal_grouped = pcs_combined || chal_merged;

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
        if !groups.chal_first_layer.is_empty() || (chal_grouped && fl_len > 0) {
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
            let grouped = chal_grouped
                || groups
                    .chal_commit
                    .iter()
                    .any(|g| g.depth() as usize == path.depth as usize);
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
    use super::super::fri_mmcs_group_m4b::KeccakGroupFoldProof;
    use super::super::mmcs_group_fold::MmcsGroupFoldProof;
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

    #[test]
    fn strip_val_siblings_clears_grouped_categories() {
        let mut bundle = vec![FriValMmcsQueryProof {
            trace_index: 0,
            quot_index: 0,
            trace_siblings: vec![[1u8; 32], [2u8; 32]],
            quot_siblings: vec![[3u8; 32]],
            trace_path: FriMmcsPathProof {
                depth: 1,
                leaf_width: 3,
                leaf_digest: [0u8; 32],
                layer_digests: vec![[0u8; 32]],
                fold_stark: vec![],
                leaf_keccak: Keccak256StarkProof {
                    msg_len: 12,
                    digest: [0u8; 32],
                    stark: vec![],
                },
                compress_starks: vec![Keccak256StarkProof {
                    msg_len: 64,
                    digest: [0u8; 32],
                    stark: vec![],
                }],
            },
            quot_path: FriMmcsPathProof {
                depth: 1,
                leaf_width: 3,
                leaf_digest: [0u8; 32],
                layer_digests: vec![[0u8; 32]],
                fold_stark: vec![],
                leaf_keccak: Keccak256StarkProof {
                    msg_len: 12,
                    digest: [0u8; 32],
                    stark: vec![],
                },
                compress_starks: vec![Keccak256StarkProof {
                    msg_len: 64,
                    digest: [0u8; 32],
                    stark: vec![],
                }],
            },
            quot_batch: None,
        }];
        let groups = LeafMmcsFoldGroups {
            val_trace: vec![MmcsGroupFoldProof::Keccak(KeccakGroupFoldProof {
                path_count: 1,
                depth: 1,
                leaf_width: 3,
                group_stark: vec![1],
            })],
            val_quot: vec![MmcsGroupFoldProof::Keccak(KeccakGroupFoldProof {
                path_count: 1,
                depth: 1,
                leaf_width: 3,
                group_stark: vec![1],
            })],
            ..Default::default()
        };
        let saved = strip_val_mmcs_siblings_for_groups(&mut bundle, &groups);
        assert_eq!(saved, 32 * (2 + 1));
        assert!(bundle[0].trace_siblings.is_empty());
        assert!(bundle[0].quot_siblings.is_empty());
    }

    #[test]
    fn strip_chal_siblings_clears_grouped_categories() {
        let mut bundle = vec![FriChalMmcsQueryProof {
            first_layer: FriChalBatchPathProof {
                index: 0,
                siblings: vec![[1u8; 32], [2u8; 32]],
                leaf_rows: vec![vec![Mersenne31::ZERO; 6]],
                leaf_keccs: vec![],
                leaf_digests: vec![[0u8; 32]],
                sib_compresses: vec![],
                sib_layer_digests: vec![[0u8; 32], [0u8; 32]],
                inject_compresses: vec![],
                inject_digests: vec![],
                inject_leaf_indices: vec![],
            },
            commit_indices: vec![0, 1],
            commit_siblings: vec![vec![[3u8; 32]], vec![[4u8; 32], [5u8; 32]]],
            commit_paths: vec![
                FriMmcsPathProof {
                    depth: 1,
                    leaf_width: 6,
                    leaf_digest: [0u8; 32],
                    layer_digests: vec![[0u8; 32]],
                    fold_stark: vec![],
                    leaf_keccak: Keccak256StarkProof {
                        msg_len: 24,
                        digest: [0u8; 32],
                        stark: vec![],
                    },
                    compress_starks: vec![],
                },
                FriMmcsPathProof {
                    depth: 2,
                    leaf_width: 6,
                    leaf_digest: [0u8; 32],
                    layer_digests: vec![[0u8; 32], [0u8; 32]],
                    fold_stark: vec![],
                    leaf_keccak: Keccak256StarkProof {
                        msg_len: 24,
                        digest: [0u8; 32],
                        stark: vec![],
                    },
                    compress_starks: vec![],
                },
            ],
        }];
        let groups = LeafMmcsFoldGroups {
            chal_first_layer: vec![MmcsGroupFoldProof::Keccak(KeccakGroupFoldProof {
                path_count: 1,
                depth: 2,
                leaf_width: 6,
                group_stark: vec![1],
            })],
            chal_commit: vec![MmcsGroupFoldProof::Keccak(KeccakGroupFoldProof {
                path_count: 1,
                depth: 1,
                leaf_width: 6,
                group_stark: vec![1],
            })],
            ..Default::default()
        };
        let saved = strip_chal_mmcs_siblings_for_groups(&mut bundle, &groups);
        // first_layer 2 sibs + commit depth-1 (1 sib); depth-2 commit kept
        assert_eq!(saved, 32 * (2 + 1));
        assert!(bundle[0].commit_siblings[0].is_empty());
        assert_eq!(bundle[0].commit_siblings[1].len(), 2);
    }

    #[test]
    fn strip_chal_merged_fl_commit_clears_all_siblings() {
        let mut bundle = vec![FriChalMmcsQueryProof {
            first_layer: FriChalBatchPathProof {
                index: 0,
                siblings: vec![[1u8; 32], [2u8; 32]],
                leaf_rows: vec![],
                leaf_keccs: vec![],
                leaf_digests: vec![],
                sib_compresses: vec![],
                sib_layer_digests: vec![],
                inject_compresses: vec![],
                inject_digests: vec![],
                inject_leaf_indices: vec![],
            },
            commit_siblings: vec![vec![[3u8; 32]], vec![[4u8; 32], [5u8; 32]]],
            commit_indices: vec![0, 0],
            commit_paths: vec![
                FriMmcsPathProof {
                    depth: 1,
                    leaf_width: 6,
                    leaf_digest: [0u8; 32],
                    layer_digests: vec![[0u8; 32]],
                    fold_stark: vec![],
                    leaf_keccak: Keccak256StarkProof {
                        msg_len: 24,
                        digest: [0u8; 32],
                        stark: vec![],
                    },
                    compress_starks: vec![],
                },
                FriMmcsPathProof {
                    depth: 2,
                    leaf_width: 6,
                    leaf_digest: [0u8; 32],
                    layer_digests: vec![[0u8; 32], [0u8; 32]],
                    fold_stark: vec![],
                    leaf_keccak: Keccak256StarkProof {
                        msg_len: 24,
                        digest: [0u8; 32],
                        stark: vec![],
                    },
                    compress_starks: vec![],
                },
            ],
        }];
        let groups = LeafMmcsFoldGroups {
            chal_commit: vec![MmcsGroupFoldProof::Keccak(KeccakGroupFoldProof {
                path_count: 3,
                depth: 2,
                leaf_width: 6,
                group_stark: vec![1],
            })],
            ..Default::default()
        };
        let saved = strip_chal_mmcs_siblings_for_groups(&mut bundle, &groups);
        assert_eq!(saved, 32 * (2 + 1 + 2));
        assert!(bundle[0].first_layer.siblings.is_empty());
        assert!(bundle[0].commit_siblings.iter().all(|s| s.is_empty()));
    }
}

//! Leaf uni-STARK PCS opening certificates (R3-M3e / M4c).
//!
//! Mirrors AggregationAir M3d flow on a leaf `Proof`: host OOD, FriFold, DeepRo
//! (quot + leaf-trace), and in-circuit Val/Challenge Mmcs. Skips natural-row LDE
//! rebuild (no prover_data); `merkle_fold` reuses query-0 ValMmcs trace path.
//! M4c folds eligible single-matrix paths into `LeafMmcsFoldGroups` and strips
//! nested Keccak STARKs from the wire.

use p3_commit::Mmcs;
use p3_mersenne_31::Mersenne31;
use p3_uni_stark::Proof;
use sha3::{Digest, Sha3_256};

use crate::aggregation::{
    is_born_leaf_proof, is_trajectory_leaf_proof, parse_leaf_binding, parsed_to_stark_context,
};
use crate::aggregation::{parse_born_leaf_prefix, parse_trajectory_leaf_prefix};
use crate::distribution::base_proof_without_distribution_tail;
use crate::plonky3_stark::config::{ValMmcs, WqcStarkConfig};
use crate::plonky3_stark::shot_sampling_stark::split_shot_sampling_from_bundle;
use crate::plonky3_stark::transcript_born::BORN_STARK_INNER_MARKER;
use crate::plonky3_stark::transcript_trajectory_stark::{
    TRAJ_MARG_STARK_INNER_MARKER, TRAJ_SHOT_STARK_INNER_MARKER,
};
use crate::plonky3_stark::transcript_v2::decode_proof_v2_plonky3_bytes;
use crate::plonky3_stark::{split_born_stark_tail, split_trajectory_stark_tail};
use crate::trajectory::base_proof_without_aux_tails;

use super::deep_ro_air::{verify_deep_ro_proof, DeepRoStepProof};
use super::deep_ro_bind::{bind_deep_ro_leaf_bundle_to_proof, deep_ro_bundle_from_leaf_proof};
use super::deep_ro_leaf_trace_air::{verify_deep_ro_leaf_trace_proof, DeepRoLeafTraceStepProof};
use super::fri_fold_air::{verify_fri_fold_proof, verify_fri_fold_y_proof, FriFoldStepProof};
use super::fri_fold_bind::{
    bind_fri_fold_bundle_to_proof_width, fri_fold_bundle_from_proof, LEAF_FRI_PROVEN_QUERIES,
};
use super::fri_mmcs_bind::{
    bind_fri_mmcs_bundle_to_proof_width, fri_mmcs_bundle_from_proof, AggFriMmcsBundle,
    FriChalMmcsQueryProof, FriValMmcsQueryProof,
};
use super::fri_mmcs_m4c::{
    apply_leaf_mmcs_m4c_folds, bind_leaf_mmcs_with_groups, LeafMmcsFoldGroups,
};
use super::fri_mmcs_path::FriMmcsPathProof;
use super::ood_air::{verify_ood_proof, OodStepProof};
use super::ood_bind::verify_leaf_ood_step;
use super::ood_native::generate_leaf_ood_proof;
use super::opening_cert::LEAF_PCS_MAX_SIBLINGS;
use super::pcs_geom::{
    validate_born_recursion_width, LeafKind, LEAF_DEEP_RO_MAX_WIDTH, UNITARY_TRACE_WIDTH,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LeafPcsCertificate {
    pub kind: LeafKind,
    pub trace_width: u32,
    pub degree_bits: u32,
    /// SHA3-256 of (kind byte ‖ postcard of trace commitment roots).
    pub stmt_digest: [u8; 32],
    pub trace_commitment: [u8; 32],
    /// LDE statement open deferred for leaves (always 0 / empty).
    pub lde_index: u32,
    pub lde_row: Vec<Mersenne31>,
    pub siblings: Vec<[u8; 32]>,
    /// Query-0 ValMmcs trace path (may be STARK-stripped when `mmcs_groups.val_trace` is set).
    pub merkle_fold: FriMmcsPathProof,
    /// M4c group folds for eligible single-matrix Val/Chal paths (`LEAF_MMCS_FOLD_V`).
    pub mmcs_groups: LeafMmcsFoldGroups,
    pub fri_fold_ys: Vec<FriFoldStepProof>,
    pub fri_folds: Vec<FriFoldStepProof>,
    pub deep_ros: Vec<DeepRoStepProof>,
    pub deep_ro_traces: Vec<DeepRoLeafTraceStepProof>,
    /// R3 OOD: in-circuit constraint fold + quotient check at ζ.
    pub ood: OodStepProof,
    pub fri_val_mmcs: Vec<FriValMmcsQueryProof>,
    pub fri_chal_mmcs: Vec<FriChalMmcsQueryProof>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LeafPcsBundle {
    pub certs: Vec<LeafPcsCertificate>,
}

fn commitment_root(com: &<ValMmcs as Mmcs<Mersenne31>>::Commitment) -> Result<[u8; 32], String> {
    com.roots()
        .first()
        .copied()
        .ok_or_else(|| "empty MerkleCap commitment".into())
}

/// `sha3_256(kind ‖ postcard(trace commitment))`.
pub fn leaf_stmt_digest(kind: LeafKind, proof: &Proof<WqcStarkConfig>) -> Result<[u8; 32], String> {
    let mut h = Sha3_256::new();
    h.update([kind as u8]);
    let roots = postcard::to_allocvec(&proof.commitments.trace)
        .map_err(|e| format!("postcard encode trace commitment: {e}"))?;
    h.update(&roots);
    let dig = h.finalize();
    let mut out = [0u8; 32];
    out.copy_from_slice(&dig);
    Ok(out)
}

fn path_self_check_val(qp: &FriValMmcsQueryProof) -> bool {
    let trace_ok =
        qp.trace_path.depth as usize == qp.trace_siblings.len() && !qp.trace_siblings.is_empty();
    if !trace_ok {
        return false;
    }
    if qp.quot_batch.is_some() {
        !qp.quot_siblings.is_empty()
    } else {
        qp.quot_path.depth as usize == qp.quot_siblings.len() && !qp.quot_siblings.is_empty()
    }
}

fn path_self_check_chal(qp: &FriChalMmcsQueryProof) -> bool {
    !qp.first_layer.siblings.is_empty()
        && qp.commit_paths.len() == qp.commit_siblings.len()
        && qp.commit_paths.len() == qp.commit_indices.len()
        && qp
            .commit_paths
            .iter()
            .zip(qp.commit_siblings.iter())
            .all(|(p, s)| p.depth as usize == s.len() && !s.is_empty())
}

fn num_outcomes_from_width(width: usize) -> Result<usize, String> {
    validate_born_recursion_width(width)
}

fn validate_leaf_recursion_trace_width(kind: LeafKind, trace_width: usize) -> Result<(), String> {
    if trace_width == 0 || trace_width > LEAF_DEEP_RO_MAX_WIDTH {
        return Err(format!(
            "unsupported leaf trace width {trace_width} (max W={LEAF_DEEP_RO_MAX_WIDTH} for in-circuit Keccak)"
        ));
    }
    match kind {
        LeafKind::Unitary => {
            if trace_width != UNITARY_TRACE_WIDTH {
                return Err(format!(
                    "unitary width {trace_width} != {UNITARY_TRACE_WIDTH}"
                ));
            }
        }
        LeafKind::Born | LeafKind::TrajMarginal => {
            validate_born_recursion_width(trace_width)?;
        }
        LeafKind::ShotSampling => {}
    }
    Ok(())
}

enum LeafOodParams {
    Unitary,
    Distribution { num_outcomes: usize },
    Shot,
}

fn ood_params_for_kind(
    kind: LeafKind,
    proof: &Proof<WqcStarkConfig>,
) -> Result<LeafOodParams, String> {
    match kind {
        LeafKind::Unitary => Ok(LeafOodParams::Unitary),
        LeafKind::Born | LeafKind::TrajMarginal => {
            let width = proof.opened_values.trace_local.len();
            Ok(LeafOodParams::Distribution {
                num_outcomes: num_outcomes_from_width(width)?,
            })
        }
        LeafKind::ShotSampling => Ok(LeafOodParams::Shot),
    }
}

/// Builds a PCS certificate for a leaf uni-STARK proof (FRI-path focus).
pub fn build_leaf_pcs_certificate(
    proof: &Proof<WqcStarkConfig>,
    kind: LeafKind,
    stmt_digest: [u8; 32],
) -> Result<LeafPcsCertificate, String> {
    let expected = leaf_stmt_digest(kind, proof)?;
    if expected != stmt_digest {
        return Err("stmt_digest mismatch".into());
    }
    let trace_width = proof.opened_values.trace_local.len();
    validate_leaf_recursion_trace_width(kind, trace_width)?;

    let ood_params = ood_params_for_kind(kind, proof)?;
    let num_outcomes = match ood_params {
        LeafOodParams::Distribution { num_outcomes } => num_outcomes,
        _ => 0,
    };
    let ood = generate_leaf_ood_proof(proof, kind, num_outcomes)
        .map_err(|e| format!("R3-M3e leaf OOD prove failed: {e}"))?;
    if !verify_ood_proof(&ood) {
        return Err("R3-M3e leaf OOD self-check failed".into());
    }

    let fri_bundle = fri_fold_bundle_from_proof(proof, trace_width)
        .map_err(|e| format!("R3-M3e FRI fold prove failed: {e}"))?;
    for (i, fold) in fri_bundle.fold_ys.iter().enumerate() {
        if !verify_fri_fold_y_proof(fold) {
            return Err(format!("R3-M3e FRI fold_y self-check failed at {i}"));
        }
    }
    for (i, fold) in fri_bundle.fold_xs.iter().enumerate() {
        if !verify_fri_fold_proof(fold) {
            return Err(format!("R3-M3e FRI fold_x self-check failed at {i}"));
        }
    }

    let deep_ros;
    let deep_ro_traces;
    if proof.opened_values.quotient_chunks.len() == 1 {
        let deep_bundle = deep_ro_bundle_from_leaf_proof(proof, trace_width)
            .map_err(|e| format!("R3-M3e DeepRo bundle prove failed: {e}"))?;
        for (i, deep) in deep_bundle.deep_ros.iter().enumerate() {
            if !verify_deep_ro_proof(deep) {
                return Err(format!("R3-M3e DeepRo self-check failed at {i}"));
            }
        }
        for (i, deep) in deep_bundle.deep_ro_traces.iter().enumerate() {
            if !verify_deep_ro_leaf_trace_proof(deep) {
                return Err(format!("R3-M3e DeepRoLeafTrace self-check failed at {i}"));
            }
        }
        bind_deep_ro_leaf_bundle_to_proof(
            proof,
            &deep_bundle.deep_ros,
            &deep_bundle.deep_ro_traces,
            &fri_bundle.fold_ys,
            trace_width,
        )
        .map_err(|e| format!("R3-M3e DeepRo bind failed: {e}"))?;
        deep_ros = deep_bundle.deep_ros;
        deep_ro_traces = deep_bundle.deep_ro_traces;
    } else {
        // Multi-chunk / same-height merge: FriFold RO reconstruct covers DEEP+λ;
        // per-matrix DeepRo STARKs are a follow-up (combined bind).
        deep_ros = Vec::new();
        deep_ro_traces = Vec::new();
    }

    let mmcs_bundle = fri_mmcs_bundle_from_proof(proof, trace_width)
        .map_err(|e| format!("R3-M3e FRI Mmcs prove failed: {e}"))?;
    if mmcs_bundle.val.len() != LEAF_FRI_PROVEN_QUERIES
        || mmcs_bundle.chal.len() != LEAF_FRI_PROVEN_QUERIES
    {
        return Err(format!(
            "unexpected FRI Mmcs counts: val={}, chal={}",
            mmcs_bundle.val.len(),
            mmcs_bundle.chal.len()
        ));
    }
    for (i, qp) in mmcs_bundle.val.iter().enumerate() {
        if !path_self_check_val(qp) {
            return Err(format!("R3-M3e ValMmcs self-check failed at query {i}"));
        }
        if qp.trace_siblings.len() > LEAF_PCS_MAX_SIBLINGS
            || qp.quot_siblings.len() > LEAF_PCS_MAX_SIBLINGS
        {
            return Err(format!("R3-M3e ValMmcs siblings too deep at query {i}"));
        }
    }
    for (i, qp) in mmcs_bundle.chal.iter().enumerate() {
        if !path_self_check_chal(qp) {
            return Err(format!(
                "R3-M3e ChallengeMmcs self-check failed at query {i}"
            ));
        }
    }
    bind_fri_mmcs_bundle_to_proof_width(proof, &mmcs_bundle, trace_width)
        .map_err(|e| format!("R3-M3e FRI Mmcs bind failed: {e}"))?;

    let mut mmcs_bundle = mmcs_bundle;
    let mmcs_groups = apply_leaf_mmcs_m4c_folds(proof, trace_width, &mut mmcs_bundle)
        .map_err(|e| format!("R3-M4c Mmcs group fold failed: {e}"))?;
    bind_leaf_mmcs_with_groups(proof, &mmcs_bundle, &mmcs_groups, trace_width)
        .map_err(|e| format!("R3-M4c Mmcs group bind failed: {e}"))?;

    let trace_commitment = commitment_root(&proof.commitments.trace)?;
    let merkle_fold = mmcs_bundle.val[0].trace_path.clone();

    Ok(LeafPcsCertificate {
        kind,
        trace_width: trace_width as u32,
        degree_bits: proof.degree_bits as u32,
        stmt_digest,
        trace_commitment,
        lde_index: 0,
        lde_row: Vec::new(),
        siblings: Vec::new(),
        merkle_fold,
        mmcs_groups,
        fri_fold_ys: fri_bundle.fold_ys,
        fri_folds: fri_bundle.fold_xs,
        deep_ros,
        deep_ro_traces,
        ood,
        fri_val_mmcs: mmcs_bundle.val,
        fri_chal_mmcs: mmcs_bundle.chal,
    })
}

/// Host-verifies a leaf PCS certificate against the Plonky3 proof.
pub fn verify_leaf_pcs_certificate(
    proof: &Proof<WqcStarkConfig>,
    cert: &LeafPcsCertificate,
) -> bool {
    let expect_stmt = match leaf_stmt_digest(cert.kind, proof) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("[LeafPcsCertificate] Failed: stmt: {e}");
            return false;
        }
    };
    if expect_stmt != cert.stmt_digest {
        eprintln!("[LeafPcsCertificate] Failed: stmt_digest mismatch");
        return false;
    }
    let trace_width = proof.opened_values.trace_local.len();
    if cert.trace_width as usize != trace_width || cert.degree_bits as usize != proof.degree_bits {
        eprintln!("[LeafPcsCertificate] Failed: geom mismatch");
        return false;
    }
    if validate_leaf_recursion_trace_width(cert.kind, trace_width).is_err() {
        eprintln!("[LeafPcsCertificate] Failed: trace width exceeds recursion Keccak cap");
        return false;
    }
    let root = match commitment_root(&proof.commitments.trace) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("[LeafPcsCertificate] Failed: {e}");
            return false;
        }
    };
    if root != cert.trace_commitment {
        eprintln!("[LeafPcsCertificate] Failed: commitment mismatch");
        return false;
    }

    if !verify_ood_proof(&cert.ood) {
        eprintln!("[LeafPcsCertificate] Failed: OOD STARK");
        return false;
    }
    if let Err(e) = verify_leaf_ood_step(proof, &cert.ood, cert.kind) {
        eprintln!("[LeafPcsCertificate] Failed: OOD bind: {e}");
        return false;
    }

    for (i, fold) in cert.fri_fold_ys.iter().enumerate() {
        if !verify_fri_fold_y_proof(fold) {
            eprintln!("[LeafPcsCertificate] Failed: FRI fold_y at {i}");
            return false;
        }
    }
    for (i, fold) in cert.fri_folds.iter().enumerate() {
        if !verify_fri_fold_proof(fold) {
            eprintln!("[LeafPcsCertificate] Failed: FRI fold_x at {i}");
            return false;
        }
    }
    if cert.deep_ros.len() != LEAF_FRI_PROVEN_QUERIES
        || cert.deep_ro_traces.len() != LEAF_FRI_PROVEN_QUERIES
    {
        // Allowed empty when multi-chunk leaf (DeepRo deferred).
        if !(cert.deep_ros.is_empty()
            && cert.deep_ro_traces.is_empty()
            && proof.opened_values.quotient_chunks.len() > 1)
        {
            eprintln!("[LeafPcsCertificate] Failed: deep_ro count");
            return false;
        }
    } else {
        for (i, deep) in cert.deep_ros.iter().enumerate() {
            if !verify_deep_ro_proof(deep) {
                eprintln!("[LeafPcsCertificate] Failed: DeepRo at {i}");
                return false;
            }
        }
        for (i, deep) in cert.deep_ro_traces.iter().enumerate() {
            if !verify_deep_ro_leaf_trace_proof(deep) {
                eprintln!("[LeafPcsCertificate] Failed: DeepRoLeafTrace at {i}");
                return false;
            }
        }
    }
    if cert.fri_val_mmcs.len() != LEAF_FRI_PROVEN_QUERIES
        || cert.fri_chal_mmcs.len() != LEAF_FRI_PROVEN_QUERIES
    {
        eprintln!("[LeafPcsCertificate] Failed: fri mmcs count");
        return false;
    }
    for (i, qp) in cert.fri_val_mmcs.iter().enumerate() {
        if !path_self_check_val(qp) {
            eprintln!("[LeafPcsCertificate] Failed: ValMmcs shape at {i}");
            return false;
        }
    }
    for (i, qp) in cert.fri_chal_mmcs.iter().enumerate() {
        if !path_self_check_chal(qp) {
            eprintln!("[LeafPcsCertificate] Failed: ChallengeMmcs shape at {i}");
            return false;
        }
    }

    // LDE rebuild skipped: merkle_fold is the query-0 ValMmcs trace path.
    if cert.merkle_fold != cert.fri_val_mmcs[0].trace_path {
        eprintln!("[LeafPcsCertificate] Failed: merkle_fold mismatch");
        return false;
    }

    if let Err(e) =
        bind_fri_fold_bundle_to_proof_width(proof, &cert.fri_fold_ys, &cert.fri_folds, trace_width)
    {
        eprintln!("[LeafPcsCertificate] Failed: FRI fold bind: {e}");
        return false;
    }
    if !cert.deep_ros.is_empty() {
        if let Err(e) = bind_deep_ro_leaf_bundle_to_proof(
            proof,
            &cert.deep_ros,
            &cert.deep_ro_traces,
            &cert.fri_fold_ys,
            trace_width,
        ) {
            eprintln!("[LeafPcsCertificate] Failed: DeepRo bind: {e}");
            return false;
        }
    }
    let mmcs_bundle = AggFriMmcsBundle {
        val: cert.fri_val_mmcs.clone(),
        chal: cert.fri_chal_mmcs.clone(),
    };
    if let Err(e) = bind_leaf_mmcs_with_groups(proof, &mmcs_bundle, &cert.mmcs_groups, trace_width)
    {
        eprintln!("[LeafPcsCertificate] Failed: FRI Mmcs bind: {e}");
        return false;
    }
    true
}

fn skip_cstr(buf: &[u8], offset: usize) -> Option<usize> {
    let end_rel = buf.get(offset..)?.iter().position(|&b| b == 0)?;
    Some(offset + end_rel + 1)
}

fn read_u32_le(buf: &[u8], offset: usize) -> Option<(u32, usize)> {
    let bytes = buf.get(offset..offset + 4)?;
    let mut raw = [0u8; 4];
    raw.copy_from_slice(bytes);
    Some((u32::from_le_bytes(raw), offset + 4))
}

fn plonky3_after_inner_marker(
    inner: &[u8],
    marker: &[u8],
    skip_cstrs: usize,
) -> Result<Vec<u8>, String> {
    let marker_pos = inner
        .windows(marker.len())
        .position(|w| w == marker)
        .ok_or_else(|| format!("missing inner marker {}", String::from_utf8_lossy(marker)))?;
    let mut cursor = marker_pos + marker.len();
    for _ in 0..skip_cstrs {
        cursor =
            skip_cstr(inner, cursor).ok_or_else(|| "truncated inner binding fields".to_string())?;
    }
    let (len, cursor) =
        read_u32_le(inner, cursor).ok_or_else(|| "truncated plonky3 length".to_string())?;
    let end = cursor + len as usize;
    inner
        .get(cursor..end)
        .map(|s| s.to_vec())
        .ok_or_else(|| "truncated plonky3 payload".to_string())
}

fn unitary_plonky3_from_child(child: &[u8]) -> Result<Vec<u8>, String> {
    let base = base_proof_without_aux_tails(base_proof_without_distribution_tail(child));
    let parsed = parse_leaf_binding(base).ok_or_else(|| "cannot parse leaf binding".to_string())?;
    let ctx = parsed_to_stark_context(&parsed);
    decode_proof_v2_plonky3_bytes(base, &ctx)
        .ok_or_else(|| "cannot decode leaf Plonky3 payload".to_string())
}

fn born_plonky3_from_child(child: &[u8]) -> Result<Vec<u8>, String> {
    let (_, tail_body) =
        parse_born_leaf_prefix(child).ok_or_else(|| "malformed Born leaf prefix".to_string())?;
    let born_inner =
        split_born_stark_tail(tail_body).ok_or_else(|| "missing Born zk tail".to_string())?;
    plonky3_after_inner_marker(born_inner, BORN_STARK_INNER_MARKER, 2)
}

fn marginal_inners_from_bundle(bundle: &[u8]) -> Result<Vec<&[u8]>, String> {
    let (marginal_bundle, _shot) = split_shot_sampling_from_bundle(bundle)
        .ok_or_else(|| "malformed trajectory STARK bundle".to_string())?;
    let (witness_count, mut cursor) = read_u32_le(marginal_bundle, 0)
        .ok_or_else(|| "truncated marginal bundle header".to_string())?;
    let mut inners = Vec::with_capacity(witness_count as usize);
    for _ in 0..witness_count {
        let (inner_len, next) = read_u32_le(marginal_bundle, cursor)
            .ok_or_else(|| "truncated marginal inner length".to_string())?;
        cursor = next;
        let end = cursor + inner_len as usize;
        let inner = marginal_bundle
            .get(cursor..end)
            .ok_or_else(|| "truncated marginal inner proof".to_string())?;
        inners.push(inner);
        cursor = end;
    }
    if cursor != marginal_bundle.len() {
        return Err("trailing marginal bundle bytes".into());
    }
    Ok(inners)
}

fn traj_plonky3_payloads_from_child(child: &[u8]) -> Result<Vec<(LeafKind, Vec<u8>)>, String> {
    let (_, tail_body) = parse_trajectory_leaf_prefix(child)
        .ok_or_else(|| "malformed trajectory leaf prefix".to_string())?;
    let bundle = split_trajectory_stark_tail(tail_body)
        .ok_or_else(|| "missing trajectory zk tail".to_string())?;
    let (marginal_bundle, shot_inner) = split_shot_sampling_from_bundle(bundle)
        .ok_or_else(|| "malformed trajectory STARK bundle".to_string())?;

    let mut out = Vec::new();
    for inner in marginal_inners_from_bundle(marginal_bundle)? {
        let plonky3 = plonky3_after_inner_marker(inner, TRAJ_MARG_STARK_INNER_MARKER, 3)?;
        out.push((LeafKind::TrajMarginal, plonky3));
    }
    let shot_plonky3 = shot_plonky3_from_inner(shot_inner)?;
    out.push((LeafKind::ShotSampling, shot_plonky3));
    Ok(out)
}

fn shot_plonky3_from_inner(inner: &[u8]) -> Result<Vec<u8>, String> {
    let marker_pos = inner
        .windows(TRAJ_SHOT_STARK_INNER_MARKER.len())
        .position(|w| w == TRAJ_SHOT_STARK_INNER_MARKER)
        .ok_or_else(|| "missing shot sampling inner marker".to_string())?;
    let mut cursor = marker_pos + TRAJ_SHOT_STARK_INNER_MARKER.len();
    cursor =
        skip_cstr(inner, cursor).ok_or_else(|| "truncated shot trajectory digest".to_string())?;
    if inner.len() < cursor + 20 {
        return Err("truncated shot binding tail".into());
    }
    cursor += 8 + 8 + 4; // sample_seed, shots, event_count
    let (len, cursor) =
        read_u32_le(inner, cursor).ok_or_else(|| "truncated shot plonky3 length".to_string())?;
    let end = cursor + len as usize;
    inner
        .get(cursor..end)
        .map(|s| s.to_vec())
        .ok_or_else(|| "truncated shot plonky3 payload".to_string())
}

fn proof_from_plonky3(plonky3: &[u8]) -> Result<Proof<WqcStarkConfig>, String> {
    postcard::from_bytes(plonky3).map_err(|e| format!("postcard decode leaf proof: {e}"))
}

fn cert_from_plonky3(plonky3: &[u8], kind: LeafKind) -> Result<LeafPcsCertificate, String> {
    let proof = proof_from_plonky3(plonky3)?;
    let stmt = leaf_stmt_digest(kind, &proof)?;
    build_leaf_pcs_certificate(&proof, kind, stmt)
}

/// SHA3-256 of the concatenation of each certificate `stmt_digest` (multi-cert traj bundles).
pub fn leaf_bundle_stmt_digest(bundle: &LeafPcsBundle) -> [u8; 32] {
    let mut h = Sha3_256::new();
    for cert in &bundle.certs {
        h.update(cert.stmt_digest);
    }
    let dig = h.finalize();
    let mut out = [0u8; 32];
    out.copy_from_slice(&dig);
    out
}

pub fn verify_leaf_pcs_bundle(child: &[u8], bundle: &LeafPcsBundle) -> Result<(), String> {
    if is_trajectory_leaf_proof(child) {
        let payloads = traj_plonky3_payloads_from_child(child)?;
        if payloads.len() != bundle.certs.len() {
            return Err(format!(
                "traj bundle cert count {} != payload count {}",
                bundle.certs.len(),
                payloads.len()
            ));
        }
        for ((kind, plonky3), cert) in payloads.into_iter().zip(&bundle.certs) {
            if cert.kind != kind {
                return Err(format!(
                    "traj cert kind mismatch: {:?} vs {:?}",
                    cert.kind, kind
                ));
            }
            let proof = proof_from_plonky3(&plonky3)?;
            if !verify_leaf_pcs_certificate(&proof, cert) {
                return Err("leaf PCS certificate self-check failed".into());
            }
        }
        return Ok(());
    }

    let plonky3 = if is_born_leaf_proof(child) {
        born_plonky3_from_child(child)?
    } else {
        unitary_plonky3_from_child(child)?
    };
    if bundle.certs.len() != 1 {
        return Err(format!(
            "expected one leaf cert, got {}",
            bundle.certs.len()
        ));
    }
    let proof = proof_from_plonky3(&plonky3)?;
    if !verify_leaf_pcs_certificate(&proof, &bundle.certs[0]) {
        return Err("leaf PCS certificate self-check failed".into());
    }
    Ok(())
}

/// Builds a leaf PCS bundle from a unitary / born / traj child wrapper.
pub fn build_leaf_pcs_bundle_from_child(child_bytes: &[u8]) -> Result<LeafPcsBundle, String> {
    if is_trajectory_leaf_proof(child_bytes) {
        let payloads = traj_plonky3_payloads_from_child(child_bytes)?;
        let mut certs = Vec::with_capacity(payloads.len());
        for (kind, plonky3) in payloads {
            certs.push(cert_from_plonky3(&plonky3, kind)?);
        }
        let bundle = LeafPcsBundle { certs };
        verify_leaf_pcs_bundle(child_bytes, &bundle)?;
        return Ok(bundle);
    }

    let (kind, plonky3) = if is_born_leaf_proof(child_bytes) {
        (LeafKind::Born, born_plonky3_from_child(child_bytes)?)
    } else {
        (LeafKind::Unitary, unitary_plonky3_from_child(child_bytes)?)
    };
    let cert = cert_from_plonky3(&plonky3, kind)?;
    let bundle = LeafPcsBundle { certs: vec![cert] };
    verify_leaf_pcs_bundle(child_bytes, &bundle)?;
    Ok(bundle)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::plonky3_stark::generate_plonky3_proof;
    use crate::transcript::StarkContext;

    #[test]
    #[ignore = "slow; local only — not run in CI"]
    fn unitary_leaf_pcs_certificate_roundtrip() {
        let ctx = StarkContext {
            circuit_id: "c-leaf",
            sub_task_id: "sub-leaf-pcs",
            node_id: "n1",
            slice_id: "0",
            output_hash: "out",
            terminal_statevector_digest: "",
            measurement_spec_hash: "",
        };
        let trace = crate::trace_spec::idle_qubit0_trace();
        let transcript = generate_plonky3_proof(&ctx, &trace).expect("prove");
        let plonky3 = decode_proof_v2_plonky3_bytes(&transcript, &ctx).expect("decode");
        let proof: Proof<WqcStarkConfig> = postcard::from_bytes(&plonky3).expect("postcard");
        let kind = LeafKind::Unitary;
        let stmt = leaf_stmt_digest(kind, &proof).expect("stmt");
        let cert = build_leaf_pcs_certificate(&proof, kind, stmt).expect("cert");
        assert_eq!(cert.trace_width as usize, UNITARY_TRACE_WIDTH);
        assert!(verify_leaf_pcs_certificate(&proof, &cert));

        let bundle = build_leaf_pcs_bundle_from_child(&transcript).expect("bundle");
        assert_eq!(bundle.certs.len(), 1);
        assert!(verify_leaf_pcs_certificate(&proof, &bundle.certs[0]));
    }

    #[test]
    #[ignore = "slow; local only — not run in CI"]
    fn born_leaf_plonky3_extract_and_ood() {
        use crate::distribution::DistributionSegment;
        use crate::plonky3_stark::generate_born_stark_proof;
        use crate::plonky3_stark::BornStarkContext;

        let inv_sqrt2 = 1.0f64 / 2.0f64.sqrt();
        let sv = vec![(inv_sqrt2, 0.0), (0.0, 0.0), (0.0, 0.0), (inv_sqrt2, 0.0)];
        let probs = vec![("00".into(), 0.5), ("11".into(), 0.5)];
        let binding = crate::distribution::BornBinding::from_specs(2, 2, &[(0, 0), (1, 1)], sv)
            .expect("bind");
        let segment = DistributionSegment {
            sample_seed: 42,
            shots: 128,
            measurement_spec_hash: "spec".into(),
            probability_digest: crate::distribution::calculate_probability_digest(&probs),
            probabilities: probs,
            born_binding: Some(binding),
        };
        let link = segment
            .born_binding
            .as_ref()
            .unwrap()
            .terminal_statevector_digest
            .clone();
        let born_ctx = BornStarkContext {
            sub_task_id: "sub-born-pcs",
            probability_digest: &segment.probability_digest,
            terminal_statevector_digest: &link,
        };
        let born_inner = generate_born_stark_proof(&born_ctx, &segment).expect("born prove");
        let leaf =
            crate::aggregation::encode_born_leaf("sub-born-pcs", &segment, Some(&born_inner));
        let plonky3 = born_plonky3_from_child(&leaf).expect("born plonky3");
        let proof = proof_from_plonky3(&plonky3).expect("proof");
        let stmt = leaf_stmt_digest(LeafKind::Born, &proof).expect("stmt");
        let cert = build_leaf_pcs_certificate(&proof, LeafKind::Born, stmt).expect("cert");
        assert!(verify_leaf_pcs_certificate(&proof, &cert));
    }
}

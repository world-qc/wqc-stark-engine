//! AggregationAir PCS opening certificates (R3-M2 / M2.5 / M2.5b / M3b4 / M3c3 / M3d).
//!
//! Mirrors leaf PCS flow (M3e): host OOD + in-circuit FriFold / DeepRo / FRI Val+Challenge
//! Mmcs. Skips natural-row LDE rebuild (no prover_data); `merkle_fold` reuses query-0 ValMmcs
//! trace path like [`super::leaf_pcs_cert::LeafPcsCertificate`].

use p3_commit::Mmcs;
use p3_field::PrimeCharacteristicRing;
use p3_mersenne_31::Mersenne31;
use p3_uni_stark::Proof;

use crate::aggregation::CHILD_HASH_LEN;
use crate::plonky3_stark::aggregation::AggregationContext;
use crate::plonky3_stark::aggregation_air::AGG_WIDTH;
use crate::plonky3_stark::config::{ValMmcs, WqcStarkConfig};
use crate::plonky3_stark::transcript_v4::decode_agg_proof_owned;

use super::agg_constraints::aggregation_air_constraints_hold;
use super::deep_ro_air::{verify_deep_ro_proof, DeepRoStepProof};
use super::deep_ro_bind::{
    bind_deep_ro_bundle_to_proof, deep_ro_bundle_from_agg_proof, AGG_DEEP_RO_MAX,
    AGG_DEEP_RO_TRACE_MAX,
};
use super::deep_ro_trace_air::{verify_deep_ro_trace_proof, DeepRoTraceStepProof};
use super::fri_fold_air::{verify_fri_fold_proof, verify_fri_fold_y_proof, FriFoldStepProof};
use super::fri_fold_bind::{
    bind_fri_fold_bundle_to_proof, covers_all_devnet_fri_queries, fri_fold_bundle_from_agg_proof,
    AGG_FRI_MAX_FOLD_YS, AGG_FRI_MAX_ROUNDS, AGG_FRI_PROVEN_QUERIES,
};
use super::fri_mmcs_bind::{
    bind_fri_mmcs_bundle_to_proof, fri_mmcs_bundle_from_agg_proof, AggFriMmcsBundle,
    FriChalMmcsQueryProof, FriValMmcsQueryProof,
};
use super::fri_mmcs_m4c::{
    apply_leaf_mmcs_m4c_folds, bind_leaf_mmcs_with_groups, LeafMmcsFoldGroups,
};
use super::fri_mmcs_path::FriMmcsPathProof;
use super::ood_air::{verify_ood_proof, OodStepProof};
use super::ood_bind::verify_agg_ood_step;
use super::ood_native::generate_agg_ood_proof;

/// Max Merkle siblings retained for legacy V6 decode (LDE rebuild removed).
pub const AGG_PCS_MAX_SIBLINGS: usize = 8;
/// Max siblings for leaf PCS LDE / FRI Mmcs paths.
pub const LEAF_PCS_MAX_SIBLINGS: usize = 20;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AggPcsCertificate {
    /// AggregationAir public statement (child container digests).
    pub stmt_left_hash: [u8; CHILD_HASH_LEN],
    pub stmt_right_hash: [u8; CHILD_HASH_LEN],
    /// Circle PCS trace commitment root (`MerkleCap` height 0).
    pub trace_commitment: [u8; 32],
    /// Natural-order AggregationAir row (width 66) used for in-circuit constraints.
    pub natural_row: [Mersenne31; AGG_WIDTH],
    /// LDE statement open deferred (always 0 / empty).
    pub lde_index: u32,
    pub lde_row: Vec<Mersenne31>,
    pub siblings: Vec<[u8; 32]>,
    /// Query-0 ValMmcs trace path (variable-depth stand-in; LDE rebuild skipped).
    pub merkle_fold: FriMmcsPathProof,
    /// M4c group folds / stripped batch digests (`LEAF_MMCS_FOLD_V`).
    pub mmcs_groups: LeafMmcsFoldGroups,
    /// R3-M3b3: first-layer Circle FRI `fold_y` steps (all proven queries).
    pub fri_fold_ys: Vec<FriFoldStepProof>,
    /// R3-M3b3: commit-phase Circle FRI `fold_x` steps (all proven queries × rounds) with FS β + RO.
    pub fri_folds: Vec<FriFoldStepProof>,
    /// R3-M3c3: DeepRo (DEEP+λ) for all proven queries' quotient batches; bound into FriFoldY.
    pub deep_ros: Vec<DeepRoStepProof>,
    /// R3-M3c3: DeepRoTrace (DEEP+λ) for all proven queries' trace batches; bound into FriFoldY.
    pub deep_ro_traces: Vec<DeepRoTraceStepProof>,
    /// R3 OOD: in-circuit constraint fold + quotient check at ζ.
    pub ood: OodStepProof,
    /// R3-M3d: ValMmcs (trace+quot) Merkle paths for all proven FRI queries.
    pub fri_val_mmcs: Vec<FriValMmcsQueryProof>,
    /// R3-M3d: ChallengeMmcs (first-layer + commit-phase) paths for all proven FRI queries.
    pub fri_chal_mmcs: Vec<FriChalMmcsQueryProof>,
}

fn commitment_root(com: &<ValMmcs as Mmcs<Mersenne31>>::Commitment) -> Result<[u8; 32], String> {
    let roots = com.roots();
    let root = roots
        .first()
        .ok_or_else(|| "empty MerkleCap commitment".to_string())?;
    Ok(*root)
}

fn natural_row_from_hashes(
    left: [u8; CHILD_HASH_LEN],
    right: [u8; CHILD_HASH_LEN],
) -> [Mersenne31; AGG_WIDTH] {
    let mut row = [Mersenne31::ZERO; AGG_WIDTH];
    for (i, b) in left.into_iter().enumerate() {
        row[i] = Mersenne31::from_u32(b as u32);
    }
    for (i, b) in right.into_iter().enumerate() {
        row[32 + i] = Mersenne31::from_u32(b as u32);
    }
    row[64] = Mersenne31::ONE;
    row[65] = Mersenne31::ONE;
    row
}

fn path_self_check_val(qp: &FriValMmcsQueryProof) -> bool {
    qp.trace_path.depth as usize == qp.trace_siblings.len()
        && qp.quot_path.depth as usize == qp.quot_siblings.len()
        && !qp.trace_siblings.is_empty()
        && !qp.quot_siblings.is_empty()
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

/// Builds a PCS opening certificate for an AggregationAir transcript.
///
/// M3d: host OOD + in-circuit FRI Val/Challenge Mmcs (no host PCS commit / LDE rebuild).
pub fn build_agg_pcs_certificate(
    context: &AggregationContext<'_>,
    agg_transcript: &[u8],
) -> Result<AggPcsCertificate, String> {
    let plonky3_bytes = decode_agg_proof_owned(agg_transcript, context)
        .ok_or_else(|| "malformed AggregationAir transcript".to_string())?;
    let proof: Proof<WqcStarkConfig> = postcard::from_bytes(&plonky3_bytes)
        .map_err(|e| format!("postcard decode AggregationAir proof: {e}"))?;

    let ood = generate_agg_ood_proof(&proof).map_err(|e| format!("R3 OOD prove failed: {e}"))?;
    if !verify_ood_proof(&ood) {
        return Err("R3 OOD self-check failed".into());
    }

    let natural_row = natural_row_from_hashes(context.left_child_hash, context.right_child_hash);
    if !aggregation_air_constraints_hold(&natural_row, &natural_row) {
        return Err("natural AggregationAir row fails constraints".to_string());
    }

    let fri_bundle = fri_fold_bundle_from_agg_proof(&proof)
        .map_err(|e| format!("R3-M3b4 FRI fold prove failed: {e}"))?;
    if fri_bundle.fold_ys.is_empty() || fri_bundle.fold_ys.len() > AGG_FRI_MAX_FOLD_YS {
        return Err(format!(
            "unexpected FRI fold_y count: {}",
            fri_bundle.fold_ys.len()
        ));
    }
    if fri_bundle.fold_xs.is_empty()
        || fri_bundle.fold_xs.len() > AGG_FRI_MAX_ROUNDS * AGG_FRI_PROVEN_QUERIES
    {
        return Err(format!(
            "unexpected FRI fold_x count: {}",
            fri_bundle.fold_xs.len()
        ));
    }
    for (i, fold) in fri_bundle.fold_ys.iter().enumerate() {
        if !verify_fri_fold_y_proof(fold) {
            return Err(format!("R3-M3b4 FRI fold_y self-check failed at step {i}"));
        }
    }
    for (i, fold) in fri_bundle.fold_xs.iter().enumerate() {
        if !verify_fri_fold_proof(fold) {
            return Err(format!("R3-M3b4 FRI fold_x self-check failed at step {i}"));
        }
    }

    let deep_bundle = deep_ro_bundle_from_agg_proof(&proof)
        .map_err(|e| format!("R3-M3c3 DeepRo bundle prove failed: {e}"))?;
    for (i, deep) in deep_bundle.deep_ros.iter().enumerate() {
        if !verify_deep_ro_proof(deep) {
            return Err(format!("R3-M3c3 DeepRo self-check failed at {i}"));
        }
    }
    for (i, deep) in deep_bundle.deep_ro_traces.iter().enumerate() {
        if !verify_deep_ro_trace_proof(deep) {
            return Err(format!("R3-M3c3 DeepRoTrace self-check failed at {i}"));
        }
    }
    bind_deep_ro_bundle_to_proof(
        &proof,
        &deep_bundle.deep_ros,
        &deep_bundle.deep_ro_traces,
        &fri_bundle.fold_ys,
    )
    .map_err(|e| format!("R3-M3c3 DeepRo bundle bind failed: {e}"))?;

    let mmcs_bundle = fri_mmcs_bundle_from_agg_proof(&proof)
        .map_err(|e| format!("R3-M3d FRI Mmcs prove failed: {e}"))?;
    if mmcs_bundle.val.len() != AGG_FRI_PROVEN_QUERIES
        || mmcs_bundle.chal.len() != AGG_FRI_PROVEN_QUERIES
    {
        return Err(format!(
            "unexpected FRI Mmcs counts: val={}, chal={}",
            mmcs_bundle.val.len(),
            mmcs_bundle.chal.len()
        ));
    }
    for (i, qp) in mmcs_bundle.val.iter().enumerate() {
        if !path_self_check_val(qp) {
            return Err(format!("R3-M3d ValMmcs self-check failed at query {i}"));
        }
    }
    for (i, qp) in mmcs_bundle.chal.iter().enumerate() {
        if !path_self_check_chal(qp) {
            return Err(format!(
                "R3-M3d ChallengeMmcs self-check failed at query {i}"
            ));
        }
    }
    bind_fri_mmcs_bundle_to_proof(&proof, &mmcs_bundle)
        .map_err(|e| format!("R3-M3d FRI Mmcs bind failed: {e}"))?;

    let mut mmcs_bundle = mmcs_bundle;
    let mmcs_groups = apply_leaf_mmcs_m4c_folds(&proof, AGG_WIDTH, &mut mmcs_bundle)
        .map_err(|e| format!("R3-M4c Agg Mmcs group fold failed: {e}"))?;
    // Inject / multi-RO first_layer: strip nested STARKs; host digest replay is sound for PCS.
    strip_inject_first_layers(&mut mmcs_bundle);
    bind_leaf_mmcs_with_groups(&proof, &mmcs_bundle, &mmcs_groups, AGG_WIDTH)
        .map_err(|e| format!("R3-M4c Agg Mmcs group bind failed: {e}"))?;

    let trace_commitment = commitment_root(&proof.commitments.trace)?;
    let merkle_fold = mmcs_bundle.val[0].trace_path.clone();

    Ok(AggPcsCertificate {
        stmt_left_hash: context.left_child_hash,
        stmt_right_hash: context.right_child_hash,
        trace_commitment,
        natural_row,
        lde_index: 0,
        lde_row: Vec::new(),
        siblings: Vec::new(),
        merkle_fold,
        mmcs_groups,
        fri_fold_ys: fri_bundle.fold_ys,
        fri_folds: fri_bundle.fold_xs,
        deep_ros: deep_bundle.deep_ros,
        deep_ro_traces: deep_bundle.deep_ro_traces,
        ood,
        fri_val_mmcs: mmcs_bundle.val,
        fri_chal_mmcs: mmcs_bundle.chal,
    })
}

fn strip_inject_first_layers(bundle: &mut AggFriMmcsBundle) {
    use super::fri_mmcs_m4c::{batch_starks_stripped, strip_chal_batch_starks};
    for qp in &mut bundle.chal {
        if !qp.first_layer.inject_compresses.is_empty() && !batch_starks_stripped(&qp.first_layer) {
            strip_chal_batch_starks(&mut qp.first_layer);
        }
    }
}

/// Host-verifies a certificate against an AggregationAir transcript + context.
///
/// Checks in-circuit OOD + FriFold / DeepRo / FRI Mmcs STARKs and FS+RO binds
/// without Plonky3 PCS commit / LDE rebuild or host `verify_agg_fri_openings`.
pub fn verify_agg_pcs_certificate(
    context: &AggregationContext<'_>,
    agg_transcript: &[u8],
    cert: &AggPcsCertificate,
) -> bool {
    if cert.stmt_left_hash != context.left_child_hash
        || cert.stmt_right_hash != context.right_child_hash
    {
        eprintln!("[AggPcsCertificate] Failed: statement hash mismatch");
        return false;
    }
    let expected = natural_row_from_hashes(context.left_child_hash, context.right_child_hash);
    if cert.natural_row != expected {
        eprintln!("[AggPcsCertificate] Failed: natural row mismatch");
        return false;
    }
    if !aggregation_air_constraints_hold(&cert.natural_row, &cert.natural_row) {
        eprintln!("[AggPcsCertificate] Failed: AggregationAir constraints");
        return false;
    }
    if !verify_ood_proof(&cert.ood) {
        eprintln!("[AggPcsCertificate] Failed: OOD STARK");
        return false;
    }
    for (i, fold) in cert.fri_fold_ys.iter().enumerate() {
        if !verify_fri_fold_y_proof(fold) {
            eprintln!("[AggPcsCertificate] Failed: FRI fold_y STARK at {i}");
            return false;
        }
    }
    for (i, fold) in cert.fri_folds.iter().enumerate() {
        if !verify_fri_fold_proof(fold) {
            eprintln!("[AggPcsCertificate] Failed: FRI fold STARK at {i}");
            return false;
        }
    }
    if cert.deep_ros.len() != AGG_DEEP_RO_MAX {
        eprintln!(
            "[AggPcsCertificate] Failed: deep_ros len {}, want {AGG_DEEP_RO_MAX}",
            cert.deep_ros.len()
        );
        return false;
    }
    for (i, deep) in cert.deep_ros.iter().enumerate() {
        if !verify_deep_ro_proof(deep) {
            eprintln!("[AggPcsCertificate] Failed: DeepRo STARK at {i}");
            return false;
        }
    }
    if cert.deep_ro_traces.len() != AGG_DEEP_RO_TRACE_MAX {
        eprintln!(
            "[AggPcsCertificate] Failed: deep_ro_traces len {}, want {AGG_DEEP_RO_TRACE_MAX}",
            cert.deep_ro_traces.len()
        );
        return false;
    }
    for (i, deep) in cert.deep_ro_traces.iter().enumerate() {
        if !verify_deep_ro_trace_proof(deep) {
            eprintln!("[AggPcsCertificate] Failed: DeepRoTrace STARK at {i}");
            return false;
        }
    }
    if cert.fri_val_mmcs.len() != AGG_FRI_PROVEN_QUERIES {
        eprintln!(
            "[AggPcsCertificate] Failed: fri_val_mmcs len {}, want {AGG_FRI_PROVEN_QUERIES}",
            cert.fri_val_mmcs.len()
        );
        return false;
    }
    if cert.fri_chal_mmcs.len() != AGG_FRI_PROVEN_QUERIES {
        eprintln!(
            "[AggPcsCertificate] Failed: fri_chal_mmcs len {}, want {AGG_FRI_PROVEN_QUERIES}",
            cert.fri_chal_mmcs.len()
        );
        return false;
    }
    for (i, qp) in cert.fri_val_mmcs.iter().enumerate() {
        if !path_self_check_val(qp) {
            eprintln!("[AggPcsCertificate] Failed: ValMmcs shape at {i}");
            return false;
        }
    }
    for (i, qp) in cert.fri_chal_mmcs.iter().enumerate() {
        if !path_self_check_chal(qp) {
            eprintln!("[AggPcsCertificate] Failed: ChallengeMmcs shape at {i}");
            return false;
        }
    }

    if covers_all_devnet_fri_queries() {
        verify_agg_pcs_certificate_fri_bound(context, agg_transcript, cert)
    } else {
        match build_agg_pcs_certificate(context, agg_transcript) {
            Ok(rebuilt) => {
                if rebuilt.trace_commitment != cert.trace_commitment
                    || rebuilt.lde_index != cert.lde_index
                    || rebuilt.lde_row != cert.lde_row
                    || rebuilt.siblings != cert.siblings
                    || rebuilt.merkle_fold != cert.merkle_fold
                    || rebuilt.mmcs_groups != cert.mmcs_groups
                    || rebuilt.fri_fold_ys != cert.fri_fold_ys
                    || rebuilt.fri_folds != cert.fri_folds
                    || rebuilt.deep_ros != cert.deep_ros
                    || rebuilt.deep_ro_traces != cert.deep_ro_traces
                    || rebuilt.ood != cert.ood
                    || rebuilt.fri_val_mmcs != cert.fri_val_mmcs
                    || rebuilt.fri_chal_mmcs != cert.fri_chal_mmcs
                {
                    eprintln!("[AggPcsCertificate] Failed: rebuilt certificate mismatch");
                    return false;
                }
                true
            }
            Err(e) => {
                eprintln!("[AggPcsCertificate] Failed: {e}");
                false
            }
        }
    }
}

/// Binds cert to AggregationAir proof via OOD + FS/RO fold/Mmcs publics (no PCS rebuild).
fn verify_agg_pcs_certificate_fri_bound(
    context: &AggregationContext<'_>,
    agg_transcript: &[u8],
    cert: &AggPcsCertificate,
) -> bool {
    let plonky3_bytes = match decode_agg_proof_owned(agg_transcript, context) {
        Some(b) => b,
        None => {
            eprintln!("[AggPcsCertificate] Failed: malformed AggregationAir transcript");
            return false;
        }
    };
    let proof: Proof<WqcStarkConfig> = match postcard::from_bytes(&plonky3_bytes) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("[AggPcsCertificate] Failed: postcard decode: {e}");
            return false;
        }
    };

    if let Err(e) = verify_agg_ood_step(&proof, &cert.ood) {
        eprintln!("[AggPcsCertificate] Failed: OOD: {e}");
        return false;
    }

    let trace_commitment = match commitment_root(&proof.commitments.trace) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("[AggPcsCertificate] Failed: {e}");
            return false;
        }
    };
    if trace_commitment != cert.trace_commitment {
        eprintln!("[AggPcsCertificate] Failed: cert commitment mismatch");
        return false;
    }

    if cert.merkle_fold != cert.fri_val_mmcs[0].trace_path {
        eprintln!("[AggPcsCertificate] Failed: merkle_fold mismatch");
        return false;
    }

    if let Err(e) = bind_fri_fold_bundle_to_proof(&proof, &cert.fri_fold_ys, &cert.fri_folds) {
        eprintln!("[AggPcsCertificate] Failed: FRI fold bind: {e}");
        return false;
    }
    if let Err(e) = bind_deep_ro_bundle_to_proof(
        &proof,
        &cert.deep_ros,
        &cert.deep_ro_traces,
        &cert.fri_fold_ys,
    ) {
        eprintln!("[AggPcsCertificate] Failed: DeepRo bundle bind: {e}");
        return false;
    }
    let mmcs_bundle = AggFriMmcsBundle {
        val: cert.fri_val_mmcs.clone(),
        chal: cert.fri_chal_mmcs.clone(),
    };
    if let Err(e) = bind_leaf_mmcs_with_groups(&proof, &mmcs_bundle, &cert.mmcs_groups, AGG_WIDTH) {
        eprintln!("[AggPcsCertificate] Failed: FRI Mmcs bind: {e}");
        return false;
    }
    true
}

/// Tries to extract a V4 AggregationAir transcript from a child compose blob.
pub fn child_aggregation_transcript(child: &[u8]) -> Option<&[u8]> {
    use crate::plonky3_stark::recursion::prove::split_rec_tail;
    use crate::plonky3_stark::transcript_v4::split_agg_tail;

    let body = split_rec_tail(child).map(|(b, _)| b).unwrap_or(child);
    split_agg_tail(body).map(|(_, agg)| agg)
}

pub fn parse_agg_v4_header(proof: &[u8], expected_parent: &str) -> Option<ParsedAggV4Header> {
    let header = parse_agg_v4_header_any(proof)?;
    if header.parent_task_id != expected_parent {
        return None;
    }
    Some(header)
}

/// Parses a V4 AggregationAir header without fixing the parent id up-front.
pub fn parse_agg_v4_header_any(proof: &[u8]) -> Option<ParsedAggV4Header> {
    use crate::plonky3_stark::transcript_v4::V4_AGG_INNER_MARKER;

    let pos = proof
        .windows(V4_AGG_INNER_MARKER.len())
        .position(|w| w == V4_AGG_INNER_MARKER)?;
    let prefix = &proof[..pos];
    if prefix.is_empty() || prefix.last() != Some(&0) {
        return None;
    }
    let parent_task_id = std::str::from_utf8(&prefix[..prefix.len() - 1])
        .ok()?
        .to_string();
    let mut cursor = pos + V4_AGG_INNER_MARKER.len();
    let end = proof.get(cursor..)?.iter().position(|&b| b == 0)? + cursor;
    let compose_label = std::str::from_utf8(&proof[cursor..end]).ok()?.to_string();
    cursor = end + 1;
    let end = proof.get(cursor..)?.iter().position(|&b| b == 0)? + cursor;
    let manifest = std::str::from_utf8(&proof[cursor..end]).ok()?.to_string();
    cursor = end + 1;
    let left: [u8; CHILD_HASH_LEN] = proof.get(cursor..cursor + 32)?.try_into().ok()?;
    cursor += 32;
    let right: [u8; CHILD_HASH_LEN] = proof.get(cursor..cursor + 32)?.try_into().ok()?;
    Some(ParsedAggV4Header {
        parent_task_id,
        compose_label,
        manifest_root_hash: manifest,
        left_child_hash: left,
        right_child_hash: right,
    })
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParsedAggV4Header {
    pub parent_task_id: String,
    pub compose_label: String,
    pub manifest_root_hash: String,
    pub left_child_hash: [u8; CHILD_HASH_LEN],
    pub right_child_hash: [u8; CHILD_HASH_LEN],
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::plonky3_stark::generate_aggregation_proof;

    #[test]
    #[ignore = "slow; local only — not run in CI"]
    fn agg_pcs_certificate_roundtrip() {
        let ctx = AggregationContext {
            parent_task_id: "parent",
            compose_label: "L1:0",
            manifest_root_hash: "",
            left_child_hash: [3u8; CHILD_HASH_LEN],
            right_child_hash: [5u8; CHILD_HASH_LEN],
        };
        let proof = generate_aggregation_proof(&ctx).expect("prove");
        let cert = build_agg_pcs_certificate(&ctx, &proof).expect("cert");
        assert!(verify_agg_pcs_certificate(&ctx, &proof, &cert));
        assert_eq!(cert.natural_row[64], Mersenne31::ONE);
        assert!(cert.lde_row.is_empty());
        assert_eq!(cert.merkle_fold, cert.fri_val_mmcs[0].trace_path);
    }
}

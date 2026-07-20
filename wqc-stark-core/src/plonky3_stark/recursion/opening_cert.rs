//! AggregationAir PCS opening certificates (R3-M2 / M2.5 / M2.5b / M3b4 / M3c3).
//!
//! Rebuild Circle PCS commitment, open an LDE row, host-check LDE `Mmcs::verify_batch`,
//! attach Merkle/FriFold STARKs for all FRI queries, plus all-query quotient
//! [`DeepRoStepProof`] and trace [`DeepRoTraceStepProof`] (DEEP+λ bound into FriFoldY).
//! Build/verify use host OOD + FRI Mmcs (no Plonky3 FRI).

use p3_commit::{BatchOpeningRef, Mmcs, Pcs};
use p3_field::PrimeCharacteristicRing;
use p3_matrix::{Dimensions, Matrix};
use p3_mersenne_31::Mersenne31;
use p3_uni_stark::{Proof, StarkGenericConfig};

use crate::aggregation::CHILD_HASH_LEN;
use crate::air::pad_air_matrix_for_uni_stark;
use crate::plonky3_stark::aggregation::{build_agg_matrix, AggregationContext};
use crate::plonky3_stark::aggregation_air::AGG_WIDTH;
use crate::plonky3_stark::config::{devnet_circle_config, ValMmcs, WqcStarkConfig};
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
use super::fri_mmcs::verify_agg_fri_openings;
use super::fri_ood::verify_agg_ood;
use super::keccak_merkle_air::{
    generate_keccak_merkle_path_proof, verify_keccak_merkle_path_proof, KeccakMerklePathProof,
};
use super::merkle_keccak::verify_agg_merkle_path;

/// Max Merkle siblings for AggregationAir LDE (height 8 with log_blowup=1).
pub const AGG_PCS_MAX_SIBLINGS: usize = 8;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AggPcsCertificate {
    /// AggregationAir public statement (child container digests).
    pub stmt_left_hash: [u8; CHILD_HASH_LEN],
    pub stmt_right_hash: [u8; CHILD_HASH_LEN],
    /// Circle PCS trace commitment root (`MerkleCap` height 0).
    pub trace_commitment: [u8; 32],
    /// Natural-order AggregationAir row (width 66) used for in-circuit constraints.
    pub natural_row: [Mersenne31; AGG_WIDTH],
    /// LDE row index opened against the PCS commitment.
    pub lde_index: u32,
    /// Opened LDE row values (length = AGG_WIDTH).
    pub lde_row: Vec<Mersenne31>,
    /// Merkle siblings authenticating `lde_row` to `trace_commitment`.
    pub siblings: Vec<[u8; 32]>,
    /// R3-M2.5b: Merkle fold + in-circuit Keccak-256 leaf/compress sponges.
    pub merkle_fold: KeccakMerklePathProof,
    /// R3-M3b3: first-layer Circle FRI `fold_y` steps (all proven queries).
    pub fri_fold_ys: Vec<FriFoldStepProof>,
    /// R3-M3b3: commit-phase Circle FRI `fold_x` steps (all proven queries × rounds) with FS β + RO.
    pub fri_folds: Vec<FriFoldStepProof>,
    /// R3-M3c3: DeepRo (DEEP+λ) for all proven queries' quotient batches; bound into FriFoldY.
    pub deep_ros: Vec<DeepRoStepProof>,
    /// R3-M3c3: DeepRoTrace (DEEP+λ) for all proven queries' trace batches; bound into FriFoldY.
    pub deep_ro_traces: Vec<DeepRoTraceStepProof>,
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

/// Builds a PCS opening certificate for an AggregationAir transcript.
///
/// M3b4: uses host OOD + FRI Mmcs instead of Plonky3 `verify_aggregation_proof`.
pub fn build_agg_pcs_certificate(
    context: &AggregationContext<'_>,
    agg_transcript: &[u8],
) -> Result<AggPcsCertificate, String> {
    let plonky3_bytes = decode_agg_proof_owned(agg_transcript, context)
        .ok_or_else(|| "malformed AggregationAir transcript".to_string())?;
    let proof: Proof<WqcStarkConfig> = postcard::from_bytes(&plonky3_bytes)
        .map_err(|e| format!("postcard decode AggregationAir proof: {e}"))?;

    verify_agg_ood(&proof).map_err(|e| format!("R3-M3b4 OOD failed: {e}"))?;
    verify_agg_fri_openings(&proof).map_err(|e| format!("R3-M3b4 FRI Mmcs failed: {e}"))?;

    let matrix = pad_air_matrix_for_uni_stark(build_agg_matrix(
        context.left_child_hash,
        context.right_child_hash,
    ));
    let natural_row = natural_row_from_hashes(context.left_child_hash, context.right_child_hash);
    if !aggregation_air_constraints_hold(&natural_row, &natural_row) {
        return Err("natural AggregationAir row fails constraints".to_string());
    }

    let config = devnet_circle_config();
    let pcs = config.pcs();
    let domain = <crate::plonky3_stark::config::Pcs as Pcs<
        crate::plonky3_stark::config::Challenge,
        crate::plonky3_stark::config::Challenger,
    >>::natural_domain_for_degree(pcs, matrix.height());
    let (comm, prover_data) = <crate::plonky3_stark::config::Pcs as Pcs<
        crate::plonky3_stark::config::Challenge,
        crate::plonky3_stark::config::Challenger,
    >>::commit(pcs, vec![(domain, matrix)]);
    if comm != proof.commitments.trace {
        return Err("rebuilt PCS commitment does not match AggregationAir proof".to_string());
    }

    let trace_commitment = commitment_root(&comm)?;
    // Open the first LDE leaf; height is small (AggregationAir-sized).
    let lde_index = 0usize;
    let batch = pcs.mmcs.open_batch(lde_index, &prover_data);
    let dims: Vec<Dimensions> = pcs
        .mmcs
        .get_matrices(&prover_data)
        .iter()
        .map(|m| Dimensions {
            width: m.width(),
            height: m.height(),
        })
        .collect();
    pcs.mmcs
        .verify_batch(
            &comm,
            &dims,
            lde_index,
            BatchOpeningRef::new(&batch.opened_values, &batch.opening_proof),
        )
        .map_err(|e| format!("AggregationAir PCS Merkle verify failed: {e:?}"))?;

    let lde_row = batch
        .opened_values
        .first()
        .cloned()
        .ok_or_else(|| "empty PCS batch opening".to_string())?;
    if lde_row.len() != AGG_WIDTH {
        return Err(format!(
            "unexpected LDE row width: got {}, want {AGG_WIDTH}",
            lde_row.len()
        ));
    }
    if batch.opening_proof.len() > AGG_PCS_MAX_SIBLINGS {
        return Err(format!(
            "too many Merkle siblings: {}",
            batch.opening_proof.len()
        ));
    }

    if !verify_agg_merkle_path(&lde_row, &batch.opening_proof, lde_index, &trace_commitment) {
        return Err("ValMmcs Keccak Merkle path self-check failed".into());
    }
    let merkle_fold = generate_keccak_merkle_path_proof(
        &lde_row,
        &batch.opening_proof,
        lde_index,
        &trace_commitment,
    )
    .map_err(|e| format!("R3-M2.5 Merkle fold prove failed: {e}"))?;
    if !verify_keccak_merkle_path_proof(
        &lde_row,
        &batch.opening_proof,
        lde_index,
        &trace_commitment,
        &merkle_fold,
    ) {
        return Err("R3-M2.5 Merkle fold self-check failed".into());
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

    Ok(AggPcsCertificate {
        stmt_left_hash: context.left_child_hash,
        stmt_right_hash: context.right_child_hash,
        trace_commitment,
        natural_row,
        lde_index: lde_index as u32,
        lde_row,
        siblings: batch.opening_proof,
        merkle_fold,
        fri_fold_ys: fri_bundle.fold_ys,
        fri_folds: fri_bundle.fold_xs,
        deep_ros: deep_bundle.deep_ros,
        deep_ro_traces: deep_bundle.deep_ro_traces,
    })
}

/// Host-verifies a certificate against an AggregationAir transcript + context.
///
/// M3b4: when the cert covers all FRI queries, verification binds fold publics to the
/// transcript via FS+RO reconstruction, checks host OOD + FRI Mmcs, and verifies
/// Merkle/FriFold STARKs **without** Plonky3 AggregationAir FRI.
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
    if !verify_keccak_merkle_path_proof(
        &cert.lde_row,
        &cert.siblings,
        cert.lde_index as usize,
        &cert.trace_commitment,
        &cert.merkle_fold,
    ) {
        eprintln!("[AggPcsCertificate] Failed: Merkle fold STARK");
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

    if covers_all_devnet_fri_queries() {
        verify_agg_pcs_certificate_fri_bound(context, agg_transcript, cert)
    } else {
        // Partial query coverage: fall back to full rebuild.
        match build_agg_pcs_certificate(context, agg_transcript) {
            Ok(rebuilt) => {
                if rebuilt.trace_commitment != cert.trace_commitment
                    || rebuilt.lde_index != cert.lde_index
                    || rebuilt.lde_row != cert.lde_row
                    || rebuilt.siblings != cert.siblings
                    || rebuilt.merkle_fold != cert.merkle_fold
                    || rebuilt.fri_fold_ys != cert.fri_fold_ys
                    || rebuilt.fri_folds != cert.fri_folds
                    || rebuilt.deep_ros != cert.deep_ros
                    || rebuilt.deep_ro_traces != cert.deep_ro_traces
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

/// Binds cert to AggregationAir proof via PCS rebuild + OOD/Mmcs + FS/RO fold publics.
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

    if let Err(e) = verify_agg_ood(&proof) {
        eprintln!("[AggPcsCertificate] Failed: OOD: {e}");
        return false;
    }
    if let Err(e) = verify_agg_fri_openings(&proof) {
        eprintln!("[AggPcsCertificate] Failed: FRI Mmcs: {e}");
        return false;
    }

    let matrix = pad_air_matrix_for_uni_stark(build_agg_matrix(
        context.left_child_hash,
        context.right_child_hash,
    ));
    let config = devnet_circle_config();
    let pcs = config.pcs();
    let domain = <crate::plonky3_stark::config::Pcs as Pcs<
        crate::plonky3_stark::config::Challenge,
        crate::plonky3_stark::config::Challenger,
    >>::natural_domain_for_degree(pcs, matrix.height());
    let (comm, prover_data) = <crate::plonky3_stark::config::Pcs as Pcs<
        crate::plonky3_stark::config::Challenge,
        crate::plonky3_stark::config::Challenger,
    >>::commit(pcs, vec![(domain, matrix)]);
    if comm != proof.commitments.trace {
        eprintln!("[AggPcsCertificate] Failed: rebuilt PCS commitment mismatch");
        return false;
    }
    let trace_commitment = match commitment_root(&comm) {
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

    let lde_index = cert.lde_index as usize;
    let batch = pcs.mmcs.open_batch(lde_index, &prover_data);
    if batch.opened_values.first() != Some(&cert.lde_row) || batch.opening_proof != cert.siblings {
        eprintln!("[AggPcsCertificate] Failed: LDE opening mismatch");
        return false;
    }
    if !verify_agg_merkle_path(
        &cert.lde_row,
        &cert.siblings,
        lde_index,
        &cert.trace_commitment,
    ) {
        eprintln!("[AggPcsCertificate] Failed: Merkle path");
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
    }
}

//! AggregationAir PCS opening certificates (R3-M2 / M2.5 / M2.5b / M3a).
//!
//! Rebuild Circle PCS commitment, open an LDE row, host-check `Mmcs::verify_batch`,
//! attach a [`KeccakMerklePathProof`] (MerkleFoldAir + in-circuit Keccak-256
//! leaf/compress sponges), and a [`FriFoldStepProof`] bound to FRI
//! `final_poly` + last sibling (M3a; FS β replay is M3b).

use p3_commit::{BatchOpeningRef, Mmcs, Pcs};
use p3_field::PrimeCharacteristicRing;
use p3_matrix::{Dimensions, Matrix};
use p3_mersenne_31::Mersenne31;
use p3_uni_stark::{Proof, StarkGenericConfig};

use crate::aggregation::CHILD_HASH_LEN;
use crate::air::pad_air_matrix_for_uni_stark;
use crate::plonky3_stark::aggregation::{
    build_agg_matrix, verify_aggregation_proof, AggregationContext,
};
use crate::plonky3_stark::aggregation_air::AGG_WIDTH;
use crate::plonky3_stark::config::{devnet_circle_config, ValMmcs, WqcStarkConfig};
use crate::plonky3_stark::transcript_v4::decode_agg_proof_owned;

use super::agg_constraints::aggregation_air_constraints_hold;
use super::fri_fold_air::{verify_fri_fold_proof, FriFoldStepProof};
use super::fri_fold_bind::fri_fold_step_from_agg_proof;
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
    /// R3-M3a: in-circuit Circle FRI `fold_x` step bound to FRI openings.
    pub fri_fold: FriFoldStepProof,
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

/// Builds a PCS opening certificate for a verified AggregationAir transcript.
pub fn build_agg_pcs_certificate(
    context: &AggregationContext<'_>,
    agg_transcript: &[u8],
) -> Result<AggPcsCertificate, String> {
    if !verify_aggregation_proof(context, agg_transcript) {
        return Err("AggregationAir verification failed before PCS certificate".to_string());
    }
    let plonky3_bytes = decode_agg_proof_owned(agg_transcript, context)
        .ok_or_else(|| "malformed AggregationAir transcript".to_string())?;
    let proof: Proof<WqcStarkConfig> = postcard::from_bytes(&plonky3_bytes)
        .map_err(|e| format!("postcard decode AggregationAir proof: {e}"))?;

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

    let fri_fold = fri_fold_step_from_agg_proof(&proof)
        .map_err(|e| format!("R3-M3a FRI fold prove failed: {e}"))?;
    if !verify_fri_fold_proof(&fri_fold) {
        return Err("R3-M3a FRI fold self-check failed".into());
    }

    Ok(AggPcsCertificate {
        stmt_left_hash: context.left_child_hash,
        stmt_right_hash: context.right_child_hash,
        trace_commitment,
        natural_row,
        lde_index: lde_index as u32,
        lde_row,
        siblings: batch.opening_proof,
        merkle_fold,
        fri_fold,
    })
}

/// Host-verifies a certificate against an AggregationAir transcript + context.
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
    match build_agg_pcs_certificate(context, agg_transcript) {
        Ok(rebuilt) => {
            if rebuilt.trace_commitment != cert.trace_commitment
                || rebuilt.lde_index != cert.lde_index
                || rebuilt.lde_row != cert.lde_row
                || rebuilt.siblings != cert.siblings
                || rebuilt.merkle_fold != cert.merkle_fold
                || rebuilt.fri_fold != cert.fri_fold
            {
                eprintln!("[AggPcsCertificate] Failed: rebuilt certificate mismatch");
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
            if !verify_fri_fold_proof(&cert.fri_fold) {
                eprintln!("[AggPcsCertificate] Failed: FRI fold STARK");
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

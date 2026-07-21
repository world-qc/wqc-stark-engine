//! R3 recursive aggregation prove / verify (M1 digest binding + M2 AggregationAir PCS).

use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;
use p3_mersenne_31::Mersenne31;
use p3_uni_stark::{prove, verify};

use crate::aggregation::CHILD_HASH_LEN;
use crate::air::pad_air_matrix_for_uni_stark;
use crate::plonky3_stark::aggregation_air::AGG_WIDTH;
use crate::plonky3_stark::config::{devnet_circle_config, WqcStarkConfig};

use super::air::{
    RecursiveAggregationAir, REC_AGG_WIDTH, REC_KIND_AGG, REC_KIND_LEAF, REC_LEFT_AGG_ROW_COL,
    REC_LEFT_KIND_COL, REC_LEFT_OK_COL, REC_LEFT_PCS_OK_COL, REC_LEFT_STARK_DIGEST_COL,
    REC_LEFT_TRACE_COM_COL, REC_RIGHT_AGG_ROW_COL, REC_RIGHT_KIND_COL, REC_RIGHT_OK_COL,
    REC_RIGHT_PCS_OK_COL, REC_RIGHT_STARK_DIGEST_COL, REC_RIGHT_TRACE_COM_COL,
};
use super::air_m1::RecursiveAggregationAirM1;
use super::child_binding::STARK_DIGEST_LEN;
use super::context::RecursiveAggregationContext;
use super::leaf_pcs_cert::{leaf_bundle_stmt_digest, LeafPcsBundle};
use super::opening_cert::AggPcsCertificate;
use super::transcript_v5::{
    decode_rec_agg_proof_owned, has_rec_tail as has_v5_rec_tail,
    split_rec_tail as split_v5_rec_tail, V5_REC_TAIL_MARKER,
};
use super::transcript_v6::{
    decode_rec_agg_proof_owned_v6, encode_rec_agg_proof_v6, split_rec_tail_v6, V6_REC_TAIL_MARKER,
};

fn byte_to_m31(b: u8) -> Mersenne31 {
    Mersenne31::from_u32(b as u32)
}

fn push_bytes(row: &mut Vec<Mersenne31>, bytes: &[u8]) {
    for &b in bytes {
        row.push(byte_to_m31(b));
    }
}

fn push_commitment_or_zero(
    row: &mut Vec<Mersenne31>,
    kind: u8,
    agg_cert: &Option<AggPcsCertificate>,
    leaf_bundle: &Option<LeafPcsBundle>,
) -> Result<(), String> {
    match (kind, agg_cert, leaf_bundle) {
        (REC_KIND_LEAF, None, None) => {
            for _ in 0..32 {
                row.push(Mersenne31::ZERO);
            }
            Ok(())
        }
        (REC_KIND_LEAF, None, Some(bundle)) => {
            // Primary cert commitment column; multi-cert bundles use the first cert.
            let primary = bundle
                .certs
                .first()
                .ok_or_else(|| "empty leaf PCS bundle".to_string())?;
            push_bytes(row, &primary.trace_commitment);
            Ok(())
        }
        (REC_KIND_AGG, Some(cert), None) => {
            push_bytes(row, &cert.trace_commitment);
            Ok(())
        }
        (REC_KIND_AGG, None, _) => Err("kind=agg requires AggregationAir PCS certificate".into()),
        (REC_KIND_LEAF, Some(_), _) => {
            Err("kind=leaf must not carry AggregationAir certificate".into())
        }
        (REC_KIND_AGG, Some(_), Some(_)) => Err("kind=agg must not carry leaf PCS bundle".into()),
        (k, _, _) => Err(format!("invalid kind {k}")),
    }
}

fn push_natural_row_or_zero(
    row: &mut Vec<Mersenne31>,
    kind: u8,
    agg_cert: &Option<AggPcsCertificate>,
    leaf_bundle: &Option<LeafPcsBundle>,
) -> Result<(), String> {
    match (kind, agg_cert, leaf_bundle) {
        (REC_KIND_LEAF, None, None) => {
            for _ in 0..AGG_WIDTH {
                row.push(Mersenne31::ZERO);
            }
            Ok(())
        }
        (REC_KIND_LEAF, None, Some(bundle)) => {
            // Bundle stmt_digest = sha3(concat cert.stmt_digests); row cols 0..32 hold it as M31.
            let digest = leaf_bundle_stmt_digest(bundle);
            for &b in digest.iter().take(32) {
                row.push(byte_to_m31(b));
            }
            for _ in 32..AGG_WIDTH {
                row.push(Mersenne31::ZERO);
            }
            Ok(())
        }
        (REC_KIND_AGG, Some(cert), None) => {
            for v in cert.natural_row {
                row.push(v);
            }
            Ok(())
        }
        (REC_KIND_AGG, None, _) => Err("kind=agg requires AggregationAir PCS certificate".into()),
        (REC_KIND_LEAF, Some(_), _) => {
            Err("kind=leaf must not carry AggregationAir certificate".into())
        }
        (REC_KIND_AGG, Some(_), Some(_)) => Err("kind=agg must not carry leaf PCS bundle".into()),
        (k, _, _) => Err(format!("invalid kind {k}")),
    }
}

fn build_rec_matrix(
    ctx: &RecursiveAggregationContext<'_>,
) -> Result<RowMajorMatrix<Mersenne31>, String> {
    let mut row = Vec::with_capacity(REC_AGG_WIDTH);
    push_bytes(&mut row, &ctx.left_child_hash);
    push_bytes(&mut row, &ctx.right_child_hash);
    row.push(Mersenne31::ONE); // left_ok
    row.push(Mersenne31::ONE); // right_ok
    debug_assert_eq!(row.len(), REC_LEFT_STARK_DIGEST_COL);
    push_bytes(&mut row, &ctx.left_stark_digest);
    debug_assert_eq!(row.len(), REC_RIGHT_STARK_DIGEST_COL);
    push_bytes(&mut row, &ctx.right_stark_digest);
    debug_assert_eq!(row.len(), REC_LEFT_KIND_COL);
    row.push(byte_to_m31(ctx.left_kind));
    row.push(byte_to_m31(ctx.right_kind));
    debug_assert_eq!(row.len(), REC_LEFT_TRACE_COM_COL);

    push_commitment_or_zero(
        &mut row,
        ctx.left_kind,
        &ctx.left_agg_cert,
        &ctx.left_leaf_bundle,
    )?;
    debug_assert_eq!(row.len(), REC_RIGHT_TRACE_COM_COL);
    push_commitment_or_zero(
        &mut row,
        ctx.right_kind,
        &ctx.right_agg_cert,
        &ctx.right_leaf_bundle,
    )?;
    debug_assert_eq!(row.len(), REC_LEFT_AGG_ROW_COL);
    push_natural_row_or_zero(
        &mut row,
        ctx.left_kind,
        &ctx.left_agg_cert,
        &ctx.left_leaf_bundle,
    )?;
    debug_assert_eq!(row.len(), REC_RIGHT_AGG_ROW_COL);
    push_natural_row_or_zero(
        &mut row,
        ctx.right_kind,
        &ctx.right_agg_cert,
        &ctx.right_leaf_bundle,
    )?;
    debug_assert_eq!(row.len(), REC_LEFT_PCS_OK_COL);

    row.push(Mersenne31::ONE); // left_pcs_ok
    row.push(Mersenne31::ONE); // right_pcs_ok
    debug_assert_eq!(row.len(), REC_AGG_WIDTH);
    let _ = (
        REC_LEFT_OK_COL,
        REC_RIGHT_OK_COL,
        REC_RIGHT_KIND_COL,
        REC_RIGHT_PCS_OK_COL,
        CHILD_HASH_LEN,
        STARK_DIGEST_LEN,
    );

    let mut values = row.clone();
    values.extend(row);
    Ok(RowMajorMatrix::new(values, REC_AGG_WIDTH))
}

pub fn generate_recursive_aggregation_proof(
    context: &RecursiveAggregationContext<'_>,
) -> Result<Vec<u8>, String> {
    if context.parent_task_id.is_empty() {
        return Err("parent_task_id is required".to_string());
    }
    if context.left_kind > REC_KIND_AGG || context.right_kind > REC_KIND_AGG {
        return Err("kind must be 0 (leaf) or 1 (agg)".to_string());
    }

    if context.left_kind == REC_KIND_AGG && context.left_agg_cert.is_none() {
        return Err("kind=agg requires left AggregationAir PCS certificate".into());
    }
    if context.right_kind == REC_KIND_AGG && context.right_agg_cert.is_none() {
        return Err("kind=agg requires right AggregationAir PCS certificate".into());
    }
    if context.left_kind == REC_KIND_LEAF && context.left_agg_cert.is_some() {
        return Err("kind=leaf must not carry left AggregationAir certificate".into());
    }
    if context.right_kind == REC_KIND_LEAF && context.right_agg_cert.is_some() {
        return Err("kind=leaf must not carry right AggregationAir certificate".into());
    }
    if context.left_kind == REC_KIND_AGG && context.left_leaf_bundle.is_some() {
        return Err("kind=agg must not carry left leaf PCS bundle".into());
    }
    if context.right_kind == REC_KIND_AGG && context.right_leaf_bundle.is_some() {
        return Err("kind=agg must not carry right leaf PCS bundle".into());
    }

    let matrix = pad_air_matrix_for_uni_stark(build_rec_matrix(context)?);
    let config = devnet_circle_config();
    let air = RecursiveAggregationAir;
    let proof = prove(&config, &air, matrix, &[]);
    let plonky3_bytes =
        postcard::to_allocvec(&proof).map_err(|e| format!("postcard encode failed: {e}"))?;
    Ok(encode_rec_agg_proof_v6(context, &plonky3_bytes))
}

pub fn verify_recursive_aggregation_proof(
    context: &RecursiveAggregationContext<'_>,
    proof: &[u8],
) -> bool {
    if context.parent_task_id.is_empty() {
        eprintln!("[RecursiveAggregationAir] Failed: parent_task_id is empty");
        return false;
    }

    // Prefer V6 (R3-M2); fall back to legacy V5 (R3-M1) when certs are absent.
    let (plonky3_bytes, use_m1_air) =
        if let Some(bytes) = decode_rec_agg_proof_owned_v6(proof, context) {
            if context.left_kind == REC_KIND_AGG && context.left_agg_cert.is_none() {
                eprintln!("[RecursiveAggregationAir] Failed: V6 left agg cert missing");
                return false;
            }
            if context.right_kind == REC_KIND_AGG && context.right_agg_cert.is_none() {
                eprintln!("[RecursiveAggregationAir] Failed: V6 right agg cert missing");
                return false;
            }
            (bytes, false)
        } else if context.left_agg_cert.is_none()
            && context.right_agg_cert.is_none()
            && context.left_leaf_bundle.is_none()
            && context.right_leaf_bundle.is_none()
        {
            match decode_rec_agg_proof_owned(proof, context) {
                Some(bytes) => (bytes, true),
                None => {
                    eprintln!("[RecursiveAggregationAir] Failed: malformed V5/V6 transcript");
                    return false;
                }
            }
        } else {
            eprintln!("[RecursiveAggregationAir] Failed: malformed V6 transcript");
            return false;
        };

    let p3_proof: p3_uni_stark::Proof<WqcStarkConfig> = match postcard::from_bytes(&plonky3_bytes) {
        Ok(proof) => proof,
        Err(e) => {
            eprintln!("[RecursiveAggregationAir] Failed: postcard decode: {e}");
            return false;
        }
    };
    let config = devnet_circle_config();
    let verified = if use_m1_air {
        verify(&config, &RecursiveAggregationAirM1, &p3_proof, &[]).is_ok()
    } else {
        verify(&config, &RecursiveAggregationAir, &p3_proof, &[]).is_ok()
    };
    if verified {
        eprintln!(
            "[RecursiveAggregationAir] Verification success (R3-{} compose={})",
            if use_m1_air { "M1" } else { "M2" },
            context.compose_label
        );
        true
    } else {
        eprintln!("[RecursiveAggregationAir] Failed: Plonky3 verify error");
        false
    }
}

/// Splits a compose blob's recursive aggregation tail (V6 preferred, else V5).
pub fn split_rec_tail(proof: &[u8]) -> Option<(&[u8], &[u8])> {
    if let Some(pair) = split_rec_tail_v6(proof) {
        return Some(pair);
    }
    split_v5_rec_tail(proof)
}

pub fn has_rec_tail(proof: &[u8]) -> bool {
    proof
        .windows(V6_REC_TAIL_MARKER.len())
        .any(|w| w == V6_REC_TAIL_MARKER)
        || has_v5_rec_tail(proof)
}

pub fn append_rec_tail(body: Vec<u8>, rec_proof: &[u8]) -> Vec<u8> {
    // New proofs are V6; marker is chosen by the encoder inside `rec_proof`.
    // Detect which marker the inner transcript uses.
    if rec_proof
        .windows(super::transcript_v6::V6_REC_AGG_INNER_MARKER.len())
        .any(|w| w == super::transcript_v6::V6_REC_AGG_INNER_MARKER)
    {
        super::transcript_v6::append_rec_tail_v6(body, rec_proof)
    } else {
        let mut out = body;
        out.extend_from_slice(V5_REC_TAIL_MARKER);
        out.extend_from_slice(&(rec_proof.len() as u32).to_le_bytes());
        out.extend_from_slice(rec_proof);
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::plonky3_stark::generate_aggregation_proof;
    use crate::plonky3_stark::recursion::opening_cert::build_agg_pcs_certificate;
    use crate::plonky3_stark::AggregationContext;

    #[test]
    #[ignore = "slow; local only — not run in CI"]
    fn recursive_agg_leaf_pair_roundtrip() {
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
        };
        let proof = generate_recursive_aggregation_proof(&ctx).expect("prove");
        assert!(verify_recursive_aggregation_proof(&ctx, &proof));
        let wrapped = crate::plonky3_stark::recursion::transcript_v6::append_rec_tail_v6(
            vec![1, 2, 3],
            &proof,
        );
        assert!(has_rec_tail(&wrapped));
    }

    #[test]
    #[ignore = "slow; local only — not run in CI"]
    fn recursive_agg_with_child_agg_certs() {
        let agg_ctx = AggregationContext {
            parent_task_id: "child-parent",
            compose_label: "L1:0",
            manifest_root_hash: "",
            left_child_hash: [7u8; CHILD_HASH_LEN],
            right_child_hash: [8u8; CHILD_HASH_LEN],
        };
        let agg_proof = generate_aggregation_proof(&agg_ctx).expect("agg");
        let cert = build_agg_pcs_certificate(&agg_ctx, &agg_proof).expect("cert");

        let ctx = RecursiveAggregationContext {
            parent_task_id: "parent",
            compose_label: "root",
            manifest_root_hash: "m",
            left_child_hash: [1u8; CHILD_HASH_LEN],
            right_child_hash: [2u8; CHILD_HASH_LEN],
            left_stark_digest: [3u8; STARK_DIGEST_LEN],
            right_stark_digest: [4u8; STARK_DIGEST_LEN],
            left_kind: REC_KIND_AGG,
            right_kind: REC_KIND_AGG,
            left_agg_cert: Some(cert.clone()),
            right_agg_cert: Some(cert),
            left_leaf_bundle: None,
            right_leaf_bundle: None,
        };
        let proof = generate_recursive_aggregation_proof(&ctx).expect("prove");
        assert!(verify_recursive_aggregation_proof(&ctx, &proof));
    }
}

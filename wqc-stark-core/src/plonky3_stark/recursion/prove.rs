//! R3-M1 prove / verify for `RecursiveAggregationAir`.

use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;
use p3_mersenne_31::Mersenne31;
use p3_uni_stark::{prove, verify};

use crate::aggregation::CHILD_HASH_LEN;
use crate::air::pad_air_matrix_for_uni_stark;
use crate::plonky3_stark::config::{devnet_circle_config, WqcStarkConfig};

use super::air::{
    RecursiveAggregationAir, REC_AGG_WIDTH, REC_LEFT_KIND_COL, REC_LEFT_OK_COL,
    REC_LEFT_STARK_DIGEST_COL, REC_RIGHT_KIND_COL, REC_RIGHT_OK_COL, REC_RIGHT_STARK_DIGEST_COL,
};
use super::child_binding::STARK_DIGEST_LEN;
use super::context::RecursiveAggregationContext;
use super::transcript_v5::{decode_rec_agg_proof_owned, encode_rec_agg_proof};

fn byte_to_m31(b: u8) -> Mersenne31 {
    Mersenne31::from_u32(b as u32)
}

fn build_rec_matrix(ctx: &RecursiveAggregationContext<'_>) -> RowMajorMatrix<Mersenne31> {
    let mut row = Vec::with_capacity(REC_AGG_WIDTH);
    for b in ctx.left_child_hash {
        row.push(byte_to_m31(b));
    }
    for b in ctx.right_child_hash {
        row.push(byte_to_m31(b));
    }
    row.push(Mersenne31::ONE); // left_ok
    row.push(Mersenne31::ONE); // right_ok
    debug_assert_eq!(row.len(), REC_LEFT_STARK_DIGEST_COL);
    for b in ctx.left_stark_digest {
        row.push(byte_to_m31(b));
    }
    debug_assert_eq!(row.len(), REC_RIGHT_STARK_DIGEST_COL);
    for b in ctx.right_stark_digest {
        row.push(byte_to_m31(b));
    }
    debug_assert_eq!(row.len(), REC_LEFT_KIND_COL);
    row.push(byte_to_m31(ctx.left_kind));
    row.push(byte_to_m31(ctx.right_kind));
    debug_assert_eq!(row.len(), REC_AGG_WIDTH);
    let _ = (REC_LEFT_OK_COL, REC_RIGHT_OK_COL, REC_RIGHT_KIND_COL);

    let mut values = row.clone();
    values.extend(row);
    RowMajorMatrix::new(values, REC_AGG_WIDTH)
}

pub fn generate_recursive_aggregation_proof(
    context: &RecursiveAggregationContext<'_>,
) -> Result<Vec<u8>, String> {
    if context.parent_task_id.is_empty() {
        return Err("parent_task_id is required".to_string());
    }
    if context.left_kind > 1 || context.right_kind > 1 {
        return Err("kind must be 0 (leaf) or 1 (agg)".to_string());
    }

    let matrix = pad_air_matrix_for_uni_stark(build_rec_matrix(context));
    let config = devnet_circle_config();
    let air = RecursiveAggregationAir;
    let proof = prove(&config, &air, matrix, &[]);
    let plonky3_bytes =
        postcard::to_allocvec(&proof).map_err(|e| format!("postcard encode failed: {e}"))?;
    Ok(encode_rec_agg_proof(context, &plonky3_bytes))
}

pub fn verify_recursive_aggregation_proof(
    context: &RecursiveAggregationContext<'_>,
    proof: &[u8],
) -> bool {
    if context.parent_task_id.is_empty() {
        eprintln!("[RecursiveAggregationAir] Failed: parent_task_id is empty");
        return false;
    }
    let plonky3_bytes = match decode_rec_agg_proof_owned(proof, context) {
        Some(bytes) => bytes,
        None => {
            eprintln!("[RecursiveAggregationAir] Failed: malformed V5 transcript");
            return false;
        }
    };
    let p3_proof: p3_uni_stark::Proof<WqcStarkConfig> = match postcard::from_bytes(&plonky3_bytes) {
        Ok(proof) => proof,
        Err(e) => {
            eprintln!("[RecursiveAggregationAir] Failed: postcard decode: {e}");
            return false;
        }
    };
    let config = devnet_circle_config();
    let air = RecursiveAggregationAir;
    match verify(&config, &air, &p3_proof, &[]) {
        Ok(()) => {
            eprintln!(
                "[RecursiveAggregationAir] Verification success (R3-M1 compose={})",
                context.compose_label
            );
            true
        }
        Err(e) => {
            eprintln!("[RecursiveAggregationAir] Failed: Plonky3 verify error: {e:?}");
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn recursive_agg_roundtrip() {
        let ctx = RecursiveAggregationContext {
            parent_task_id: "parent",
            compose_label: "root",
            manifest_root_hash: "m",
            left_child_hash: [1u8; CHILD_HASH_LEN],
            right_child_hash: [2u8; CHILD_HASH_LEN],
            left_stark_digest: [3u8; STARK_DIGEST_LEN],
            right_stark_digest: [4u8; STARK_DIGEST_LEN],
            left_kind: 0,
            right_kind: 1,
        };
        let proof = generate_recursive_aggregation_proof(&ctx).expect("prove");
        assert!(verify_recursive_aggregation_proof(&ctx, &proof));
    }
}

//! R2 aggregation prove / verify (Plonky3 uni-STARK).

pub use super::aggregation_air::{AggregationAir, AGG_WIDTH};

use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;
use p3_mersenne_31::Mersenne31;
use p3_uni_stark::{prove, verify};

use crate::aggregation::CHILD_HASH_LEN;
use crate::air::pad_air_matrix_for_uni_stark;

use super::config::{
    circle_config_for_security_level, fri_num_queries_for_security_level, WqcStarkConfig,
};
use super::recursion::{circle_config_matching_proof, fri_queries_from_proof};
use super::transcript_v4::{decode_agg_proof_owned, encode_agg_proof};

/// Public binding for an aggregation STARK over a proof-tree pair.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AggregationContext<'a> {
    pub parent_task_id: &'a str,
    pub compose_label: &'a str,
    pub manifest_root_hash: &'a str,
    pub left_child_hash: [u8; CHILD_HASH_LEN],
    pub right_child_hash: [u8; CHILD_HASH_LEN],
    /// Orchestrator security tier; empty → FRI default (40).
    pub security_level: &'a str,
}

fn byte_to_m31(b: u8) -> Mersenne31 {
    Mersenne31::from_u32(b as u32)
}

pub(crate) fn build_agg_matrix(
    left_hash: [u8; CHILD_HASH_LEN],
    right_hash: [u8; CHILD_HASH_LEN],
) -> RowMajorMatrix<Mersenne31> {
    let mut row = Vec::with_capacity(AGG_WIDTH);
    for b in left_hash {
        row.push(byte_to_m31(b));
    }
    for b in right_hash {
        row.push(byte_to_m31(b));
    }
    row.push(Mersenne31::ONE);
    row.push(Mersenne31::ONE);

    let mut values = row.clone();
    values.extend(row);
    RowMajorMatrix::new(values, AGG_WIDTH)
}

/// Generates a v4 aggregation STARK transcript after native child verification.
pub fn generate_aggregation_proof(context: &AggregationContext<'_>) -> Result<Vec<u8>, String> {
    if context.parent_task_id.is_empty() {
        return Err("parent_task_id is required".to_string());
    }

    let matrix = build_agg_matrix(context.left_child_hash, context.right_child_hash);
    let matrix = pad_air_matrix_for_uni_stark(matrix);

    let config = circle_config_for_security_level(context.security_level, 1);
    let air = AggregationAir;
    let proof = prove(&config, &air, matrix, &[]);
    let plonky3_bytes =
        postcard::to_allocvec(&proof).map_err(|e| format!("postcard encode failed: {e}"))?;

    Ok(encode_agg_proof(context, &plonky3_bytes))
}

/// Verifies a v4 aggregation STARK transcript.
pub fn verify_aggregation_proof(context: &AggregationContext<'_>, proof: &[u8]) -> bool {
    if context.parent_task_id.is_empty() {
        eprintln!("[AggregationAir] Failed: parent_task_id is empty");
        return false;
    }

    let plonky3_bytes = match decode_agg_proof_owned(proof, context) {
        Some(bytes) => bytes,
        None => {
            eprintln!("[AggregationAir] Failed: malformed aggregation transcript");
            return false;
        }
    };

    let p3_proof: p3_uni_stark::Proof<WqcStarkConfig> = match postcard::from_bytes(&plonky3_bytes) {
        Ok(proof) => proof,
        Err(e) => {
            eprintln!("[AggregationAir] Failed: postcard decode: {e}");
            return false;
        }
    };

    if let Ok(n) = fri_queries_from_proof(&p3_proof) {
        if !context.security_level.is_empty()
            && n != fri_num_queries_for_security_level(context.security_level)
        {
            eprintln!(
                "[AggregationAir] Failed: FRI query count {n} != security_level {}",
                context.security_level
            );
            return false;
        }
    }
    let config = match circle_config_matching_proof(&p3_proof) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("[AggregationAir] Failed: config from proof: {e}");
            return false;
        }
    };
    let air = AggregationAir;
    match verify(&config, &air, &p3_proof, &[]) {
        Ok(()) => {
            eprintln!(
                "[AggregationAir] Verification success (R2 compose={})",
                context.compose_label
            );
            true
        }
        Err(e) => {
            eprintln!("[AggregationAir] Failed: Plonky3 verify error: {e:?}");
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_context() -> AggregationContext<'static> {
        AggregationContext {
            parent_task_id: "parent-task",
            compose_label: "L1:0",
            manifest_root_hash: "",
            left_child_hash: [7u8; CHILD_HASH_LEN],
            right_child_hash: [9u8; CHILD_HASH_LEN],
            security_level: "",
        }
    }

    #[test]
    fn aggregation_stark_low_security_roundtrip() {
        let ctx = AggregationContext {
            parent_task_id: "parent-task",
            compose_label: "L1:0",
            manifest_root_hash: "",
            left_child_hash: [7u8; CHILD_HASH_LEN],
            right_child_hash: [9u8; CHILD_HASH_LEN],
            security_level: "low",
        };
        let proof = generate_aggregation_proof(&ctx).expect("prove");
        assert!(verify_aggregation_proof(&ctx, &proof));
        let mut ultra = ctx.clone();
        ultra.security_level = "ultra";
        assert!(!verify_aggregation_proof(&ultra, &proof));
    }

    #[test]
    fn aggregation_stark_roundtrip() {
        let ctx = sample_context();
        let proof = generate_aggregation_proof(&ctx).expect("prove");
        assert!(verify_aggregation_proof(&ctx, &proof));
    }

    #[test]
    fn aggregation_rejects_tampered_hash_binding() {
        let ctx = sample_context();
        let proof = generate_aggregation_proof(&ctx).expect("prove");
        let mut bad = ctx;
        bad.left_child_hash[0] ^= 0xFF;
        assert!(!verify_aggregation_proof(&bad, &proof));
    }
}

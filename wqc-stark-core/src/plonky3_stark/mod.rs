//! Phase 3: Plonky3 `p3-uni-stark` prover and verifier (Mersenne31 Circle STARK).

mod config;
mod quantum_air;
mod transcript_v2;
#[cfg(feature = "plonky3-stark")]
mod aggregation;
#[cfg(feature = "plonky3-stark")]
mod aggregation_air;
#[cfg(feature = "plonky3-stark")]
mod transcript_v4;

pub use config::devnet_circle_config;
pub use quantum_air::QuantumExecutionAir;
pub use transcript_v2::{decode_proof_v2_owned, encode_proof_v2};
#[cfg(feature = "plonky3-stark")]
pub use aggregation::{generate_aggregation_proof, verify_aggregation_proof, AggregationContext};
#[cfg(feature = "plonky3-stark")]
pub use transcript_v4::{append_agg_tail, has_agg_tail, split_agg_tail};

use p3_field::PrimeCharacteristicRing;
use p3_mersenne_31::Mersenne31;
use p3_uni_stark::{prove, verify};

use crate::air::{evaluate_air_sum, pad_air_matrix_for_uni_stark, trace_to_air_matrix};
use crate::transcript::{StarkContext, V2_MARKER};

/// Generates a v2 Plonky3 uni-STARK proof transcript.
pub fn generate_plonky3_proof(
    context: &StarkContext<'_>,
    execution_trace: &[f64],
) -> Result<Vec<u8>, String> {
    if execution_trace.is_empty() {
        return Err("execution trace is empty".to_string());
    }

    let matrix = trace_to_air_matrix(execution_trace).ok_or_else(|| {
        "invalid execution trace shape (must be non-empty multiple of TRACE_WIDTH)".to_string()
    })?;

    if evaluate_air_sum(&matrix) != Mersenne31::ZERO {
        return Err(
            "execution trace does not satisfy AIR constraints (air_sum != 0)".to_string(),
        );
    }

    let matrix = pad_air_matrix_for_uni_stark(matrix);

    let config = devnet_circle_config();
    let air = QuantumExecutionAir;
    let proof = prove(&config, &air, matrix, &[]);
    let plonky3_bytes =
        postcard::to_allocvec(&proof).map_err(|e| format!("postcard encode failed: {e}"))?;

    Ok(encode_proof_v2(context, &plonky3_bytes))
}

/// Verifies a v2 Plonky3 uni-STARK proof transcript.
pub fn verify_plonky3_proof(context: &StarkContext<'_>, proof: &[u8]) -> bool {
    if !proof.starts_with(context.sub_task_id.as_bytes()) {
        eprintln!("[STARK Core] Failed: sub_task_id prefix mismatch (v2)");
        return false;
    }

    let prefix_len = context.sub_task_id.len();
    if !proof[prefix_len..].starts_with(V2_MARKER) {
        eprintln!("[STARK Core] Failed: v2 marker missing");
        return false;
    }

    let plonky3_bytes = match decode_proof_v2_owned(proof, context) {
        Some(bytes) => bytes,
        None => {
            eprintln!("[STARK Core] Failed: malformed v2 proof payload");
            return false;
        }
    };

    let p3_proof: p3_uni_stark::Proof<config::WqcStarkConfig> =
        match postcard::from_bytes(&plonky3_bytes) {
            Ok(proof) => proof,
            Err(e) => {
                eprintln!("[STARK Core] Failed: postcard decode v2 proof: {e}");
                return false;
            }
        };

    let config = devnet_circle_config();
    let air = QuantumExecutionAir;
    match verify(&config, &air, &p3_proof, &[]) {
        Ok(()) => {
            eprintln!("[STARK Core] Verification success (v2 Plonky3 STARK)");
            true
        }
        Err(e) => {
            eprintln!("[STARK Core] Failed: Plonky3 verify error: {e:?}");
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::transcript::StarkContext;

    fn context() -> StarkContext<'static> {
        StarkContext {
            circuit_id: "c1",
            sub_task_id: "sub-v2",
            node_id: "n1",
            slice_id: "0",
            output_hash: "out-hash",
        }
    }

    #[test]
    fn empty_circuit_v2_roundtrip() {
        let ctx = context();
        let trace = vec![0.0, 0.0, 0.0, 1.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0];
        let proof = generate_plonky3_proof(&ctx, &trace).expect("prove");
        assert!(verify_plonky3_proof(&ctx, &proof));
    }

    #[test]
    fn honest_h_trace_v2_roundtrip() {
        let ctx = context();
        let inv_sqrt2 = 1.0 / 2.0f64.sqrt();
        let trace = vec![
            4.0, 0.0, 0.0, 1.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0, inv_sqrt2,
            0.0, inv_sqrt2, 0.0, 0.0,
        ];
        let proof = generate_plonky3_proof(&ctx, &trace).expect("prove");
        assert!(verify_plonky3_proof(&ctx, &proof));
    }
}

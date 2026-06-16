pub mod air;
pub mod trace_spec;
pub mod transcript;

#[cfg(feature = "plonky3-stark")]
pub mod plonky3_stark;

pub use air::{
    boundary_from_matrix, evaluate_air_sum, evaluate_execution_trace, f64_to_m31,
    selector_index_for_gate, selectors_for_gate, trace_to_air_matrix, QuantumAirRow,
};
pub use trace_spec::{
    AIR_WIDTH, FIXED_POINT_SCALE, GATE_CCNOT, GATE_CNOT, GATE_CZ, GATE_H, GATE_RX, GATE_RY,
    GATE_RZ, GATE_S, GATE_T, GATE_X, GATE_Y, GATE_Z, SELECTOR_COUNT, TRACE_WIDTH,
};
pub use transcript::{
    air_digest_from_trace, decode_proof_v1_owned, encode_proof_v1, find_marker, StarkContext,
    LEGACY_MARKER, V1_MARKER, V2_MARKER,
};

use transcript::verify_public_input_binding;

/// Generates a v1 AIR commitment proof: embeds the execution trace and AIR digest.
///
/// This is **not** a full STARK (no FRI / polynomial commitments). Phase 3 adds Plonky3 uni-STARK.
pub fn generate_stark_proof(context: &StarkContext<'_>, execution_trace: &[f64]) -> Vec<u8> {
    if execution_trace.is_empty() {
        return Vec::new();
    }

    let (air_sum, boundary) = match air_digest_from_trace(execution_trace) {
        Some(digest) => digest,
        None => return Vec::new(),
    };

    encode_proof_v1(context, execution_trace, air_sum, boundary)
}

/// Verifies a v1 proof: public-input binding, trace re-evaluation, and boundary check.
pub fn verify_stark_proof_core(context: &StarkContext<'_>, proof: &[u8]) -> bool {
    if proof.is_empty() {
        eprintln!("[STARK Core] Failed: proof is empty");
        return false;
    }

    for (name, value) in [
        ("circuit_id", context.circuit_id),
        ("sub_task_id", context.sub_task_id),
        ("node_id", context.node_id),
        ("slice_id", context.slice_id),
        ("output_hash", context.output_hash),
    ] {
        if value.is_empty() {
            eprintln!("[STARK Core] Failed: {} is empty", name);
            return false;
        }
    }

    if !proof.starts_with(context.sub_task_id.as_bytes()) {
        eprintln!("[STARK Core] Failed: sub_task_id prefix mismatch");
        return false;
    }

    let (marker_index, marker) = match find_marker(proof, context.sub_task_id) {
        Some(found) => found,
        None => {
            eprintln!("[STARK Core] Failed: transcript marker not found");
            return false;
        }
    };

    if marker == LEGACY_MARKER {
        eprintln!(
            "[STARK Core] Failed: legacy proof format (no embedded trace); upgrade prover to v1"
        );
        return false;
    }

    if marker == V2_MARKER {
        #[cfg(feature = "plonky3-stark")]
        {
            return plonky3_stark::verify_plonky3_proof(context, proof);
        }
        #[cfg(not(feature = "plonky3-stark"))]
        {
            eprintln!("[STARK Core] Failed: v2 Plonky3 proof but `plonky3-stark` feature disabled");
            return false;
        }
    }

    let binding_start = marker_index + V1_MARKER.len();
    let payload_start = match verify_public_input_binding(proof, binding_start, context) {
        Some(offset) => offset,
        None => return false,
    };

    let (trace, claimed_sum, claimed_boundary) =
        match transcript::decode_proof_v1_payload(proof, payload_start) {
            Some((trace, sum, boundary, end)) if end == proof.len() => (trace, sum, boundary),
            _ => {
                eprintln!("[STARK Core] Failed: malformed v1 proof payload");
                return false;
            }
        };

    let (recomputed_sum, recomputed_boundary) = match air_digest_from_trace(&trace) {
        Some(digest) => digest,
        None => {
            eprintln!("[STARK Core] Failed: invalid embedded execution trace");
            return false;
        }
    };

    if recomputed_sum != claimed_sum {
        eprintln!(
            "[STARK Core] Failed: embedded AIR sum mismatch (claimed {}, recomputed {})",
            claimed_sum, recomputed_sum
        );
        return false;
    }

    if recomputed_sum != 0 {
        eprintln!("[STARK Core] Failed: air_evaluation_sum is non-zero ({recomputed_sum})");
        return false;
    }

    if recomputed_boundary != claimed_boundary {
        eprintln!("[STARK Core] Failed: boundary amplitude mismatch");
        return false;
    }

    eprintln!("[STARK Core] Verification success (v1 AIR, trace_len={})", trace.len());
    true
}

#[cfg(test)]
mod integration_tests {
    use super::*;

    fn context() -> StarkContext<'static> {
        StarkContext {
            circuit_id: "c1",
            sub_task_id: "sub-1",
            node_id: "n1",
            slice_id: "0",
            output_hash: "out-hash",
        }
    }

    #[test]
    fn honest_empty_circuit_roundtrip() {
        let ctx = context();
        let trace = vec![0.0, 0.0, 0.0, 1.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0];
        let proof = generate_stark_proof(&ctx, &trace);
        assert!(verify_stark_proof_core(&ctx, &proof));
    }

    #[test]
    fn tampered_air_sum_rejected() {
        let ctx = context();
        let trace = vec![0.0, 0.0, 0.0, 1.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0];
        let (sum, boundary) = air_digest_from_trace(&trace).unwrap();
        let mut proof = encode_proof_v1(&ctx, &trace, sum, boundary);
        let len = proof.len();
        proof[len - 20] ^= 0xFF;
        assert!(!verify_stark_proof_core(&ctx, &proof));
    }
}

pub mod air;
pub mod aggregation;
pub mod distribution;
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
pub use aggregation::{
    compose_stark_proofs, verify_child_proof, verify_composed_proof, verify_root_proof,
    ComposeContext, ComposeHeader, ParsedLeafBinding, RootVerifyContext, V3_COMPOSE_MARKER,
};
pub use distribution::{
    append_distribution_tail, base_proof_without_distribution_tail, calculate_probability_digest,
    calculate_terminal_statevector_digest, decode_and_verify_distribution_tail,
    decode_distribution_segment, sample_counts_from_probabilities, split_distribution_tail,
    verify_distribution_binding, BornBinding, DistributionSegment, DIST_V1_MARKER, DIST_V2_MARKER,
};
pub use transcript::{
    air_digest_from_trace, decode_proof_v1_owned, encode_proof_v1, find_marker, StarkContext,
    LEGACY_MARKER, V1_MARKER, V2_MARKER,
};

use transcript::verify_public_input_binding;

/// Reports whether a proof binds unitary v2 and Born tails via `terminal_statevector_digest`.
pub fn proof_has_unitary_statevector_link(proof: &[u8]) -> bool {
    distribution::split_distribution_tail(proof)
        .and_then(|(_, tail)| tail)
        .and_then(|(payload, marker)| {
            distribution::decode_and_verify_distribution_tail(payload, marker)
        })
        .and_then(|seg| seg.born_binding)
        .is_some_and(|b| !b.terminal_statevector_digest.is_empty())
}

/// Generates a v2 Plonky3 uni-STARK proof transcript (requires `plonky3-stark` feature).
#[cfg(feature = "plonky3-stark")]
pub fn generate_plonky3_stark_proof(
    context: &StarkContext<'_>,
    execution_trace: &[f64],
) -> Result<Vec<u8>, String> {
    plonky3_stark::generate_plonky3_proof(context, execution_trace)
}

#[cfg(feature = "plonky3-stark")]
pub use plonky3_stark::{
    append_born_stark_tail, generate_born_stark_proof, has_born_stark_tail, segment_supports_born_zk,
    verify_born_stark_proof, BornStarkContext, BORN_STARK_TAIL_MARKER, BORN_ZK_MAX_QUBITS,
};

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

    let base = crate::distribution::base_proof_without_distribution_tail(proof);
    let binding_start = marker_index + V1_MARKER.len();
    let payload_start = match verify_public_input_binding(base, binding_start, context) {
        Some(offset) => offset,
        None => return false,
    };

    let (trace, claimed_sum, claimed_boundary) =
        match transcript::decode_proof_v1_payload(base, payload_start) {
            Some((trace, sum, boundary, end)) if end == base.len() => (trace, sum, boundary),
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

    if let Some((_, Some((dist_payload, marker)))) = crate::distribution::split_distribution_tail(proof) {
        if crate::distribution::decode_and_verify_distribution_tail(dist_payload, marker).is_none() {
            eprintln!("[STARK Core] Failed: invalid distribution tail");
            return false;
        }
        eprintln!(
            "[STARK Core] Verification success (v1 AIR, trace_len={}, distribution tail)",
            trace.len()
        );
        return true;
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
            terminal_statevector_digest: "",
        }
    }

    #[test]
    fn honest_empty_circuit_roundtrip() {
        let ctx = context();
        let trace = crate::trace_spec::idle_qubit0_trace();
        let proof = generate_stark_proof(&ctx, &trace);
        assert!(verify_stark_proof_core(&ctx, &proof));
    }

    #[test]
    fn tampered_air_sum_rejected() {
        let ctx = context();
        let trace = crate::trace_spec::idle_qubit0_trace();
        let (sum, boundary) = air_digest_from_trace(&trace).unwrap();
        let mut proof = encode_proof_v1(&ctx, &trace, sum, boundary);
        let len = proof.len();
        proof[len - 20] ^= 0xFF;
        assert!(!verify_stark_proof_core(&ctx, &proof));
    }

    #[test]
    fn honest_h_trace_roundtrip() {
        let ctx = context();
        let trace = crate::trace_spec::golden_h_q0_trace();
        let proof = generate_stark_proof(&ctx, &trace);
        assert!(verify_stark_proof_core(&ctx, &proof));
    }

    #[cfg(feature = "plonky3-stark")]
    #[test]
    fn v1_and_v2_dual_prove_on_golden_traces() {
        let ctx = context();
        for trace in [
            crate::trace_spec::idle_qubit0_trace(),
            crate::trace_spec::golden_h_q0_trace(),
        ] {
            let v1 = generate_stark_proof(&ctx, &trace);
            assert!(verify_stark_proof_core(&ctx, &v1));
            let v2 = generate_plonky3_stark_proof(&ctx, &trace).expect("v2 prove");
            assert!(verify_stark_proof_core(&ctx, &v2));
        }
    }
}

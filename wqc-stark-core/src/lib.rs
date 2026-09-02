pub mod aggregation;
pub mod air;
pub mod distribution;
pub mod shrink;
pub mod trace_spec;
pub mod trajectory;
pub mod transcript;

#[cfg(feature = "plonky3-stark")]
pub mod plonky3_stark;

pub use aggregation::{
    born_proof_view, compose_stark_proofs, compose_stark_proofs_with_pcs,
    is_unitary_born_leaf_compose, is_unitary_trajectory_leaf_compose, parse_leaf_binding,
    trajectory_proof_view, verify_child_proof, verify_composed_proof, verify_root_proof,
    ComposeContext, ComposeHeader, ParsedLeafBinding, RootVerifyContext,
    UNITARY_BORN_COMPOSE_LABEL, UNITARY_TRAJ_COMPOSE_LABEL, V3_COMPOSE_MARKER,
};
#[cfg(feature = "plonky3-stark")]
pub use aggregation::{
    compose_unitary_born_leaf, compose_unitary_trajectory_leaf, verify_unitary_born_leaf_compose,
    verify_unitary_trajectory_leaf_compose,
};
pub use air::evaluate_execution_trace;
pub use air::trajectory::z_marginal_from_statevector;
pub use distribution::{
    append_distribution_tail, base_proof_without_distribution_tail, calculate_probability_digest,
    calculate_terminal_statevector_digest, canonicalize_terminal_statevector,
    decode_and_verify_distribution_tail, decode_distribution_segment,
    sample_counts_from_probabilities, split_distribution_tail, verify_distribution_binding,
    BornBinding, DistributionSegment, DIST_V1_MARKER, DIST_V2_MARKER,
};
pub use trace_spec::{
    AIR_WIDTH, FIXED_POINT_SCALE, GATE_CCNOT, GATE_CNOT, GATE_CZ, GATE_H, GATE_RX, GATE_RY,
    GATE_RZ, GATE_S, GATE_T, GATE_X, GATE_Y, GATE_Z, SELECTOR_COUNT, TRACE_WIDTH,
};
pub use trajectory::{
    append_trajectory_tail, base_proof_without_aux_tails, calculate_trajectory_digest,
    counts_from_trajectory_segment, decode_and_verify_trajectory_tail, format_trajectory_json,
    has_trajectory_tail, peek_trajectory_unitary_link_digest, split_trajectory_tail,
    verify_trajectory_binding, TrajectoryMarginalWitness, TrajectoryMeasureEvent,
    TrajectorySegment, TrajectoryShotTrace, TRAJ_V1_MARKER, TRAJ_V2_MARKER,
};
pub use transcript::{
    air_digest_from_trace, encode_proof_v1, find_marker, StarkContext, LEGACY_MARKER,
    MEASUREMENT_SPEC_HASH_PI_PREFIX, SECURITY_LEVEL_PI_PREFIX, V1_MARKER, V2_MARKER,
};

use transcript::verify_public_input_binding;

/// Reports whether a proof binds unitary v2 and trajectory marginals via `unitary_link_digest`.
pub fn proof_has_trajectory_unitary_link(proof: &[u8]) -> bool {
    trajectory::peek_trajectory_unitary_link_digest(aggregation::trajectory_proof_view(proof))
        .is_some()
}

/// Reports whether a proof binds unitary v2 and Born tails via `terminal_statevector_digest`.
pub fn proof_has_unitary_statevector_link(proof: &[u8]) -> bool {
    distribution::split_distribution_tail(born_proof_view(proof))
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
    append_born_stark_tail, append_trajectory_stark_tail, build_encoded_leaf_pcs_bundle_from_child,
    decode_leaf_pcs_bundle_bytes, generate_born_stark_proof, generate_trajectory_stark_bundle,
    has_born_stark_tail, has_trajectory_shot_sampling_stark, has_trajectory_stark_tail,
    segment_supports_born_zk, segment_supports_trajectory_zk, verify_born_stark_proof,
    verify_leaf_pcs_bundle, verify_trajectory_stark_bundle, BornStarkContext,
    BORN_STARK_TAIL_MARKER, BORN_ZK_MAX_OUTCOMES, BORN_ZK_MAX_QUBITS, TRAJ_MARGINAL_ZK_MAX_QUBITS,
    TRAJ_SHOT_STARK_INNER_MARKER, TRAJ_STARK_TAIL_MARKER,
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

    #[cfg(feature = "plonky3-stark")]
    if aggregation::is_unitary_trajectory_leaf_compose(proof) {
        return aggregation::verify_unitary_trajectory_leaf_compose(context, proof);
    }
    #[cfg(feature = "plonky3-stark")]
    if aggregation::is_unitary_born_leaf_compose(proof) {
        return aggregation::verify_unitary_born_leaf_compose(context, proof);
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

    if let Some((_, Some((dist_payload, marker)))) =
        crate::distribution::split_distribution_tail(proof)
    {
        if crate::distribution::decode_and_verify_distribution_tail(dist_payload, marker).is_none()
        {
            eprintln!("[STARK Core] Failed: invalid distribution tail");
            return false;
        }
    }

    if crate::trajectory::has_trajectory_tail(proof) {
        let Some((_, Some((payload, marker)))) = crate::trajectory::split_trajectory_tail(proof)
        else {
            eprintln!("[STARK Core] Failed: malformed trajectory tail");
            return false;
        };
        if crate::trajectory::decode_and_verify_trajectory_tail(payload, marker).is_none() {
            eprintln!("[STARK Core] Failed: invalid trajectory tail");
            return false;
        }
    }

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
            measurement_spec_hash: "",
            security_level: "",
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

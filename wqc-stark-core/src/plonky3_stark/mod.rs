//! Phase 3: Plonky3 `p3-uni-stark` prover and verifier (Mersenne31 Circle STARK).

#[cfg(feature = "plonky3-stark")]
mod aggregation;
#[cfg(feature = "plonky3-stark")]
mod aggregation_air;
mod config;
#[cfg(feature = "plonky3-stark")]
mod distribution_air;
#[cfg(feature = "plonky3-stark")]
mod distribution_stark;
mod quantum_air;
#[cfg(feature = "plonky3-stark")]
pub mod recursion;
#[cfg(feature = "plonky3-stark")]
mod shot_sampling_air;
#[cfg(feature = "plonky3-stark")]
mod shot_sampling_stark;
#[cfg(feature = "plonky3-stark")]
mod streaming_distribution;
#[cfg(feature = "plonky3-stark")]
mod trajectory_stark;
#[cfg(feature = "plonky3-stark")]
mod transcript_born;
#[cfg(feature = "plonky3-stark")]
mod transcript_trajectory_stark;
mod transcript_v2;
#[cfg(feature = "plonky3-stark")]
mod transcript_v4;

#[cfg(feature = "plonky3-stark")]
pub use aggregation::{generate_aggregation_proof, verify_aggregation_proof, AggregationContext};
pub use config::devnet_circle_config;
pub use config::{
    circle_config_for_security_level, devnet_circle_config_with_queries,
    fri_num_queries_for_security_level, keccak_circle_config, keccak_circle_config_with_queries,
    DEVNET_FRI_NUM_QUERIES, FRI_NUM_QUERIES_HIGH, FRI_NUM_QUERIES_LOW, FRI_NUM_QUERIES_NORMAL,
    FRI_NUM_QUERIES_ULTRA,
};
#[cfg(feature = "plonky3-stark")]
pub use distribution_stark::{
    generate_born_stark_proof, segment_supports_born_recursion_zk, segment_supports_born_zk,
    verify_born_stark_proof, BornStarkContext, BORN_ZK_MAX_OUTCOMES, BORN_ZK_MAX_QUBITS,
};
pub use quantum_air::QuantumExecutionAir;
#[cfg(feature = "plonky3-stark")]
pub use recursion::{
    append_rec_tail, build_agg_pcs_certificate, build_encoded_leaf_pcs_bundle_from_child,
    build_leaf_pcs_bundle_from_child, child_aggregation_transcript, child_stark_binding,
    decode_leaf_pcs_bundle_bytes, encode_leaf_pcs_bundle_bytes,
    generate_recursive_aggregation_proof, has_rec_tail, leaf_bundle_stark_sizes,
    parse_agg_v4_header, parse_agg_v4_header_any, parse_rec_agg_sides_v6, split_rec_tail,
    verify_agg_pcs_certificate, verify_leaf_pcs_bundle, verify_recursive_aggregation_proof,
    AggPcsCertificate, LeafPcsBundle, RecAggSidesV6, RecursiveAggregationContext, REC_KIND_AGG,
    REC_KIND_LEAF,
};
#[cfg(feature = "plonky3-stark")]
pub use trajectory_stark::{
    generate_trajectory_stark_bundle, segment_supports_trajectory_zk,
    verify_trajectory_stark_bundle, TRAJ_MARGINAL_ZK_MAX_QUBITS,
};
#[cfg(feature = "plonky3-stark")]
pub use transcript_born::{
    append_born_stark_tail, has_born_stark_tail, split_born_stark_tail, BORN_STARK_TAIL_MARKER,
};
#[cfg(feature = "plonky3-stark")]
pub use transcript_trajectory_stark::{
    append_trajectory_stark_tail, has_trajectory_shot_sampling_stark, has_trajectory_stark_tail,
    split_trajectory_stark_tail, TRAJ_SHOT_STARK_INNER_MARKER, TRAJ_STARK_TAIL_MARKER,
};
pub use transcript_v2::{decode_proof_v2_owned, decode_proof_v2_plonky3_bytes, encode_proof_v2};
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
        return Err("execution trace does not satisfy AIR constraints (air_sum != 0)".to_string());
    }

    let matrix = pad_air_matrix_for_uni_stark(matrix);

    let config = circle_config_for_security_level(context.security_level, 1);
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

    let expected_sv_digest = crate::distribution::split_distribution_tail(proof)
        .and_then(|(_, tail)| tail)
        .and_then(|(payload, marker)| {
            crate::distribution::decode_and_verify_distribution_tail(payload, marker)
        })
        .and_then(|seg| seg.born_binding)
        .filter(|b| !b.terminal_statevector_digest.is_empty())
        .map(|b| b.terminal_statevector_digest.clone())
        .or_else(|| crate::trajectory::peek_trajectory_unitary_link_digest(proof))
        .or_else(|| {
            if context.terminal_statevector_digest.is_empty() {
                None
            } else {
                Some(context.terminal_statevector_digest.to_string())
            }
        });

    // Prefer the transcript-bound hash (via leaf parse) so legacy proofs without PI promotion
    // are not forced to expect a measurement_spec_hash that only exists on the segment.
    let base_for_parse = crate::distribution::base_proof_without_distribution_tail(proof);
    let parsed_binding = crate::aggregation::parse_leaf_binding(base_for_parse);
    let parsed_msh = parsed_binding
        .as_ref()
        .map(|p| p.measurement_spec_hash.as_str())
        .unwrap_or("");
    if !context.measurement_spec_hash.is_empty()
        && !parsed_msh.is_empty()
        && context.measurement_spec_hash != parsed_msh
    {
        eprintln!(
            "[STARK Core] Failed: measurement_spec_hash mismatch (context '{}', proof '{}')",
            context.measurement_spec_hash, parsed_msh
        );
        return false;
    }
    // Prefer orchestrator expectation when provided; otherwise restore from PI binding.
    let expected_msh = if !context.measurement_spec_hash.is_empty() {
        Some(context.measurement_spec_hash.to_string())
    } else if !parsed_msh.is_empty() {
        Some(parsed_msh.to_string())
    } else {
        None
    };
    let parsed_sec = parsed_binding
        .as_ref()
        .map(|p| p.security_level.as_str())
        .unwrap_or("");
    if !context.security_level.is_empty()
        && !parsed_sec.is_empty()
        && context.security_level != parsed_sec
    {
        eprintln!(
            "[STARK Core] Failed: security_level mismatch (context '{}', proof '{}')",
            context.security_level, parsed_sec
        );
        return false;
    }
    // Prefer orchestrator/SubTask level when provided; otherwise restore from PI binding.
    let expected_sec = if !context.security_level.is_empty() {
        Some(context.security_level.to_string())
    } else if !parsed_sec.is_empty() {
        Some(parsed_sec.to_string())
    } else {
        None
    };

    let verify_ctx = StarkContext {
        circuit_id: context.circuit_id,
        sub_task_id: context.sub_task_id,
        node_id: context.node_id,
        slice_id: context.slice_id,
        output_hash: context.output_hash,
        terminal_statevector_digest: expected_sv_digest.as_deref().unwrap_or(""),
        measurement_spec_hash: expected_msh.as_deref().unwrap_or(""),
        security_level: expected_sec.as_deref().unwrap_or(""),
    };

    let base = crate::distribution::base_proof_without_distribution_tail(proof);
    let plonky3_bytes = match decode_proof_v2_plonky3_bytes(base, &verify_ctx) {
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

    let config = circle_config_for_security_level(verify_ctx.security_level, 1);
    let air = QuantumExecutionAir;
    if let Err(e) = verify(&config, &air, &p3_proof, &[]) {
        eprintln!("[STARK Core] Failed: Plonky3 verify error: {e:?}");
        return false;
    }

    let mut verified_distribution = false;
    let mut verified_born_zk = false;
    if let Some((_, Some((dist_payload, marker)))) =
        crate::distribution::split_distribution_tail(proof)
    {
        let segment =
            match crate::distribution::decode_and_verify_distribution_tail(dist_payload, marker) {
                Some(seg) => seg,
                None => {
                    eprintln!("[STARK Core] Failed: invalid distribution tail");
                    return false;
                }
            };

        if let Some(binding) = &segment.born_binding {
            if !binding.terminal_statevector_digest.is_empty() {
                let recomputed = crate::distribution::calculate_terminal_statevector_digest(
                    &binding.terminal_statevector,
                );
                if recomputed != binding.terminal_statevector_digest {
                    eprintln!(
                        "[STARK Core] Failed: terminal_statevector_digest mismatch in segment"
                    );
                    return false;
                }
            }
        }

        if segment_supports_born_zk(&segment) {
            let Some(born_bytes) = split_born_stark_tail(proof) else {
                eprintln!("[STARK Core] Failed: Born zk STARK tail missing");
                return false;
            };
            let sv_digest = segment
                .born_binding
                .as_ref()
                .map(|b| b.terminal_statevector_digest.as_str())
                .unwrap_or("");
            let born_ctx = BornStarkContext {
                sub_task_id: context.sub_task_id,
                probability_digest: &segment.probability_digest,
                terminal_statevector_digest: sv_digest,
                security_level: context.security_level,
            };
            if !verify_born_stark_proof(&born_ctx, &segment, born_bytes) {
                eprintln!("[STARK Core] Failed: Born zk STARK verification failed");
                return false;
            }
            verified_born_zk = true;
        }
        verified_distribution = true;
    }

    let verified_trajectory = if crate::trajectory::has_trajectory_tail(proof) {
        let Some((_, Some((payload, marker)))) = crate::trajectory::split_trajectory_tail(proof)
        else {
            eprintln!("[STARK Core] Failed: malformed trajectory tail");
            return false;
        };
        let segment = match crate::trajectory::decode_and_verify_trajectory_tail(payload, marker) {
            Some(seg) => seg,
            None => {
                eprintln!("[STARK Core] Failed: invalid trajectory tail");
                return false;
            }
        };

        if segment_supports_trajectory_zk(&segment) {
            let Some(bundle) = split_trajectory_stark_tail(proof) else {
                eprintln!("[STARK Core] Failed: trajectory zk STARK tail missing");
                return false;
            };
            if !verify_trajectory_stark_bundle(
                context.sub_task_id,
                &segment,
                bundle,
                context.security_level,
            ) {
                eprintln!("[STARK Core] Failed: trajectory zk STARK verification failed");
                return false;
            }
        }
        true
    } else {
        false
    };

    if verified_trajectory {
        if verified_born_zk {
            eprintln!(
                "[STARK Core] Verification success (v2 Plonky3 STARK + distribution + Born zk + trajectory tail)"
            );
        } else if verified_distribution {
            eprintln!(
                "[STARK Core] Verification success (v2 Plonky3 STARK + distribution + trajectory tail)"
            );
        } else {
            eprintln!("[STARK Core] Verification success (v2 Plonky3 STARK + trajectory tail)");
        }
        return true;
    }

    if verified_born_zk {
        eprintln!(
            "[STARK Core] Verification success (v2 Plonky3 STARK + distribution + Born zk + unitary link)"
        );
        return true;
    }

    if verified_distribution {
        eprintln!("[STARK Core] Verification success (v2 Plonky3 STARK + distribution tail)");
        return true;
    }

    eprintln!("[STARK Core] Verification success (v2 Plonky3 STARK)");
    true
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
            terminal_statevector_digest: "",
            measurement_spec_hash: "",
            security_level: "",
        }
    }

    #[test]
    fn empty_circuit_v2_roundtrip() {
        let ctx = context();
        let trace = crate::trace_spec::idle_qubit0_trace();
        let proof = generate_plonky3_proof(&ctx, &trace).expect("prove");
        assert!(verify_plonky3_proof(&ctx, &proof));
    }

    #[test]
    fn security_level_low_selects_fewer_fri_queries() {
        let ctx = StarkContext {
            security_level: "low",
            ..context()
        };
        assert_eq!(fri_num_queries_for_security_level(ctx.security_level), 8);
        let trace = crate::trace_spec::idle_qubit0_trace();
        let proof = generate_plonky3_proof(&ctx, &trace).expect("prove");
        assert!(verify_plonky3_proof(&ctx, &proof));
        // Orch-style verify with matching level from SubTask.
        assert!(verify_plonky3_proof(
            &StarkContext {
                security_level: "low",
                ..context()
            },
            &proof
        ));
        // Wrong ladder must fail.
        assert!(!verify_plonky3_proof(
            &StarkContext {
                security_level: "ultra",
                ..context()
            },
            &proof
        ));
    }

    #[test]
    fn honest_h_trace_v2_roundtrip() {
        let ctx = context();
        let trace = crate::trace_spec::golden_h_q0_trace();
        let proof = generate_plonky3_proof(&ctx, &trace).expect("prove");
        assert!(verify_plonky3_proof(&ctx, &proof));
    }

    #[test]
    fn v2_with_born_zk_tail_roundtrip() {
        let ctx = context();
        let trace = crate::trace_spec::golden_h_q0_trace();
        let inv_sqrt2 = 1.0f64 / 2.0f64.sqrt();
        let sv = vec![(inv_sqrt2, 0.0), (inv_sqrt2, 0.0)];
        let binding =
            crate::distribution::BornBinding::from_specs(1, 1, &[(0, 0)], sv).expect("bind");
        let probs = vec![("0".into(), 0.5), ("1".into(), 0.5)];
        let segment = crate::distribution::DistributionSegment {
            sample_seed: 7,
            shots: 128,
            measurement_spec_hash: "spec".into(),
            probability_digest: crate::distribution::calculate_probability_digest(&probs),
            probabilities: probs,
            born_binding: Some(binding),
        };
        let sv_digest = segment
            .born_binding
            .as_ref()
            .map(|b| b.terminal_statevector_digest.as_str())
            .unwrap_or("");
        let linked_ctx = StarkContext {
            terminal_statevector_digest: sv_digest,
            ..ctx
        };
        let mut proof = generate_plonky3_proof(&linked_ctx, &trace).expect("prove");
        proof = crate::distribution::append_distribution_tail(proof, &segment);
        if segment_supports_born_zk(&segment) {
            let born_ctx = BornStarkContext {
                sub_task_id: ctx.sub_task_id,
                probability_digest: &segment.probability_digest,
                terminal_statevector_digest: sv_digest,
                security_level: "",
            };
            let born = generate_born_stark_proof(&born_ctx, &segment).expect("born prove");
            proof = append_born_stark_tail(proof, &born);
        }
        assert!(verify_plonky3_proof(&ctx, &proof));
    }

    #[test]
    fn v2_born_zk_rejects_unlinked_unitary() {
        let ctx = context();
        let trace = crate::trace_spec::golden_h_q0_trace();
        let inv_sqrt2 = 1.0f64 / 2.0f64.sqrt();
        let sv = vec![(inv_sqrt2, 0.0), (inv_sqrt2, 0.0)];
        let binding =
            crate::distribution::BornBinding::from_specs(1, 1, &[(0, 0)], sv).expect("bind");
        let probs = vec![("0".into(), 0.5), ("1".into(), 0.5)];
        let segment = crate::distribution::DistributionSegment {
            sample_seed: 7,
            shots: 128,
            measurement_spec_hash: "spec".into(),
            probability_digest: crate::distribution::calculate_probability_digest(&probs),
            probabilities: probs,
            born_binding: Some(binding),
        };
        let sv_digest = segment
            .born_binding
            .as_ref()
            .map(|b| b.terminal_statevector_digest.as_str())
            .unwrap_or("");
        let mut proof = generate_plonky3_proof(&ctx, &trace).expect("prove without link");
        proof = crate::distribution::append_distribution_tail(proof, &segment);
        let born_ctx = BornStarkContext {
            sub_task_id: ctx.sub_task_id,
            probability_digest: &segment.probability_digest,
            terminal_statevector_digest: sv_digest,
            security_level: "",
        };
        let born = generate_born_stark_proof(&born_ctx, &segment).expect("born prove");
        proof = append_born_stark_tail(proof, &born);
        assert!(!verify_plonky3_proof(&ctx, &proof));
    }
}

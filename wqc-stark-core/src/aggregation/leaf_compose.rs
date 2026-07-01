//! C2c leaf-level v3 compose: unitary `QuantumExecutionAir` + trajectory marginal STARKs.
//!
//! Mid-circuit `sample_counts` proofs pair:
//! - **Left child**: v2 Plonky3 unitary transcript (`terminal_statevector_digest` = first MEASURE pre-state)
//! - **Right child**: trajectory segment + marginal zk bundle (`_M31_TRAJ_LEAF_V1_`)
//!
//! An R2 `AggregationAir` tail binds the two child SHA3-256 digests.

use crate::aggregation::leaf::{parse_leaf_binding, parsed_to_stark_context};
use crate::aggregation::transcript_v3::{child_digest, decode_compose_v3, decode_compose_v3_slices, is_compose_v3};
use crate::aggregation::{compose_stark_proofs, ComposeContext};
use crate::trajectory::{append_trajectory_tail, decode_and_verify_trajectory_tail, split_trajectory_tail, TrajectorySegment};
use crate::transcript::StarkContext;

#[cfg(feature = "plonky3-stark")]
use crate::plonky3_stark::{
    append_trajectory_stark_tail, has_trajectory_stark_tail, segment_supports_trajectory_zk,
    split_trajectory_stark_tail, verify_plonky3_proof, verify_trajectory_stark_bundle,
};
#[cfg(feature = "plonky3-stark")]
use crate::plonky3_stark::split_agg_tail;

/// v3 compose label for a mid-circuit unitary + trajectory leaf pair.
pub const UNITARY_TRAJ_COMPOSE_LABEL: &str = "leaf:unitary_traj";

/// Marker prefix on the trajectory-only child transcript.
pub const TRAJ_LEAF_MARKER: &[u8] = b"_M31_TRAJ_LEAF_V1_";

pub fn compose_v3_body(proof: &[u8]) -> &[u8] {
    #[cfg(feature = "plonky3-stark")]
    {
        if let Some((v3, _)) = split_agg_tail(proof) {
            return v3;
        }
    }
    proof
}

/// Returns true when `proof` is a v3 compose node with label `leaf:unitary_traj`.
pub fn is_unitary_trajectory_leaf_compose(proof: &[u8]) -> bool {
    if !is_compose_v3(proof) {
        return false;
    }
    let v3 = compose_v3_body(proof);
    decode_compose_v3(v3)
        .is_some_and(|(header, _, _)| header.compose_label == UNITARY_TRAJ_COMPOSE_LABEL)
}

/// Extracts the trajectory child bytes from a composed leaf, if present.
pub fn trajectory_child_from_compose(proof: &[u8]) -> Option<&[u8]> {
    if !is_unitary_trajectory_leaf_compose(proof) {
        return None;
    }
    let v3 = compose_v3_body(proof);
    let (header, _, right) = decode_compose_v3_slices(v3)?;
    if header.compose_label != UNITARY_TRAJ_COMPOSE_LABEL {
        return None;
    }
    Some(right)
}

/// Resolves the proof slice that carries trajectory segment / zk tails.
pub fn trajectory_proof_view<'a>(proof: &'a [u8]) -> &'a [u8] {
    trajectory_child_from_compose(proof).unwrap_or(proof)
}

/// Encodes a trajectory-only leaf child (segment + optional marginal zk bundle).
pub fn encode_trajectory_leaf(
    sub_task_id: &str,
    segment: &TrajectorySegment,
    bundle: Option<&[u8]>,
) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(sub_task_id.as_bytes());
    out.push(0);
    out.extend_from_slice(TRAJ_LEAF_MARKER);
    out = append_trajectory_tail(out, segment);
    #[cfg(feature = "plonky3-stark")]
    if let Some(bundle) = bundle.filter(|b| !b.is_empty()) {
        out = append_trajectory_stark_tail(out, bundle);
    }
    #[cfg(not(feature = "plonky3-stark"))]
    let _ = bundle;
    out
}

fn parse_trajectory_leaf_prefix(proof: &[u8]) -> Option<(&str, &[u8])> {
    let marker_pos = proof
        .windows(TRAJ_LEAF_MARKER.len())
        .position(|w| w == TRAJ_LEAF_MARKER)?;
    let sub_end = marker_pos.saturating_sub(1);
    if marker_pos == 0 || proof.get(sub_end)? != &0 {
        return None;
    }
    let sub_task_id = std::str::from_utf8(&proof[..sub_end]).ok()?;
    let tail_start = marker_pos + TRAJ_LEAF_MARKER.len();
    Some((sub_task_id, proof.get(tail_start..)?))
}

pub fn is_trajectory_leaf_proof(proof: &[u8]) -> bool {
    parse_trajectory_leaf_prefix(proof).is_some()
}

/// Verifies a trajectory-only leaf child (algebraic segment + optional marginal zk bundle).
pub fn verify_trajectory_leaf(sub_task_id: &str, proof: &[u8]) -> Result<(), String> {
    let (parsed_sub, tail_body) = parse_trajectory_leaf_prefix(proof)
        .ok_or_else(|| "malformed trajectory leaf prefix".to_string())?;
    if parsed_sub != sub_task_id {
        return Err("trajectory leaf sub_task_id mismatch".to_string());
    }

    let (_, tail) = split_trajectory_tail(tail_body)
        .ok_or_else(|| "missing trajectory segment tail".to_string())?;
    let (payload, marker) = tail.ok_or_else(|| "missing trajectory segment tail".to_string())?;
    let segment = decode_and_verify_trajectory_tail(payload, marker)
        .ok_or_else(|| "invalid trajectory segment".to_string())?;

    #[cfg(feature = "plonky3-stark")]
    if has_trajectory_stark_tail(tail_body) {
        if !segment_supports_trajectory_zk(&segment) {
            return Err("trajectory zk tail without zk-capable segment".to_string());
        }
        let bundle = split_trajectory_stark_tail(tail_body)
            .ok_or_else(|| "malformed trajectory zk tail".to_string())?;
        if !verify_trajectory_stark_bundle(sub_task_id, &segment, bundle) {
            return Err("trajectory marginal zk verification failed".to_string());
        }
    }

    Ok(())
}

/// Pairs a verified unitary v2 proof with a trajectory leaf into a v3 compose transcript + agg tail.
#[cfg(feature = "plonky3-stark")]
pub fn compose_unitary_trajectory_leaf(
    context: &StarkContext<'_>,
    unitary_v2_proof: &[u8],
    segment: &TrajectorySegment,
    traj_bundle: &[u8],
) -> Result<Vec<u8>, String> {
    if context.sub_task_id.is_empty() {
        return Err("sub_task_id is required".to_string());
    }
    if segment.unitary_link_digest.is_empty() {
        return Err("unitary_link_digest is required for unitary+trajectory compose".to_string());
    }
    if !segment_supports_trajectory_zk(segment) {
        return Err("trajectory segment does not support marginal zk".to_string());
    }
    if crate::trajectory::has_trajectory_tail(unitary_v2_proof)
        || crate::distribution::split_distribution_tail(unitary_v2_proof)
            .and_then(|(_, tail)| tail)
            .is_some()
    {
        return Err("unitary child must not include auxiliary tails".to_string());
    }

    let unitary_ctx = StarkContext {
        circuit_id: context.circuit_id,
        sub_task_id: context.sub_task_id,
        node_id: context.node_id,
        slice_id: context.slice_id,
        output_hash: context.output_hash,
        terminal_statevector_digest: &segment.unitary_link_digest,
    };

    if !verify_plonky3_proof(&unitary_ctx, unitary_v2_proof) {
        return Err("unitary child Plonky3 verification failed".to_string());
    }

    let parsed = parse_leaf_binding(unitary_v2_proof)
        .ok_or_else(|| "cannot parse unitary child public inputs".to_string())?;
    if parsed.terminal_statevector_digest != segment.unitary_link_digest {
        return Err("unitary_link_digest mismatch between unitary child and trajectory segment".to_string());
    }

    let traj_child = encode_trajectory_leaf(context.sub_task_id, segment, Some(traj_bundle));
    verify_trajectory_leaf(context.sub_task_id, &traj_child)?;

    compose_stark_proofs(
        &ComposeContext {
            parent_task_id: context.sub_task_id,
            compose_label: UNITARY_TRAJ_COMPOSE_LABEL,
            manifest_root_hash: "",
        },
        unitary_v2_proof,
        &traj_child,
        Some(&unitary_ctx),
        None,
    )
}

/// Verifies a `leaf:unitary_traj` v3 compose transcript (unitary + trajectory children + agg tail).
#[cfg(feature = "plonky3-stark")]
pub fn verify_unitary_trajectory_leaf_compose(
    context: &StarkContext<'_>,
    proof: &[u8],
) -> bool {
    if !is_unitary_trajectory_leaf_compose(proof) {
        eprintln!("[LeafCompose] Failed: not a unitary+trajectory compose proof");
        return false;
    }

    let v3 = compose_v3_body(proof);
    let (header, left_child, right_child) = match decode_compose_v3_slices(v3) {
        Some(parts) => parts,
        None => {
            eprintln!("[LeafCompose] Failed: malformed v3 compose body");
            return false;
        }
    };

    if header.parent_task_id != context.sub_task_id {
        eprintln!("[LeafCompose] Failed: parent_task_id mismatch");
        return false;
    }
    if header.compose_label != UNITARY_TRAJ_COMPOSE_LABEL {
        eprintln!("[LeafCompose] Failed: unexpected compose label");
        return false;
    }
    if child_digest(left_child) != header.left_child_hash
        || child_digest(right_child) != header.right_child_hash
    {
        eprintln!("[LeafCompose] Failed: child digest mismatch");
        return false;
    }

    let parsed = match parse_leaf_binding(left_child) {
        Some(p) => p,
        None => {
            eprintln!("[LeafCompose] Failed: cannot parse unitary child");
            return false;
        }
    };
    if parsed.sub_task_id != context.sub_task_id
        || parsed.circuit_id != context.circuit_id
        || parsed.node_id != context.node_id
        || parsed.slice_id != context.slice_id
        || parsed.output_hash != context.output_hash
    {
        eprintln!("[LeafCompose] Failed: unitary child public input mismatch");
        return false;
    }

    let unitary_ctx = parsed_to_stark_context(&parsed);
    if !verify_plonky3_proof(&unitary_ctx, left_child) {
        eprintln!("[LeafCompose] Failed: unitary child verification failed");
        return false;
    }

    if let Err(err) = verify_trajectory_leaf(context.sub_task_id, right_child) {
        eprintln!("[LeafCompose] Failed: trajectory child: {err}");
        return false;
    }

    let tail_body = parse_trajectory_leaf_prefix(right_child)
        .map(|(_, tail)| tail)
        .unwrap_or(right_child);
    let (_, tail) = match split_trajectory_tail(tail_body) {
        Some(parts) => parts,
        None => {
            eprintln!("[LeafCompose] Failed: trajectory segment missing");
            return false;
        }
    };
    let (payload, marker) = match tail {
        Some(parts) => parts,
        None => {
            eprintln!("[LeafCompose] Failed: trajectory segment missing");
            return false;
        }
    };
    let segment = match decode_and_verify_trajectory_tail(payload, marker) {
        Some(seg) => seg,
        None => {
            eprintln!("[LeafCompose] Failed: invalid trajectory segment");
            return false;
        }
    };

    if !segment.unitary_link_digest.is_empty()
        && parsed.terminal_statevector_digest != segment.unitary_link_digest
    {
        eprintln!("[LeafCompose] Failed: unitary↔trajectory link digest mismatch");
        return false;
    }

    if let Some(agg_bytes) = split_agg_tail(proof).map(|(_, agg)| agg) {
        let agg_ctx = crate::plonky3_stark::AggregationContext {
            parent_task_id: context.sub_task_id,
            compose_label: UNITARY_TRAJ_COMPOSE_LABEL,
            manifest_root_hash: "",
            left_child_hash: header.left_child_hash,
            right_child_hash: header.right_child_hash,
        };
        if !crate::plonky3_stark::verify_aggregation_proof(&agg_ctx, agg_bytes) {
            eprintln!("[LeafCompose] Failed: aggregation STARK verification failed");
            return false;
        }
    }

    eprintln!(
        "[LeafCompose] Verification success (unitary+trajectory v3 compose, link={})",
        segment.unitary_link_digest
    );
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::trajectory::{TrajectoryMeasureEvent, TrajectoryShotTrace};

    fn sample_segment() -> TrajectorySegment {
        let inv_sqrt2 = 1.0f64 / 2.0f64.sqrt();
        let pre_first_raw = vec![(inv_sqrt2, 0.0), (0.0, 0.0), (inv_sqrt2, 0.0), (0.0, 0.0)];
        let pre_second_raw = vec![(0.0, 0.0), (0.0, 0.0), (1.0, 0.0), (0.0, 0.0)];
        let pre_first = crate::distribution::canonicalize_terminal_statevector(&pre_first_raw);
        let pre_second = crate::distribution::canonicalize_terminal_statevector(&pre_second_raw);
        let d0 = crate::distribution::calculate_terminal_statevector_digest(&pre_first);
        let d2 = crate::distribution::calculate_terminal_statevector_digest(&pre_second);
        let (p0, p1) = crate::air::trajectory::z_marginal_from_statevector(&pre_first, 0, 2).unwrap();
        let (p0b, p1b) = crate::air::trajectory::z_marginal_from_statevector(&pre_second, 1, 2).unwrap();
        let witnesses = vec![
            crate::trajectory::TrajectoryMarginalWitness {
                qubit: 0,
                reference_p0: p0,
                reference_p1: p1,
                pre_measure_statevector: pre_first.clone(),
                pre_measure_statevector_digest: d0.clone(),
            },
            crate::trajectory::TrajectoryMarginalWitness {
                qubit: 1,
                reference_p0: p0b,
                reference_p1: p1b,
                pre_measure_statevector: pre_second.clone(),
                pre_measure_statevector_digest: d2.clone(),
            },
        ];
        let traces = vec![TrajectoryShotTrace {
            shot_index: 0,
            shot_seed: 7,
            final_outcome: "01".into(),
            classical_bits: vec![1, 0],
            measures: vec![
                TrajectoryMeasureEvent {
                    gate_index: 1,
                    qubit: 0,
                    cbit: 0,
                    p0: p0,
                    p1: p1,
                    outcome: 1,
                    pre_measure_statevector_digest: d0.clone(),
                },
                TrajectoryMeasureEvent {
                    gate_index: 3,
                    qubit: 1,
                    cbit: 1,
                    p0: p0b,
                    p1: p1b,
                    outcome: 1,
                    pre_measure_statevector_digest: d2.clone(),
                },
            ],
        }];
        TrajectorySegment {
            sample_seed: 7,
            shots: 1,
            measurement_spec_hash: "spec".into(),
            trajectory_digest: crate::trajectory::calculate_trajectory_digest(&traces),
            qubit_count: 2,
            unitary_link_digest: d0,
            traces,
            marginal_witnesses: witnesses,
        }
    }

    #[test]
    fn trajectory_leaf_roundtrip_prefix() {
        let segment = sample_segment();
        let leaf = encode_trajectory_leaf("sub-traj", &segment, None);
        assert!(is_trajectory_leaf_proof(&leaf));
        verify_trajectory_leaf("sub-traj", &leaf).expect("verify leaf");
        assert!(trajectory_proof_view(&leaf).windows(TRAJ_LEAF_MARKER.len()).any(|w| w == TRAJ_LEAF_MARKER));
    }

    #[cfg(feature = "plonky3-stark")]
    #[test]
    fn unitary_trajectory_compose_roundtrip() {
        use crate::generate_plonky3_stark_proof;
        use crate::plonky3_stark::generate_trajectory_stark_bundle;

        let segment = sample_segment();
        let ctx = StarkContext {
            circuit_id: "circuit-if",
            sub_task_id: "sub-traj",
            node_id: "node-1",
            slice_id: "0",
            output_hash: "counts-hash",
            terminal_statevector_digest: &segment.unitary_link_digest,
        };
        let trace = crate::trace_spec::golden_h_q0_trace();
        let unitary = generate_plonky3_stark_proof(&ctx, &trace).expect("unitary prove");
        let bundle = generate_trajectory_stark_bundle("sub-traj", &segment).expect("traj zk");
        let composed =
            compose_unitary_trajectory_leaf(&ctx, &unitary, &segment, &bundle).expect("compose");
        assert!(is_unitary_trajectory_leaf_compose(&composed));
        assert!(verify_unitary_trajectory_leaf_compose(&ctx, &composed));
        assert!(trajectory_child_from_compose(&composed).is_some());
    }
}

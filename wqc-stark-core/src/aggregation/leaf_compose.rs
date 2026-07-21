//! C2c leaf-level v3 compose: unitary `QuantumExecutionAir` + trajectory marginal STARKs.
//!
//! Mid-circuit `sample_counts` proofs pair:
//! - **Left child**: v2 Plonky3 unitary transcript (`terminal_statevector_digest` = first MEASURE pre-state)
//! - **Right child**: trajectory segment + marginal zk bundle (`_M31_TRAJ_LEAF_V1_`)
//!
//! An R3-M1 `RecursiveAggregationAir` tail (legacy R2 `AggregationAir` still accepted) binds
//! child digests and verified child STARK digests.

use crate::aggregation::leaf::{parse_leaf_binding, parsed_to_stark_context};
use crate::aggregation::transcript_v3::{
    child_digest, decode_compose_v3, decode_compose_v3_slices, is_compose_v3,
};
use crate::aggregation::{compose_stark_proofs, ComposeContext};
use crate::trajectory::{
    append_trajectory_tail, decode_and_verify_trajectory_tail, split_trajectory_tail,
    TrajectorySegment,
};
use crate::transcript::StarkContext;

#[cfg(feature = "plonky3-stark")]
use crate::aggregation::recursive_context_for_children;
use crate::plonky3_stark::{
    append_trajectory_stark_tail, has_trajectory_stark_tail, segment_supports_trajectory_zk,
    split_agg_tail, split_rec_tail, split_trajectory_stark_tail, verify_aggregation_proof,
    verify_plonky3_proof, verify_recursive_aggregation_proof, verify_trajectory_stark_bundle,
    AggregationContext,
};

/// v3 compose label for a mid-circuit unitary + trajectory leaf pair.
pub const UNITARY_TRAJ_COMPOSE_LABEL: &str = "leaf:unitary_traj";

/// Marker prefix on the trajectory-only child transcript.
pub const TRAJ_LEAF_MARKER: &[u8] = b"_M31_TRAJ_LEAF_V1_";

pub(crate) fn compose_v3_body(proof: &[u8]) -> &[u8] {
    #[cfg(feature = "plonky3-stark")]
    {
        let body = split_rec_tail(proof).map(|(b, _)| b).unwrap_or(proof);
        if let Some((v3, _)) = split_agg_tail(body) {
            return v3;
        }
        body
    }
    #[cfg(not(feature = "plonky3-stark"))]
    {
        proof
    }
}

/// Returns true when `proof` is a v3 compose node with label `leaf:unitary_traj`.
pub fn is_unitary_trajectory_leaf_compose(proof: &[u8]) -> bool {
    let v3 = compose_v3_body(proof);
    if !is_compose_v3(v3) {
        return false;
    }
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
pub fn trajectory_proof_view(proof: &[u8]) -> &[u8] {
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

pub(crate) fn parse_trajectory_leaf_prefix(proof: &[u8]) -> Option<(&str, &[u8])> {
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
        measurement_spec_hash: context.measurement_spec_hash,
    };

    if !verify_plonky3_proof(&unitary_ctx, unitary_v2_proof) {
        return Err("unitary child Plonky3 verification failed".to_string());
    }

    let parsed = parse_leaf_binding(unitary_v2_proof)
        .ok_or_else(|| "cannot parse unitary child public inputs".to_string())?;
    if parsed.terminal_statevector_digest != segment.unitary_link_digest {
        return Err(
            "unitary_link_digest mismatch between unitary child and trajectory segment".to_string(),
        );
    }
    if !context.measurement_spec_hash.is_empty()
        && parsed.measurement_spec_hash != context.measurement_spec_hash
    {
        return Err(
            "measurement_spec_hash mismatch between unitary child and StarkContext".to_string(),
        );
    }
    if !parsed.measurement_spec_hash.is_empty()
        && !segment.measurement_spec_hash.is_empty()
        && parsed.measurement_spec_hash != segment.measurement_spec_hash
    {
        return Err(
            "measurement_spec_hash mismatch between unitary child and trajectory segment"
                .to_string(),
        );
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
pub fn verify_unitary_trajectory_leaf_compose(context: &StarkContext<'_>, proof: &[u8]) -> bool {
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
    if !context.measurement_spec_hash.is_empty()
        && parsed.measurement_spec_hash != context.measurement_spec_hash
    {
        eprintln!("[LeafCompose] Failed: measurement_spec_hash mismatch");
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
    if !parsed.measurement_spec_hash.is_empty()
        && !segment.measurement_spec_hash.is_empty()
        && parsed.measurement_spec_hash != segment.measurement_spec_hash
    {
        eprintln!("[LeafCompose] Failed: measurement_spec_hash mismatch vs trajectory segment");
        return false;
    }

    #[cfg(feature = "plonky3-stark")]
    {
        if let Some((_, rec_bytes)) = split_rec_tail(proof) {
            let rec_ctx = match recursive_context_for_children(
                context.sub_task_id,
                UNITARY_TRAJ_COMPOSE_LABEL,
                "",
                header.left_child_hash,
                header.right_child_hash,
                left_child,
                right_child,
            ) {
                Ok(ctx) => ctx,
                Err(e) => {
                    eprintln!("[LeafCompose] Failed: rec context: {e}");
                    return false;
                }
            };
            if !verify_recursive_aggregation_proof(&rec_ctx, rec_bytes) {
                eprintln!(
                    "[LeafCompose] Failed: R3-M2 recursive aggregation STARK verification failed"
                );
                return false;
            }
        }
        // Always check V4 when present (compose emits V4 + V6 together).
        let body = split_rec_tail(proof).map(|(b, _)| b).unwrap_or(proof);
        if let Some(agg_bytes) = split_agg_tail(body).map(|(_, agg)| agg) {
            let agg_ctx = AggregationContext {
                parent_task_id: context.sub_task_id,
                compose_label: UNITARY_TRAJ_COMPOSE_LABEL,
                manifest_root_hash: "",
                left_child_hash: header.left_child_hash,
                right_child_hash: header.right_child_hash,
            };
            if !verify_aggregation_proof(&agg_ctx, agg_bytes) {
                eprintln!("[LeafCompose] Failed: aggregation STARK verification failed");
                return false;
            }
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
        use rand::rngs::StdRng;
        use rand::{Rng, SeedableRng};

        let inv_sqrt2 = 1.0f64 / 2.0f64.sqrt();
        let pre_first_raw = vec![(inv_sqrt2, 0.0), (0.0, 0.0), (inv_sqrt2, 0.0), (0.0, 0.0)];
        let pre_second_raw = vec![(0.0, 0.0), (0.0, 0.0), (1.0, 0.0), (0.0, 0.0)];
        let pre_first = crate::distribution::canonicalize_terminal_statevector(&pre_first_raw);
        let pre_second = crate::distribution::canonicalize_terminal_statevector(&pre_second_raw);
        let d0 = crate::distribution::calculate_terminal_statevector_digest(&pre_first);
        let d2 = crate::distribution::calculate_terminal_statevector_digest(&pre_second);
        let (p0, p1) =
            crate::air::trajectory::z_marginal_from_statevector(&pre_first, 0, 2).unwrap();
        let (p0b, p1b) =
            crate::air::trajectory::z_marginal_from_statevector(&pre_second, 1, 2).unwrap();
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

        let mut rng = StdRng::seed_from_u64(7);
        let u0: f64 = rng.gen();
        let denom0 = (p0 + p1).max(1e-30_f64);
        let o0 = if u0 < p0 / denom0 { 0u8 } else { 1 };
        let u1: f64 = rng.gen();
        let denom1 = (p0b + p1b).max(1e-30_f64);
        let o1 = if u1 < p0b / denom1 { 0u8 } else { 1 };

        let traces = vec![TrajectoryShotTrace {
            shot_index: 0,
            shot_seed: 7,
            final_outcome: format!("{o0}{o1}"),
            classical_bits: vec![o0, o1],
            measures: vec![
                TrajectoryMeasureEvent {
                    gate_index: 1,
                    qubit: 0,
                    cbit: 0,
                    p0,
                    p1,
                    outcome: o0,
                    pre_measure_statevector_digest: d0.clone(),
                },
                TrajectoryMeasureEvent {
                    gate_index: 3,
                    qubit: 1,
                    cbit: 1,
                    p0: p0b,
                    p1: p1b,
                    outcome: o1,
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
        assert!(trajectory_proof_view(&leaf)
            .windows(TRAJ_LEAF_MARKER.len())
            .any(|w| w == TRAJ_LEAF_MARKER));
    }

    #[cfg(feature = "plonky3-stark")]
    fn if_compose_fixture() -> (StarkContext<'static>, Vec<u8>) {
        use crate::generate_plonky3_stark_proof;
        use crate::plonky3_stark::generate_trajectory_stark_bundle;

        let segment = sample_segment();
        let link_digest: &'static str =
            Box::leak(segment.unitary_link_digest.clone().into_boxed_str());
        let ctx = StarkContext {
            circuit_id: "circuit-if",
            sub_task_id: "sub-traj",
            node_id: "node-1",
            slice_id: "0",
            output_hash: "counts-hash",
            terminal_statevector_digest: link_digest,
            measurement_spec_hash: "",
        };
        let trace = crate::trace_spec::golden_h_q0_trace();
        let unitary = generate_plonky3_stark_proof(&ctx, &trace).expect("unitary prove");
        let bundle = generate_trajectory_stark_bundle("sub-traj", &segment).expect("traj zk");
        let composed =
            compose_unitary_trajectory_leaf(&ctx, &unitary, &segment, &bundle).expect("compose");
        (ctx, composed)
    }

    #[cfg(feature = "plonky3-stark")]
    fn tamper_subslice(proof: &mut [u8], needle: &[u8]) {
        let offset = proof
            .windows(needle.len())
            .position(|window| window == needle)
            .expect("needle in proof");
        proof[offset] ^= 0xFF;
    }

    #[cfg(feature = "plonky3-stark")]
    #[test]
    #[ignore = "slow; run in release CI"]
    fn unitary_trajectory_compose_roundtrip() {
        let (ctx, composed) = if_compose_fixture();
        assert!(is_unitary_trajectory_leaf_compose(&composed));
        assert!(verify_unitary_trajectory_leaf_compose(&ctx, &composed));
        assert!(trajectory_child_from_compose(&composed).is_some());
    }

    #[cfg(feature = "plonky3-stark")]
    #[test]
    fn compose_rejects_unitary_link_digest_mismatch() {
        use crate::generate_plonky3_stark_proof;
        use crate::plonky3_stark::generate_trajectory_stark_bundle;

        let segment = sample_segment();
        let link_digest = segment.unitary_link_digest.clone();
        let ctx = StarkContext {
            circuit_id: "circuit-if",
            sub_task_id: "sub-traj",
            node_id: "node-1",
            slice_id: "0",
            output_hash: "counts-hash",
            terminal_statevector_digest: &link_digest,
            measurement_spec_hash: "",
        };
        let trace = crate::trace_spec::golden_h_q0_trace();
        let unitary = generate_plonky3_stark_proof(&ctx, &trace).expect("unitary prove");
        let bundle = generate_trajectory_stark_bundle("sub-traj", &segment).expect("traj zk");

        let mut bad_segment = segment;
        bad_segment.unitary_link_digest = "00".repeat(32);
        let err = compose_unitary_trajectory_leaf(&ctx, &unitary, &bad_segment, &bundle)
            .expect_err("tampered link digest");
        assert!(
            err.contains("unitary_link_digest mismatch")
                || err.contains("unitary child Plonky3 verification failed"),
            "unexpected error: {err}"
        );
    }

    #[cfg(feature = "plonky3-stark")]
    #[test]
    fn composed_proof_rejects_tampered_children_and_agg_tail() {
        use crate::aggregation::transcript_v3::decode_compose_v3_slices;
        use crate::plonky3_stark::{split_agg_tail, split_rec_tail};

        let (ctx, mut composed) = if_compose_fixture();
        assert!(verify_unitary_trajectory_leaf_compose(&ctx, &composed));

        let v3 = compose_v3_body(&composed);
        let (_, left_child, right_child) = decode_compose_v3_slices(v3).expect("decode");

        let mut bad_left = composed.clone();
        tamper_subslice(&mut bad_left, left_child);
        assert!(!verify_unitary_trajectory_leaf_compose(&ctx, &bad_left));

        let mut bad_right = composed.clone();
        tamper_subslice(&mut bad_right, right_child);
        assert!(!verify_unitary_trajectory_leaf_compose(&ctx, &bad_right));

        if let Some((_, rec)) = split_rec_tail(&composed) {
            let mut bad_rec = composed.clone();
            tamper_subslice(&mut bad_rec, rec);
            assert!(!verify_unitary_trajectory_leaf_compose(&ctx, &bad_rec));
        } else if let Some((_, agg)) = split_agg_tail(&composed) {
            let mut bad_agg = composed.clone();
            tamper_subslice(&mut bad_agg, agg);
            assert!(!verify_unitary_trajectory_leaf_compose(&ctx, &bad_agg));
        }

        let tail_idx = composed.len() - 1;
        composed[tail_idx] ^= 0xFF;
        assert!(!verify_unitary_trajectory_leaf_compose(&ctx, &composed));
    }

    #[cfg(feature = "plonky3-stark")]
    #[test]
    fn composed_proof_rejects_wrong_verify_context() {
        let (ctx, composed) = if_compose_fixture();
        assert!(verify_unitary_trajectory_leaf_compose(&ctx, &composed));

        let wrong_sub = StarkContext {
            circuit_id: ctx.circuit_id,
            sub_task_id: "other-sub",
            node_id: ctx.node_id,
            slice_id: ctx.slice_id,
            output_hash: ctx.output_hash,
            terminal_statevector_digest: ctx.terminal_statevector_digest,
            measurement_spec_hash: "",
        };
        assert!(!verify_unitary_trajectory_leaf_compose(
            &wrong_sub, &composed
        ));

        let wrong_output = StarkContext {
            circuit_id: ctx.circuit_id,
            sub_task_id: ctx.sub_task_id,
            node_id: ctx.node_id,
            slice_id: ctx.slice_id,
            output_hash: "deadbeef",
            terminal_statevector_digest: ctx.terminal_statevector_digest,
            measurement_spec_hash: "",
        };
        assert!(!verify_unitary_trajectory_leaf_compose(
            &wrong_output,
            &composed
        ));
    }

    #[cfg(feature = "plonky3-stark")]
    #[test]
    fn composed_proof_rejects_tampered_unitary_link_in_trajectory_child() {
        let (ctx, composed) = if_compose_fixture();
        let link = ctx.terminal_statevector_digest.as_bytes();
        let mut tampered = composed.clone();
        tamper_subslice(&mut tampered, link);
        assert!(!verify_unitary_trajectory_leaf_compose(&ctx, &tampered));
    }

    #[cfg(feature = "plonky3-stark")]
    #[test]
    fn verify_stark_proof_core_routes_composed_leaf() {
        use crate::verify_stark_proof_core;

        let (ctx, composed) = if_compose_fixture();
        assert!(verify_stark_proof_core(&ctx, &composed));

        let mut bad = composed.clone();
        let mid = bad.len() / 2;
        bad[mid] ^= 0xFF;
        assert!(!verify_stark_proof_core(&ctx, &bad));
    }
}

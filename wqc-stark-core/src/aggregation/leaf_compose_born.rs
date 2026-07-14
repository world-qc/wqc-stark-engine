//! C2c extension: `leaf:unitary_born` v3 compose (terminal Born symmetry with `leaf:unitary_traj`).
//!
//! Terminal `sample_counts` proofs pair:
//! - **Left child**: v2 Plonky3 unitary transcript (`terminal_statevector_digest` = Born binding digest)
//! - **Right child**: DIST segment + Born zk tail (`_M31_BORN_LEAF_V1_`)
//!
//! An R2 `AggregationAir` tail binds the two child SHA3-256 digests.

use crate::aggregation::leaf::{parse_leaf_binding, parsed_to_stark_context};
use crate::aggregation::transcript_v3::{
    child_digest, decode_compose_v3, decode_compose_v3_slices, is_compose_v3,
};
use crate::aggregation::{compose_stark_proofs, ComposeContext};
use crate::distribution::{
    append_distribution_tail, decode_and_verify_distribution_tail, split_distribution_tail,
    DistributionSegment,
};
use crate::transcript::StarkContext;

#[cfg(feature = "plonky3-stark")]
use crate::plonky3_stark::split_agg_tail;
#[cfg(feature = "plonky3-stark")]
use crate::plonky3_stark::{
    append_born_stark_tail, has_born_stark_tail, segment_supports_born_zk, split_born_stark_tail,
    verify_born_stark_proof, verify_plonky3_proof, BornStarkContext,
};

use super::leaf_compose::compose_v3_body;

/// v3 compose label for a terminal unitary + Born leaf pair.
pub const UNITARY_BORN_COMPOSE_LABEL: &str = "leaf:unitary_born";

/// Marker prefix on the Born-only child transcript.
pub const BORN_LEAF_MARKER: &[u8] = b"_M31_BORN_LEAF_V1_";

/// Returns true when `proof` is a v3 compose node with label `leaf:unitary_born`.
pub fn is_unitary_born_leaf_compose(proof: &[u8]) -> bool {
    if !is_compose_v3(proof) {
        return false;
    }
    let v3 = compose_v3_body(proof);
    decode_compose_v3(v3)
        .is_some_and(|(header, _, _)| header.compose_label == UNITARY_BORN_COMPOSE_LABEL)
}

/// Extracts the Born child bytes from a composed leaf, if present.
pub fn born_child_from_compose(proof: &[u8]) -> Option<&[u8]> {
    if !is_unitary_born_leaf_compose(proof) {
        return None;
    }
    let v3 = compose_v3_body(proof);
    let (header, _, right) = decode_compose_v3_slices(v3)?;
    if header.compose_label != UNITARY_BORN_COMPOSE_LABEL {
        return None;
    }
    Some(right)
}

/// Resolves the proof slice that carries DIST / Born tails.
pub fn born_proof_view(proof: &[u8]) -> &[u8] {
    born_child_from_compose(proof).unwrap_or(proof)
}

/// Encodes a Born-only leaf child (DIST segment + optional Born zk inner transcript).
pub fn encode_born_leaf(
    sub_task_id: &str,
    segment: &DistributionSegment,
    born_inner: Option<&[u8]>,
) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(sub_task_id.as_bytes());
    out.push(0);
    out.extend_from_slice(BORN_LEAF_MARKER);
    out = append_distribution_tail(out, segment);
    #[cfg(feature = "plonky3-stark")]
    if let Some(inner) = born_inner.filter(|b| !b.is_empty()) {
        out = append_born_stark_tail(out, inner);
    }
    #[cfg(not(feature = "plonky3-stark"))]
    let _ = born_inner;
    out
}

fn parse_born_leaf_prefix(proof: &[u8]) -> Option<(&str, &[u8])> {
    let marker_pos = proof
        .windows(BORN_LEAF_MARKER.len())
        .position(|w| w == BORN_LEAF_MARKER)?;
    let sub_end = marker_pos.saturating_sub(1);
    if marker_pos == 0 || proof.get(sub_end)? != &0 {
        return None;
    }
    let sub_task_id = std::str::from_utf8(&proof[..sub_end]).ok()?;
    let tail_start = marker_pos + BORN_LEAF_MARKER.len();
    Some((sub_task_id, proof.get(tail_start..)?))
}

pub fn is_born_leaf_proof(proof: &[u8]) -> bool {
    parse_born_leaf_prefix(proof).is_some()
}

/// Verifies a Born-only leaf child (DIST segment + optional Born zk).
pub fn verify_born_leaf(sub_task_id: &str, proof: &[u8]) -> Result<(), String> {
    let (parsed_sub, tail_body) =
        parse_born_leaf_prefix(proof).ok_or_else(|| "malformed Born leaf prefix".to_string())?;
    if parsed_sub != sub_task_id {
        return Err("Born leaf sub_task_id mismatch".to_string());
    }

    let (_, tail) = split_distribution_tail(tail_body)
        .ok_or_else(|| "missing distribution segment tail".to_string())?;
    let (payload, marker) = tail.ok_or_else(|| "missing distribution segment tail".to_string())?;
    let segment = decode_and_verify_distribution_tail(payload, marker)
        .ok_or_else(|| "invalid distribution segment".to_string())?;

    #[cfg(feature = "plonky3-stark")]
    if has_born_stark_tail(tail_body) {
        if !segment_supports_born_zk(&segment) {
            return Err("Born zk tail without zk-capable segment".to_string());
        }
        let born_bytes =
            split_born_stark_tail(tail_body).ok_or_else(|| "malformed Born zk tail".to_string())?;
        let sv = segment
            .born_binding
            .as_ref()
            .map(|b| b.terminal_statevector_digest.as_str())
            .unwrap_or("");
        let born_ctx = BornStarkContext {
            sub_task_id,
            probability_digest: &segment.probability_digest,
            terminal_statevector_digest: sv,
        };
        if !verify_born_stark_proof(&born_ctx, &segment, born_bytes) {
            return Err("Born zk verification failed".to_string());
        }
    }

    Ok(())
}

/// Pairs a verified unitary v2 proof with a Born leaf into a v3 compose transcript + agg tail.
#[cfg(feature = "plonky3-stark")]
pub fn compose_unitary_born_leaf(
    context: &StarkContext<'_>,
    unitary_v2_proof: &[u8],
    segment: &DistributionSegment,
    born_inner: &[u8],
) -> Result<Vec<u8>, String> {
    if context.sub_task_id.is_empty() {
        return Err("sub_task_id is required".to_string());
    }
    let binding = segment
        .born_binding
        .as_ref()
        .ok_or_else(|| "born_binding is required for unitary+Born compose".to_string())?;
    if binding.terminal_statevector_digest.is_empty() {
        return Err("terminal_statevector_digest is required for unitary+Born compose".to_string());
    }
    if !segment_supports_born_zk(segment) {
        return Err("distribution segment does not support Born zk".to_string());
    }
    if crate::trajectory::has_trajectory_tail(unitary_v2_proof)
        || split_distribution_tail(unitary_v2_proof)
            .and_then(|(_, tail)| tail)
            .is_some()
    {
        return Err("unitary child must not include auxiliary tails".to_string());
    }

    let link = binding.terminal_statevector_digest.as_str();
    let unitary_ctx = StarkContext {
        circuit_id: context.circuit_id,
        sub_task_id: context.sub_task_id,
        node_id: context.node_id,
        slice_id: context.slice_id,
        output_hash: context.output_hash,
        terminal_statevector_digest: link,
        measurement_spec_hash: context.measurement_spec_hash,
    };

    if !verify_plonky3_proof(&unitary_ctx, unitary_v2_proof) {
        return Err("unitary child Plonky3 verification failed".to_string());
    }

    let parsed = parse_leaf_binding(unitary_v2_proof)
        .ok_or_else(|| "cannot parse unitary child public inputs".to_string())?;
    if parsed.terminal_statevector_digest != link {
        return Err(
            "terminal_statevector_digest mismatch between unitary child and Born binding"
                .to_string(),
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
            "measurement_spec_hash mismatch between unitary child and distribution segment"
                .to_string(),
        );
    }

    let born_child = encode_born_leaf(context.sub_task_id, segment, Some(born_inner));
    verify_born_leaf(context.sub_task_id, &born_child)?;

    compose_stark_proofs(
        &ComposeContext {
            parent_task_id: context.sub_task_id,
            compose_label: UNITARY_BORN_COMPOSE_LABEL,
            manifest_root_hash: "",
        },
        unitary_v2_proof,
        &born_child,
        Some(&unitary_ctx),
        None,
    )
}

/// Verifies a `leaf:unitary_born` v3 compose transcript.
#[cfg(feature = "plonky3-stark")]
pub fn verify_unitary_born_leaf_compose(context: &StarkContext<'_>, proof: &[u8]) -> bool {
    if !is_unitary_born_leaf_compose(proof) {
        eprintln!("[LeafCompose] Failed: not a unitary+Born compose proof");
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
    if header.compose_label != UNITARY_BORN_COMPOSE_LABEL {
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

    if let Err(err) = verify_born_leaf(context.sub_task_id, right_child) {
        eprintln!("[LeafCompose] Failed: Born child: {err}");
        return false;
    }

    let tail_body = parse_born_leaf_prefix(right_child)
        .map(|(_, tail)| tail)
        .unwrap_or(right_child);
    let (_, tail) = match split_distribution_tail(tail_body) {
        Some(parts) => parts,
        None => {
            eprintln!("[LeafCompose] Failed: distribution segment missing");
            return false;
        }
    };
    let (payload, marker) = match tail {
        Some(parts) => parts,
        None => {
            eprintln!("[LeafCompose] Failed: distribution segment missing");
            return false;
        }
    };
    let segment = match decode_and_verify_distribution_tail(payload, marker) {
        Some(seg) => seg,
        None => {
            eprintln!("[LeafCompose] Failed: invalid distribution segment");
            return false;
        }
    };

    let link = segment
        .born_binding
        .as_ref()
        .map(|b| b.terminal_statevector_digest.as_str())
        .unwrap_or("");
    if !link.is_empty() && parsed.terminal_statevector_digest != link {
        eprintln!("[LeafCompose] Failed: unitary↔Born link digest mismatch");
        return false;
    }
    if !parsed.measurement_spec_hash.is_empty()
        && !segment.measurement_spec_hash.is_empty()
        && parsed.measurement_spec_hash != segment.measurement_spec_hash
    {
        eprintln!("[LeafCompose] Failed: measurement_spec_hash mismatch vs distribution segment");
        return false;
    }

    if let Some(agg_bytes) = split_agg_tail(proof).map(|(_, agg)| agg) {
        let agg_ctx = crate::plonky3_stark::AggregationContext {
            parent_task_id: context.sub_task_id,
            compose_label: UNITARY_BORN_COMPOSE_LABEL,
            manifest_root_hash: "",
            left_child_hash: header.left_child_hash,
            right_child_hash: header.right_child_hash,
        };
        if !crate::plonky3_stark::verify_aggregation_proof(&agg_ctx, agg_bytes) {
            eprintln!("[LeafCompose] Failed: aggregation STARK verification failed");
            return false;
        }
    }

    eprintln!("[LeafCompose] Verification success (unitary+Born v3 compose, link={link})");
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bell_segment() -> DistributionSegment {
        let inv_sqrt2 = 1.0f64 / 2.0f64.sqrt();
        let sv = vec![(inv_sqrt2, 0.0), (0.0, 0.0), (0.0, 0.0), (inv_sqrt2, 0.0)];
        let probs = vec![("00".into(), 0.5), ("11".into(), 0.5)];
        let binding = crate::distribution::BornBinding::from_specs(2, 2, &[(0, 0), (1, 1)], sv)
            .expect("bind");
        DistributionSegment {
            sample_seed: 42,
            shots: 128,
            measurement_spec_hash: "spec".into(),
            probability_digest: crate::distribution::calculate_probability_digest(&probs),
            probabilities: probs,
            born_binding: Some(binding),
        }
    }

    #[test]
    fn born_leaf_roundtrip_prefix() {
        let segment = bell_segment();
        let leaf = encode_born_leaf("sub-born", &segment, None);
        assert!(is_born_leaf_proof(&leaf));
        verify_born_leaf("sub-born", &leaf).expect("verify leaf");
    }

    #[cfg(feature = "plonky3-stark")]
    fn born_compose_fixture() -> (StarkContext<'static>, Vec<u8>) {
        use crate::generate_plonky3_stark_proof;
        use crate::plonky3_stark::generate_born_stark_proof;

        let segment = bell_segment();
        let link: &'static str = Box::leak(
            segment
                .born_binding
                .as_ref()
                .unwrap()
                .terminal_statevector_digest
                .clone()
                .into_boxed_str(),
        );
        let ctx = StarkContext {
            circuit_id: "circuit-bell",
            sub_task_id: "sub-born",
            node_id: "node-1",
            slice_id: "0",
            output_hash: "counts-hash",
            terminal_statevector_digest: link,
            measurement_spec_hash: "",
        };
        let trace = crate::trace_spec::golden_h_q0_trace();
        let unitary = generate_plonky3_stark_proof(&ctx, &trace).expect("unitary prove");
        let born_ctx = BornStarkContext {
            sub_task_id: "sub-born",
            probability_digest: &segment.probability_digest,
            terminal_statevector_digest: link,
        };
        let born_inner = generate_born_stark_proof(&born_ctx, &segment).expect("born zk");
        let composed =
            compose_unitary_born_leaf(&ctx, &unitary, &segment, &born_inner).expect("compose");
        (ctx, composed)
    }

    #[cfg(feature = "plonky3-stark")]
    #[test]
    fn unitary_born_compose_roundtrip() {
        let (ctx, composed) = born_compose_fixture();
        assert!(is_unitary_born_leaf_compose(&composed));
        assert!(verify_unitary_born_leaf_compose(&ctx, &composed));
        assert!(born_child_from_compose(&composed).is_some());
        assert!(composed
            .windows(BORN_LEAF_MARKER.len())
            .any(|w| w == BORN_LEAF_MARKER));
    }

    #[cfg(feature = "plonky3-stark")]
    #[test]
    fn compose_rejects_born_link_digest_mismatch() {
        use crate::generate_plonky3_stark_proof;
        use crate::plonky3_stark::generate_born_stark_proof;

        let segment = bell_segment();
        let link = segment
            .born_binding
            .as_ref()
            .unwrap()
            .terminal_statevector_digest
            .clone();
        let ctx = StarkContext {
            circuit_id: "circuit-bell",
            sub_task_id: "sub-born",
            node_id: "node-1",
            slice_id: "0",
            output_hash: "counts-hash",
            terminal_statevector_digest: &link,
            measurement_spec_hash: "",
        };
        let trace = crate::trace_spec::golden_h_q0_trace();
        let unitary = generate_plonky3_stark_proof(&ctx, &trace).expect("unitary prove");
        let born_ctx = BornStarkContext {
            sub_task_id: "sub-born",
            probability_digest: &segment.probability_digest,
            terminal_statevector_digest: &link,
        };
        let born_inner = generate_born_stark_proof(&born_ctx, &segment).expect("born zk");

        let mut bad = segment;
        if let Some(b) = bad.born_binding.as_mut() {
            b.terminal_statevector_digest = "00".repeat(32);
        }
        let err = compose_unitary_born_leaf(&ctx, &unitary, &bad, &born_inner)
            .expect_err("tampered link");
        assert!(
            err.contains("terminal_statevector_digest mismatch")
                || err.contains("unitary child Plonky3 verification failed")
                || err.contains("Born zk"),
            "unexpected error: {err}"
        );
    }

    #[cfg(feature = "plonky3-stark")]
    #[test]
    fn verify_stark_proof_core_routes_born_composed_leaf() {
        use crate::verify_stark_proof_core;

        let (ctx, composed) = born_compose_fixture();
        assert!(verify_stark_proof_core(&ctx, &composed));
        let mut bad = composed.clone();
        let mid = bad.len() / 2;
        bad[mid] ^= 0xFF;
        assert!(!verify_stark_proof_core(&ctx, &bad));
    }
}

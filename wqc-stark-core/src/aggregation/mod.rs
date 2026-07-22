//! Proof-tree aggregation (v3 compose transcripts + R2/R3 aggregation STARKs).
//!
//! ## Model
//!
//! - **Leaf proofs** (v1/v2) are verified at node ingest before rewards.
//! - **Compose** pairs two already-valid child proofs into a v3 container.
//! - **R2**: optional legacy `AggregationAir` STARK tail (digest + OK flags).
//! - **R3-M1–M3e**: `RecursiveAggregationAir` STARK tail binding child digests **and**
//!   SHA3 digests of verified child Plonky3 payloads (+ V6 PCS certs; see zk-STARK.md §8).
//! - **Root verify (fast path)**: single rec-agg (or legacy agg) STARK at the root.
//! - **Root verify (audit)**: walks the v3 tree and re-checks every leaf STARK.

mod leaf;
mod leaf_compose;
mod leaf_compose_born;

pub(crate) use leaf_compose::parse_trajectory_leaf_prefix;
pub(crate) use leaf_compose_born::parse_born_leaf_prefix;
mod transcript_v3;

#[cfg(feature = "plonky3-stark")]
use crate::plonky3_stark::{
    append_agg_tail, append_rec_tail, build_agg_pcs_certificate, build_leaf_pcs_bundle_from_child,
    child_aggregation_transcript, child_stark_binding, generate_aggregation_proof,
    generate_recursive_aggregation_proof, split_agg_tail, split_rec_tail,
    verify_agg_pcs_certificate, verify_aggregation_proof, verify_leaf_pcs_bundle,
    verify_recursive_aggregation_proof, AggregationContext, LeafPcsBundle,
    RecursiveAggregationContext, REC_KIND_AGG, REC_KIND_LEAF,
};

pub use leaf::{parse_leaf_binding, parsed_to_stark_context, ParsedLeafBinding};
#[cfg(feature = "plonky3-stark")]
pub use leaf_compose::{compose_unitary_trajectory_leaf, verify_unitary_trajectory_leaf_compose};
pub use leaf_compose::{
    encode_trajectory_leaf, is_trajectory_leaf_proof, is_unitary_trajectory_leaf_compose,
    trajectory_child_from_compose, trajectory_proof_view, verify_trajectory_leaf, TRAJ_LEAF_MARKER,
    UNITARY_TRAJ_COMPOSE_LABEL,
};
pub use leaf_compose_born::{
    born_child_from_compose, born_proof_view, encode_born_leaf, is_born_leaf_proof,
    is_unitary_born_leaf_compose, verify_born_leaf, BORN_LEAF_MARKER, UNITARY_BORN_COMPOSE_LABEL,
};
#[cfg(feature = "plonky3-stark")]
pub use leaf_compose_born::{compose_unitary_born_leaf, verify_unitary_born_leaf_compose};
pub use transcript_v3::{
    child_digest, decode_compose_v3, decode_compose_v3_slices, encode_compose_v3, is_compose_v3,
    ComposeHeader, CHILD_HASH_LEN, V3_COMPOSE_MARKER,
};

use crate::transcript::StarkContext;
use crate::verify_stark_proof_core;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ComposeContext<'a> {
    pub parent_task_id: &'a str,
    pub compose_label: &'a str,
    pub manifest_root_hash: &'a str,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RootVerifyContext<'a> {
    pub parent_task_id: &'a str,
    pub manifest_root_hash: &'a str,
}

/// Verifies a single child proof (leaf or nested compose) before composition.
pub fn verify_child_proof(
    child: &[u8],
    parent_task_id: &str,
    leaf_ctx: Option<&StarkContext<'_>>,
) -> Result<(), String> {
    if child.is_empty() {
        return Err("child proof is empty".to_string());
    }
    if is_trajectory_leaf_proof(child) {
        return verify_trajectory_leaf(parent_task_id, child)
            .map_err(|e| format!("trajectory leaf verification failed: {e}"));
    }
    if is_born_leaf_proof(child) {
        return verify_born_leaf(parent_task_id, child)
            .map_err(|e| format!("Born leaf verification failed: {e}"));
    }

    if is_compose_v3(child) {
        let embedded_parent = leaf_compose::is_unitary_trajectory_leaf_compose(child)
            .then(|| leaf_compose::compose_v3_body(child))
            .and_then(|v3| {
                transcript_v3::decode_compose_v3_slices(v3)
                    .map(|(header, _, _)| header.parent_task_id)
            })
            .or_else(|| {
                leaf_compose_born::is_unitary_born_leaf_compose(child)
                    .then(|| leaf_compose::compose_v3_body(child))
                    .and_then(|v3| {
                        transcript_v3::decode_compose_v3_slices(v3)
                            .map(|(header, _, _)| header.parent_task_id)
                    })
            });
        return verify_composed_proof(
            &ComposeContext {
                parent_task_id: embedded_parent.as_deref().unwrap_or(parent_task_id),
                compose_label: "",
                manifest_root_hash: "",
            },
            child,
        );
    }

    if let Some(ctx) = leaf_ctx {
        if verify_stark_proof_core(ctx, child) {
            return Ok(());
        }
        return Err("leaf proof verification failed".to_string());
    }

    let parsed =
        parse_leaf_binding(child).ok_or_else(|| "cannot parse leaf public inputs".to_string())?;
    let ctx = parsed_to_stark_context(&parsed);
    if verify_stark_proof_core(&ctx, child) {
        Ok(())
    } else {
        Err("leaf proof verification failed".to_string())
    }
}

/// Pairs two verified child proofs into a v3 compose transcript.
pub fn compose_stark_proofs(
    context: &ComposeContext<'_>,
    left_child: &[u8],
    right_child: &[u8],
    left_leaf_ctx: Option<&StarkContext<'_>>,
    right_leaf_ctx: Option<&StarkContext<'_>>,
) -> Result<Vec<u8>, String> {
    if context.parent_task_id.is_empty() {
        return Err("parent_task_id is required".to_string());
    }
    verify_child_proof(left_child, context.parent_task_id, left_leaf_ctx)?;
    verify_child_proof(right_child, context.parent_task_id, right_leaf_ctx)?;

    let left_hash = child_digest(left_child);
    let right_hash = child_digest(right_child);

    let mut out = encode_compose_v3(
        context.parent_task_id,
        context.compose_label,
        context.manifest_root_hash,
        left_child,
        right_child,
    );

    #[cfg(feature = "plonky3-stark")]
    {
        // R2 AggregationAir (needed so parents can build R3-M2 PCS certificates).
        let agg_ctx = AggregationContext {
            parent_task_id: context.parent_task_id,
            compose_label: context.compose_label,
            manifest_root_hash: context.manifest_root_hash,
            left_child_hash: left_hash,
            right_child_hash: right_hash,
        };
        let agg_proof = generate_aggregation_proof(&agg_ctx)
            .map_err(|e| format!("aggregation STARK prove failed: {e}"))?;
        out = append_agg_tail(out, &agg_proof);

        let left_bind = child_stark_binding(left_child);
        let right_bind = child_stark_binding(right_child);
        let left_pcs = pcs_for_child(left_child, context.parent_task_id)?;
        let right_pcs = pcs_for_child(right_child, context.parent_task_id)?;
        log_child_pcs_sizes("left", &left_pcs);
        log_child_pcs_sizes("right", &right_pcs);

        let rec_ctx = RecursiveAggregationContext {
            parent_task_id: context.parent_task_id,
            compose_label: context.compose_label,
            manifest_root_hash: context.manifest_root_hash,
            left_child_hash: left_hash,
            right_child_hash: right_hash,
            left_stark_digest: left_bind.stark_digest,
            right_stark_digest: right_bind.stark_digest,
            left_kind: left_pcs.kind,
            right_kind: right_pcs.kind,
            left_agg_cert: left_pcs.agg_cert,
            right_agg_cert: right_pcs.agg_cert,
            left_leaf_bundle: left_pcs.leaf_bundle,
            right_leaf_bundle: right_pcs.leaf_bundle,
        };
        let rec_proof = generate_recursive_aggregation_proof(&rec_ctx)
            .map_err(|e| format!("R3-M2 recursive aggregation STARK prove failed: {e}"))?;
        out = append_rec_tail(out, &rec_proof);
    }

    Ok(out)
}

#[cfg(feature = "plonky3-stark")]
struct ChildPcs {
    kind: u8,
    agg_cert: Option<crate::plonky3_stark::AggPcsCertificate>,
    leaf_bundle: Option<LeafPcsBundle>,
}

#[cfg(feature = "plonky3-stark")]
fn log_child_pcs_sizes(side: &str, pcs: &ChildPcs) {
    use crate::plonky3_stark::leaf_bundle_stark_sizes;
    if let Some(bundle) = &pcs.leaf_bundle {
        let s = leaf_bundle_stark_sizes(bundle);
        eprintln!(
            "[M4c size] compose {side} leaf PCS STARKs total={} bytes ({:.2} MiB); certs={} mmcs_groups={} fri_fold={} deep_ro={} ood={}",
            s.total,
            s.total as f64 / (1024.0 * 1024.0),
            bundle.certs.len(),
            s.mmcs_groups,
            s.fri_fold,
            s.deep_ro,
            s.ood,
        );
    } else if pcs.agg_cert.is_some() {
        eprintln!("[M4c size] compose {side} agg PCS present (nested)");
    } else {
        eprintln!("[M4c size] compose {side} PCS absent (deferred)");
    }
}

#[cfg(feature = "plonky3-stark")]
fn pcs_for_child(child: &[u8], _parent_task_id: &str) -> Result<ChildPcs, String> {
    if let Some(agg) = child_aggregation_transcript(child) {
        let cert = cert_for_child_agg(agg)?;
        return Ok(ChildPcs {
            kind: REC_KIND_AGG,
            agg_cert: Some(cert),
            leaf_bundle: None,
        });
    }

    if child_supports_leaf_pcs(child) {
        match build_leaf_pcs_bundle_from_child(child) {
            Ok(bundle) => match verify_leaf_pcs_bundle(child, &bundle) {
                Ok(()) => {
                    return Ok(ChildPcs {
                        kind: REC_KIND_LEAF,
                        agg_cert: None,
                        leaf_bundle: Some(bundle),
                    });
                }
                Err(e) => {
                    // Legacy compose without bundle when cert verify fails (e.g. DistributionAir FRI).
                    eprintln!("[Aggregation] leaf PCS bundle deferred (verify): {e}");
                }
            },
            Err(e) => {
                eprintln!("[Aggregation] leaf PCS bundle deferred (build): {e}");
            }
        }
    }

    Ok(ChildPcs {
        kind: REC_KIND_LEAF,
        agg_cert: None,
        leaf_bundle: None,
    })
}

#[cfg(feature = "plonky3-stark")]
fn child_supports_leaf_pcs(child: &[u8]) -> bool {
    if child_aggregation_transcript(child).is_some() {
        return false;
    }
    if is_born_leaf_proof(child) || is_trajectory_leaf_proof(child) {
        return true;
    }
    let base = crate::trajectory::base_proof_without_aux_tails(
        crate::distribution::base_proof_without_distribution_tail(child),
    );
    parse_leaf_binding(base).is_some()
}

#[cfg(feature = "plonky3-stark")]
fn cert_for_child_agg(agg: &[u8]) -> Result<crate::plonky3_stark::AggPcsCertificate, String> {
    use crate::plonky3_stark::parse_agg_v4_header_any;

    let header = parse_agg_v4_header_any(agg)
        .ok_or_else(|| "cannot parse child AggregationAir V4 header".to_string())?;
    let agg_ctx = AggregationContext {
        parent_task_id: header.parent_task_id.as_str(),
        compose_label: header.compose_label.as_str(),
        manifest_root_hash: header.manifest_root_hash.as_str(),
        left_child_hash: header.left_child_hash,
        right_child_hash: header.right_child_hash,
    };
    let cert = build_agg_pcs_certificate(&agg_ctx, agg)
        .map_err(|e| format!("R3-M2 AggregationAir PCS certificate failed: {e}"))?;
    if !verify_agg_pcs_certificate(&agg_ctx, agg, &cert) {
        return Err("R3-M2 AggregationAir PCS certificate self-check failed".to_string());
    }
    Ok(cert)
}

/// Recursively verifies a v3 compose tree (all embedded leaves).
pub fn verify_composed_proof(context: &ComposeContext<'_>, proof: &[u8]) -> Result<(), String> {
    #[cfg(feature = "plonky3-stark")]
    let (v3_proof, rec_tail, agg_tail) = {
        if let Some((body, rec)) = split_rec_tail(proof) {
            let (v3, agg) = match split_agg_tail(body) {
                Some((v3, agg)) => (v3, Some(agg)),
                None => (body, None),
            };
            (v3, Some(rec), agg)
        } else if let Some((v3, agg)) = split_agg_tail(proof) {
            (v3, None, Some(agg))
        } else {
            (proof, None, None)
        }
    };
    #[cfg(not(feature = "plonky3-stark"))]
    let v3_proof = proof;

    if !is_compose_v3(v3_proof) {
        return Err("not a v3 compose proof".to_string());
    }

    let (header, left_child, right_child) =
        decode_compose_v3(v3_proof).ok_or_else(|| "malformed v3 compose transcript".to_string())?;

    if header.parent_task_id != context.parent_task_id {
        return Err(format!(
            "parent_task_id mismatch: expected {}, got {}",
            context.parent_task_id, header.parent_task_id
        ));
    }

    if child_digest(&left_child) != header.left_child_hash {
        return Err("left child digest mismatch".to_string());
    }
    if child_digest(&right_child) != header.right_child_hash {
        return Err("right child digest mismatch".to_string());
    }

    if context.compose_label == "root" {
        if header.compose_label != "root" {
            return Err("expected root compose label".to_string());
        }
        if !context.manifest_root_hash.is_empty()
            && header.manifest_root_hash != context.manifest_root_hash
        {
            return Err("manifest_root_hash mismatch".to_string());
        }
    }

    verify_child_proof(&left_child, context.parent_task_id, None)?;
    verify_child_proof(&right_child, context.parent_task_id, None)?;

    #[cfg(feature = "plonky3-stark")]
    if let Some(rec_bytes) = rec_tail {
        let rec_ctx = rebuild_rec_context(
            context.parent_task_id,
            header.compose_label.as_str(),
            header.manifest_root_hash.as_str(),
            header.left_child_hash,
            header.right_child_hash,
            &left_child,
            &right_child,
        )?;
        if !verify_recursive_aggregation_proof(&rec_ctx, rec_bytes) {
            return Err("R3-M2 recursive aggregation STARK verification failed".to_string());
        }
    } else if let Some(agg_bytes) = agg_tail {
        let agg_ctx = AggregationContext {
            parent_task_id: context.parent_task_id,
            compose_label: header.compose_label.as_str(),
            manifest_root_hash: header.manifest_root_hash.as_str(),
            left_child_hash: header.left_child_hash,
            right_child_hash: header.right_child_hash,
        };
        if !verify_aggregation_proof(&agg_ctx, agg_bytes) {
            return Err("aggregation STARK verification failed".to_string());
        }
    }

    Ok(())
}

/// Rebuilds R3 recursive aggregation context (PCS certs / leaf bundles) for two children.
#[cfg(feature = "plonky3-stark")]
pub fn recursive_context_for_children<'a>(
    parent_task_id: &'a str,
    compose_label: &'a str,
    manifest_root_hash: &'a str,
    left_child_hash: [u8; CHILD_HASH_LEN],
    right_child_hash: [u8; CHILD_HASH_LEN],
    left_child: &'a [u8],
    right_child: &'a [u8],
) -> Result<RecursiveAggregationContext<'a>, String> {
    rebuild_rec_context(
        parent_task_id,
        compose_label,
        manifest_root_hash,
        left_child_hash,
        right_child_hash,
        left_child,
        right_child,
    )
}

#[cfg(feature = "plonky3-stark")]
fn rebuild_rec_context<'a>(
    parent_task_id: &'a str,
    compose_label: &'a str,
    manifest_root_hash: &'a str,
    left_child_hash: [u8; CHILD_HASH_LEN],
    right_child_hash: [u8; CHILD_HASH_LEN],
    left_child: &'a [u8],
    right_child: &'a [u8],
) -> Result<RecursiveAggregationContext<'a>, String> {
    let left_bind = child_stark_binding(left_child);
    let right_bind = child_stark_binding(right_child);
    let left_pcs = pcs_for_child(left_child, parent_task_id)?;
    let right_pcs = pcs_for_child(right_child, parent_task_id)?;
    Ok(RecursiveAggregationContext {
        parent_task_id,
        compose_label,
        manifest_root_hash,
        left_child_hash,
        right_child_hash,
        left_stark_digest: left_bind.stark_digest,
        right_stark_digest: right_bind.stark_digest,
        left_kind: left_pcs.kind,
        right_kind: right_pcs.kind,
        left_agg_cert: left_pcs.agg_cert,
        right_agg_cert: right_pcs.agg_cert,
        left_leaf_bundle: left_pcs.leaf_bundle,
        right_leaf_bundle: right_pcs.leaf_bundle,
    })
}

/// Verifies a task root proof tree.
///
/// With `plonky3-stark`, tries the R3-M1 recursive aggregation STARK fast path first,
/// then the legacy R2 aggregation STARK, then falls back to the v3 audit walk.
pub fn verify_root_proof(context: &RootVerifyContext<'_>, proof: &[u8]) -> bool {
    if context.parent_task_id.is_empty() {
        eprintln!("[Aggregation] Failed: parent_task_id is empty");
        return false;
    }

    #[cfg(feature = "plonky3-stark")]
    {
        // R3-M1 fast path: recursive aggregation STARK at root.
        if let Some((body, rec_bytes)) = split_rec_tail(proof) {
            let v3_part = split_agg_tail(body).map(|(v3, _)| v3).unwrap_or(body);
            if let Some((header, left_child, right_child)) = decode_compose_v3(v3_part) {
                if header.compose_label == "root" {
                    if !context.manifest_root_hash.is_empty()
                        && header.manifest_root_hash != context.manifest_root_hash
                    {
                        eprintln!("[Aggregation] Failed: manifest_root_hash mismatch");
                        return false;
                    }
                    match rebuild_rec_context(
                        context.parent_task_id,
                        "root",
                        context.manifest_root_hash,
                        header.left_child_hash,
                        header.right_child_hash,
                        &left_child,
                        &right_child,
                    ) {
                        Ok(rec_ctx) => {
                            if verify_recursive_aggregation_proof(&rec_ctx, rec_bytes) {
                                eprintln!(
                                    "[Aggregation] Root proof verified (R3-M2 fast path) for task {}",
                                    context.parent_task_id
                                );
                                return true;
                            }
                            eprintln!(
                                "[Aggregation] Root R3-M2 STARK failed; falling back to audit walk"
                            );
                        }
                        Err(e) => {
                            eprintln!("[Aggregation] Root R3-M2 context rebuild failed: {e}");
                        }
                    }
                }
            }
        }

        // Legacy R2 fast path.
        if let Some((v3_part, agg_bytes)) = split_agg_tail(proof) {
            if let Some((header, _, _)) = decode_compose_v3(v3_part) {
                if header.compose_label == "root" {
                    let agg_ctx = AggregationContext {
                        parent_task_id: context.parent_task_id,
                        compose_label: "root",
                        manifest_root_hash: context.manifest_root_hash,
                        left_child_hash: header.left_child_hash,
                        right_child_hash: header.right_child_hash,
                    };
                    if !context.manifest_root_hash.is_empty()
                        && header.manifest_root_hash != context.manifest_root_hash
                    {
                        eprintln!("[Aggregation] Failed: manifest_root_hash mismatch");
                        return false;
                    }
                    if verify_aggregation_proof(&agg_ctx, agg_bytes) {
                        eprintln!(
                            "[Aggregation] Root proof verified (R2 fast path) for task {}",
                            context.parent_task_id
                        );
                        return true;
                    }
                    eprintln!(
                        "[Aggregation] Root aggregation STARK failed; falling back to audit walk"
                    );
                }
            }
        }
    }

    // Strip optional STARK tails before checking the v3 marker on the audit path.
    #[cfg(feature = "plonky3-stark")]
    let audit_proof = {
        let body = split_rec_tail(proof).map(|(b, _)| b).unwrap_or(proof);
        split_agg_tail(body).map(|(v3, _)| v3).unwrap_or(body)
    };
    #[cfg(not(feature = "plonky3-stark"))]
    let audit_proof = proof;

    if !is_compose_v3(audit_proof) {
        eprintln!("[Aggregation] Failed: root proof is not v3 compose");
        return false;
    }

    let compose_ctx = ComposeContext {
        parent_task_id: context.parent_task_id,
        compose_label: "root",
        manifest_root_hash: context.manifest_root_hash,
    };

    match verify_composed_proof(&compose_ctx, proof) {
        Ok(()) => {
            eprintln!(
                "[Aggregation] Root proof verified (audit walk) for task {}",
                context.parent_task_id
            );
            true
        }
        Err(err) => {
            eprintln!("[Aggregation] Root verification failed: {err}");
            false
        }
    }
}

#[cfg(test)]
mod integration_tests {
    use super::*;
    use crate::transcript::StarkContext;

    fn leaf_context(sub: &'static str, slice: &'static str) -> StarkContext<'static> {
        StarkContext {
            circuit_id: "circuit-1",
            sub_task_id: sub,
            node_id: "node-1",
            slice_id: slice,
            output_hash: "out-hash",
            terminal_statevector_digest: "",
            measurement_spec_hash: "",
        }
    }

    fn sample_trace() -> Vec<f64> {
        crate::trace_spec::idle_qubit0_trace()
    }

    #[test]
    fn compose_two_v1_leaves_and_verify_root() {
        let left = crate::generate_stark_proof(&leaf_context("sub-a", "000"), &sample_trace());
        let right = crate::generate_stark_proof(&leaf_context("sub-b", "001"), &sample_trace());

        let root = compose_stark_proofs(
            &ComposeContext {
                parent_task_id: "parent-task",
                compose_label: "root",
                manifest_root_hash: "manifest-abc",
            },
            &left,
            &right,
            Some(&leaf_context("sub-a", "000")),
            Some(&leaf_context("sub-b", "001")),
        )
        .expect("root compose");

        assert!(verify_root_proof(
            &RootVerifyContext {
                parent_task_id: "parent-task",
                manifest_root_hash: "manifest-abc",
            },
            &root,
        ));
    }

    #[test]
    #[ignore = "slow; local only — not run in CI"]
    fn compose_builds_binary_tree() {
        let t = sample_trace();
        let leaves: Vec<_> = [
            ("sub-0", "000"),
            ("sub-1", "001"),
            ("sub-2", "010"),
            ("sub-3", "011"),
        ]
        .iter()
        .map(|(sub, slice)| crate::generate_stark_proof(&leaf_context(sub, slice), &t))
        .collect();

        let l1_0 = compose_stark_proofs(
            &ComposeContext {
                parent_task_id: "parent-task",
                compose_label: "L1:0",
                manifest_root_hash: "",
            },
            &leaves[0],
            &leaves[1],
            None,
            None,
        )
        .expect("L1:0");

        let l1_1 = compose_stark_proofs(
            &ComposeContext {
                parent_task_id: "parent-task",
                compose_label: "L1:1",
                manifest_root_hash: "",
            },
            &leaves[2],
            &leaves[3],
            None,
            None,
        )
        .expect("L1:1");

        let root = compose_stark_proofs(
            &ComposeContext {
                parent_task_id: "parent-task",
                compose_label: "root",
                manifest_root_hash: "manifest-xyz",
            },
            &l1_0,
            &l1_1,
            None,
            None,
        )
        .expect("root");

        assert!(verify_root_proof(
            &RootVerifyContext {
                parent_task_id: "parent-task",
                manifest_root_hash: "manifest-xyz",
            },
            &root,
        ));
    }

    #[test]
    fn compose_rejects_invalid_leaf() {
        let left = crate::generate_stark_proof(&leaf_context("sub-a", "000"), &sample_trace());
        let mut bad = left.clone();
        let last = bad.len() - 1;
        bad[last] ^= 0xFF;

        let err = compose_stark_proofs(
            &ComposeContext {
                parent_task_id: "parent-task",
                compose_label: "L1:0",
                manifest_root_hash: "",
            },
            &bad,
            &left,
            Some(&leaf_context("sub-a", "000")),
            Some(&leaf_context("sub-a", "000")),
        )
        .unwrap_err();
        assert!(err.contains("verification failed"));
    }
}

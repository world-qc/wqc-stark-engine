//! Proof-tree aggregation (v3 compose transcripts + R2/R3 aggregation STARKs).
//!
//! ## Model
//!
//! - **Leaf proofs** (v1/v2) are verified at node ingest before rewards.
//! - **Compose** pairs two already-valid child proofs into a v3 container.
//! - **R2**: `AggregationAir` STARK tail (digest + OK flags); never short-circuits root verify.
//! - **R3**: `RecursiveAggregationAir` V6 tail when both child PCS payloads are present.
//! - **Root verify (R3 fast path)**: RecAgg only when both sides carry verified PCS.
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
    child_aggregation_transcript, child_stark_binding, decode_leaf_pcs_bundle_bytes,
    generate_aggregation_proof, generate_recursive_aggregation_proof, parse_rec_agg_sides_v6,
    split_agg_tail, split_rec_tail, verify_agg_pcs_certificate, verify_aggregation_proof,
    verify_leaf_pcs_bundle, verify_recursive_aggregation_proof, AggregationContext, LeafPcsBundle,
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

/// Splits a `leaf:unitary_born` / `leaf:unitary_traj` v3 compose into (left, right) children.
///
/// Strips RecAgg / AggregationAir tails before decoding. Used by deferred leaf PCS so the
/// compose wrapper is not mistaken for a bare unitary v2 leaf.
pub fn split_unitary_aux_compose(proof: &[u8]) -> Option<(&[u8], &[u8])> {
    if !is_unitary_born_leaf_compose(proof) && !is_unitary_trajectory_leaf_compose(proof) {
        return None;
    }
    let v3 = leaf_compose::compose_v3_body(proof);
    let (_, left, right) = decode_compose_v3_slices(v3)?;
    Some((left, right))
}

use crate::transcript::StarkContext;
use crate::verify_stark_proof_core;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ComposeContext<'a> {
    pub parent_task_id: &'a str,
    pub compose_label: &'a str,
    pub manifest_root_hash: &'a str,
    /// Orchestrator security tier; empty → FRI default (40).
    pub security_level: &'a str,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RootVerifyContext<'a> {
    pub parent_task_id: &'a str,
    pub manifest_root_hash: &'a str,
    /// Orchestrator security tier; empty → FRI default (40).
    pub security_level: &'a str,
}

/// Verifies a single child proof (leaf or nested compose) before composition.
///
/// `security_level_fallback` is used when `leaf_ctx` is missing or has an empty
/// `security_level` (Born / trajectory children do not carry a `SEC1` tag). Callers
/// composing under a known orchestrator tier must pass [`ComposeContext::security_level`].
pub fn verify_child_proof(
    child: &[u8],
    parent_task_id: &str,
    leaf_ctx: Option<&StarkContext<'_>>,
) -> Result<(), String> {
    verify_child_proof_with_security(child, parent_task_id, leaf_ctx, "")
}

/// Like [`verify_child_proof`], with an explicit FRI-tier fallback for aux leaves.
pub fn verify_child_proof_with_security(
    child: &[u8],
    parent_task_id: &str,
    leaf_ctx: Option<&StarkContext<'_>>,
    security_level_fallback: &str,
) -> Result<(), String> {
    if child.is_empty() {
        return Err("child proof is empty".to_string());
    }
    let security_level = leaf_ctx
        .map(|c| c.security_level)
        .filter(|s| !s.is_empty())
        .unwrap_or(security_level_fallback);
    if is_trajectory_leaf_proof(child) {
        return verify_trajectory_leaf(parent_task_id, child, security_level)
            .map_err(|e| format!("trajectory leaf verification failed: {e}"));
    }
    if is_born_leaf_proof(child) {
        return verify_born_leaf(parent_task_id, child, security_level)
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
                security_level,
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
    // Prefer PI-bound SEC1; if absent, apply compose-level fallback.
    let ctx = if ctx.security_level.is_empty() && !security_level_fallback.is_empty() {
        StarkContext {
            security_level: security_level_fallback,
            ..ctx
        }
    } else {
        ctx
    };
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
    compose_stark_proofs_with_pcs(
        context,
        left_child,
        right_child,
        left_leaf_ctx,
        right_leaf_ctx,
        None,
        None,
    )
}

/// Like [`compose_stark_proofs`], but accepts optional prebuilt leaf PCS bundles.
///
/// When a prebuilt blob is `Some(non-empty)`, it is decoded and verified against the
/// corresponding child; when `None` or empty, the current prove-time PCS build runs.
pub fn compose_stark_proofs_with_pcs(
    context: &ComposeContext<'_>,
    left_child: &[u8],
    right_child: &[u8],
    left_leaf_ctx: Option<&StarkContext<'_>>,
    right_leaf_ctx: Option<&StarkContext<'_>>,
    left_prebuilt_pcs: Option<&[u8]>,
    right_prebuilt_pcs: Option<&[u8]>,
) -> Result<Vec<u8>, String> {
    if context.parent_task_id.is_empty() {
        return Err("parent_task_id is required".to_string());
    }
    verify_child_proof_with_security(
        left_child,
        context.parent_task_id,
        left_leaf_ctx,
        context.security_level,
    )?;
    verify_child_proof_with_security(
        right_child,
        context.parent_task_id,
        right_leaf_ctx,
        context.security_level,
    )?;

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
            security_level: context.security_level,
        };
        let agg_proof = generate_aggregation_proof(&agg_ctx)
            .map_err(|e| format!("aggregation STARK prove failed: {e}"))?;
        out = append_agg_tail(out, &agg_proof);

        let left_bind = child_stark_binding(left_child);
        let right_bind = child_stark_binding(right_child);
        let left_pcs = pcs_for_child(left_child, context.parent_task_id, left_prebuilt_pcs)?;
        let right_pcs = pcs_for_child(right_child, context.parent_task_id, right_prebuilt_pcs)?;
        log_child_pcs_sizes("left", &left_pcs);
        log_child_pcs_sizes("right", &right_pcs);

        // RecAgg AIR asserts pcs_ok=1; only attach V6 when both sides carry verified PCS.
        // Otherwise keep R2 AggregationAir and rely on the audit walk for child validity.
        if pcs_side_complete(&left_pcs) && pcs_side_complete(&right_pcs) {
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
                security_level: context.security_level,
            };
            let rec_proof = generate_recursive_aggregation_proof(&rec_ctx)
                .map_err(|e| format!("R3-M2 recursive aggregation STARK prove failed: {e}"))?;
            out = append_rec_tail(out, &rec_proof);
        } else {
            eprintln!(
                "[Aggregation] skipping RecAgg V6: leaf/agg PCS incomplete on one or both children"
            );
        }
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
        for (i, cert) in bundle.certs.iter().enumerate() {
            let g = &cert.mmcs_groups;
            let fmt = |label: &str, gs: &[crate::plonky3_stark::recursion::MmcsGroupFoldProof]| {
                if gs.is_empty() {
                    return;
                }
                let sizes: Vec<String> = gs
                    .iter()
                    .map(|x| {
                        format!(
                            "n={} d={} w={} stark={}",
                            x.path_count(),
                            x.depth(),
                            x.leaf_width(),
                            x.group_stark_len()
                        )
                    })
                    .collect();
                eprintln!(
                    "[M4c size]   cert{i} {label}: {} group(s) [{}]",
                    gs.len(),
                    sizes.join("; ")
                );
            };
            fmt("val_trace", &g.val_trace);
            fmt("val_quot", &g.val_quot);
            fmt("val_quot_batch", &g.val_quot_batch);
            fmt("chal_first_layer", &g.chal_first_layer);
            fmt("chal_commit", &g.chal_commit);
            if g.pcs_combined {
                eprintln!("[M4c size]   cert{i} pcs_combined=true (val+chal in val_trace)");
            }
            let xs = &cert.fri_fold_groups.fold_xs_by_log_h;
            eprintln!(
                "[M4c size]   cert{i} fri_fold: y={} xs={} (log_h={:?})",
                cert.fri_fold_groups
                    .fold_ys
                    .as_ref()
                    .map(|y| y.group_stark.len())
                    .unwrap_or(0),
                xs.iter().map(|x| x.group_stark.len()).sum::<usize>(),
                xs.iter().map(|x| x.log_folded_height).collect::<Vec<_>>(),
            );
        }
    } else if pcs.agg_cert.is_some() {
        eprintln!("[M4c size] compose {side} agg PCS present (nested)");
    } else {
        eprintln!("[M4c size] compose {side} PCS absent (RecAgg skipped)");
    }
}

#[cfg(feature = "plonky3-stark")]
fn pcs_side_complete(pcs: &ChildPcs) -> bool {
    match pcs.kind {
        k if k == REC_KIND_AGG => pcs.agg_cert.is_some(),
        k if k == REC_KIND_LEAF => pcs.leaf_bundle.is_some(),
        _ => false,
    }
}

#[cfg(feature = "plonky3-stark")]
fn rec_context_pcs_complete(ctx: &RecursiveAggregationContext<'_>) -> bool {
    let left_ok = if ctx.left_kind == REC_KIND_AGG {
        ctx.left_agg_cert.is_some()
    } else {
        ctx.left_leaf_bundle.is_some()
    };
    let right_ok = if ctx.right_kind == REC_KIND_AGG {
        ctx.right_agg_cert.is_some()
    } else {
        ctx.right_leaf_bundle.is_some()
    };
    left_ok && right_ok
}

#[cfg(feature = "plonky3-stark")]
fn pcs_for_child(
    child: &[u8],
    _parent_task_id: &str,
    prebuilt_pcs: Option<&[u8]>,
) -> Result<ChildPcs, String> {
    if let Some(agg) = child_aggregation_transcript(child) {
        let cert = pcs_opening_for_child_agg(agg)?;
        return Ok(ChildPcs {
            kind: REC_KIND_AGG,
            agg_cert: Some(cert),
            leaf_bundle: None,
        });
    }

    if let Some(bytes) = prebuilt_pcs {
        if !bytes.is_empty() {
            let bundle = decode_leaf_pcs_bundle_bytes(bytes)
                .ok_or_else(|| "prebuilt leaf PCS bundle decode failed".to_string())?;
            verify_leaf_pcs_bundle(child, &bundle)
                .map_err(|e| format!("prebuilt leaf PCS bundle verify failed: {e}"))?;
            eprintln!(
                "[Aggregation] using prebuilt leaf PCS bundle ({} bytes)",
                bytes.len()
            );
            return Ok(ChildPcs {
                kind: REC_KIND_LEAF,
                agg_cert: None,
                leaf_bundle: Some(bundle),
            });
        }
    }

    if child_supports_leaf_pcs(child) {
        let bundle = build_leaf_pcs_bundle_from_child(child)
            .map_err(|e| format!("leaf PCS bundle build failed: {e}"))?;
        verify_leaf_pcs_bundle(child, &bundle)
            .map_err(|e| format!("leaf PCS bundle verify failed: {e}"))?;
        eprintln!(
            "[Aggregation] built leaf PCS bundle fallback (certs={})",
            bundle.certs.len()
        );
        return Ok(ChildPcs {
            kind: REC_KIND_LEAF,
            agg_cert: None,
            leaf_bundle: Some(bundle),
        });
    }

    // Leaf types without a PCS builder (e.g. legacy v1 AIR) — RecAgg must not claim pcs_ok.
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
    // Only Plonky3 v2 unitary leaves can build leaf PCS; v1 AIR has no Circle PCS payload.
    base.windows(crate::V2_MARKER.len())
        .any(|w| w == crate::V2_MARKER)
}

#[cfg(feature = "plonky3-stark")]
fn pcs_opening_for_child_agg(
    agg: &[u8],
) -> Result<crate::plonky3_stark::AggPcsCertificate, String> {
    use crate::plonky3_stark::parse_agg_v4_header_any;

    let header = parse_agg_v4_header_any(agg)
        .ok_or_else(|| "cannot parse child AggregationAir V4 header".to_string())?;
    let agg_ctx = AggregationContext {
        parent_task_id: header.parent_task_id.as_str(),
        compose_label: header.compose_label.as_str(),
        manifest_root_hash: header.manifest_root_hash.as_str(),
        left_child_hash: header.left_child_hash,
        right_child_hash: header.right_child_hash,
        security_level: "",
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

    verify_child_proof_with_security(
        &left_child,
        context.parent_task_id,
        None,
        context.security_level,
    )?;
    verify_child_proof_with_security(
        &right_child,
        context.parent_task_id,
        None,
        context.security_level,
    )?;

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
            Some(rec_bytes),
            context.security_level,
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
            security_level: context.security_level,
        };
        if !verify_aggregation_proof(&agg_ctx, agg_bytes) {
            return Err("aggregation STARK verification failed".to_string());
        }
    }

    Ok(())
}

/// Rebuilds R3 recursive aggregation context (PCS certs / leaf bundles) for two children.
///
/// Prefer [`recursive_context_for_children_with_proof`] when a RecAgg V6 transcript is
/// available so embedded leaf/agg PCS can be reused instead of re-proved.
#[cfg(feature = "plonky3-stark")]
#[allow(clippy::too_many_arguments)]
pub fn recursive_context_for_children<'a>(
    parent_task_id: &'a str,
    compose_label: &'a str,
    manifest_root_hash: &'a str,
    left_child_hash: [u8; CHILD_HASH_LEN],
    right_child_hash: [u8; CHILD_HASH_LEN],
    left_child: &'a [u8],
    right_child: &'a [u8],
    security_level: &'a str,
) -> Result<RecursiveAggregationContext<'a>, String> {
    rebuild_rec_context(
        parent_task_id,
        compose_label,
        manifest_root_hash,
        left_child_hash,
        right_child_hash,
        left_child,
        right_child,
        None,
        security_level,
    )
}

/// Like [`recursive_context_for_children`], but reuses PCS payloads embedded in `rec_bytes`.
#[cfg(feature = "plonky3-stark")]
#[allow(clippy::too_many_arguments)]
pub fn recursive_context_for_children_with_proof<'a>(
    parent_task_id: &'a str,
    compose_label: &'a str,
    manifest_root_hash: &'a str,
    left_child_hash: [u8; CHILD_HASH_LEN],
    right_child_hash: [u8; CHILD_HASH_LEN],
    left_child: &'a [u8],
    right_child: &'a [u8],
    rec_bytes: &[u8],
    security_level: &'a str,
) -> Result<RecursiveAggregationContext<'a>, String> {
    rebuild_rec_context(
        parent_task_id,
        compose_label,
        manifest_root_hash,
        left_child_hash,
        right_child_hash,
        left_child,
        right_child,
        Some(rec_bytes),
        security_level,
    )
}

#[cfg(feature = "plonky3-stark")]
#[allow(clippy::too_many_arguments)]
fn rebuild_rec_context<'a>(
    parent_task_id: &'a str,
    compose_label: &'a str,
    manifest_root_hash: &'a str,
    left_child_hash: [u8; CHILD_HASH_LEN],
    right_child_hash: [u8; CHILD_HASH_LEN],
    left_child: &'a [u8],
    right_child: &'a [u8],
    rec_bytes: Option<&[u8]>,
    security_level: &'a str,
) -> Result<RecursiveAggregationContext<'a>, String> {
    let left_bind = child_stark_binding(left_child);
    let right_bind = child_stark_binding(right_child);

    if let Some(rec) = rec_bytes {
        if let Some(sides) = parse_rec_agg_sides_v6(rec) {
            if sides.parent_task_id != parent_task_id {
                return Err(format!(
                    "rec-agg parent_task_id mismatch: {} != {}",
                    sides.parent_task_id, parent_task_id
                ));
            }
            if sides.compose_label != compose_label {
                return Err(format!(
                    "rec-agg compose_label mismatch: {} != {}",
                    sides.compose_label, compose_label
                ));
            }
            if sides.manifest_root_hash != manifest_root_hash {
                return Err("rec-agg manifest_root_hash mismatch".to_string());
            }
            if sides.left_child_hash != left_child_hash
                || sides.right_child_hash != right_child_hash
            {
                return Err("rec-agg child hash mismatch".to_string());
            }
            if sides.left_stark_digest != left_bind.stark_digest
                || sides.right_stark_digest != right_bind.stark_digest
            {
                return Err("rec-agg child stark digest mismatch".to_string());
            }

            let left_pcs = pcs_from_embedded_or_build(
                left_child,
                sides.left_kind,
                sides.left_leaf_bundle,
                sides.left_agg_cert,
            )?;
            let right_pcs = pcs_from_embedded_or_build(
                right_child,
                sides.right_kind,
                sides.right_leaf_bundle,
                sides.right_agg_cert,
            )?;
            return Ok(RecursiveAggregationContext {
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
                security_level,
            });
        } else {
            eprintln!(
                "[Aggregation] parse_rec_agg_sides_v6 failed (rec_len={}); falling back to rebuild PCS",
                rec.len()
            );
            if let Err(reason) = crate::plonky3_stark::diagnose_parse_rec_agg_sides_v6(rec) {
                eprintln!("[Aggregation] parse_rec_agg_sides_v6 diagnose: {reason}");
            }
        }
    }

    let left_pcs = pcs_for_child(left_child, parent_task_id, None)?;
    let right_pcs = pcs_for_child(right_child, parent_task_id, None)?;
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
        security_level,
    })
}

/// Prefer PCS already carried in the RecAgg V6 transcript; only rebuild as last resort.
#[cfg(feature = "plonky3-stark")]
fn pcs_from_embedded_or_build(
    child: &[u8],
    kind: u8,
    embedded_leaf: Option<LeafPcsBundle>,
    embedded_agg: Option<crate::plonky3_stark::AggPcsCertificate>,
) -> Result<ChildPcs, String> {
    use crate::plonky3_stark::parse_agg_v4_header_any;

    if let Some(agg) = child_aggregation_transcript(child) {
        if kind != REC_KIND_AGG {
            return Err(format!(
                "rec-agg kind={kind} but child is nested AggregationAir"
            ));
        }
        if let Some(cert) = embedded_agg {
            let header = parse_agg_v4_header_any(agg)
                .ok_or_else(|| "cannot parse child AggregationAir V4 header".to_string())?;
            let agg_ctx = AggregationContext {
                parent_task_id: header.parent_task_id.as_str(),
                compose_label: header.compose_label.as_str(),
                manifest_root_hash: header.manifest_root_hash.as_str(),
                left_child_hash: header.left_child_hash,
                right_child_hash: header.right_child_hash,
                security_level: "",
            };
            if !verify_agg_pcs_certificate(&agg_ctx, agg, &cert) {
                return Err("embedded AggregationAir PCS certificate verify failed".to_string());
            }
            eprintln!("[Aggregation] using embedded agg PCS certificate from rec-agg proof");
            return Ok(ChildPcs {
                kind: REC_KIND_AGG,
                agg_cert: Some(cert),
                leaf_bundle: None,
            });
        }
        let cert = pcs_opening_for_child_agg(agg)?;
        return Ok(ChildPcs {
            kind: REC_KIND_AGG,
            agg_cert: Some(cert),
            leaf_bundle: None,
        });
    }

    if kind != REC_KIND_LEAF {
        return Err(format!("rec-agg kind={kind} but child is a leaf STARK"));
    }
    if let Some(bundle) = embedded_leaf {
        verify_leaf_pcs_bundle(child, &bundle)
            .map_err(|e| format!("embedded leaf PCS bundle verify failed: {e}"))?;
        eprintln!(
            "[Aggregation] using embedded leaf PCS bundle from rec-agg proof ({} certs)",
            bundle.certs.len()
        );
        return Ok(ChildPcs {
            kind: REC_KIND_LEAF,
            agg_cert: None,
            leaf_bundle: Some(bundle),
        });
    }

    // True fallback: transcript had no reusable side payload.
    pcs_for_child(child, "", None)
}

/// Verifies a task root proof tree.
///
/// With `plonky3-stark`, tries the R3 recursive aggregation STARK fast path first
/// when both child PCS payloads are present and verified, then falls through to the
/// v3 audit walk (which always re-checks embedded children). R2 AggregationAir alone
/// never short-circuits past the audit walk.
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
                        Some(rec_bytes),
                        context.security_level,
                    ) {
                        Ok(rec_ctx) => {
                            if !rec_context_pcs_complete(&rec_ctx) {
                                eprintln!(
                                    "[Aggregation] Root R3 PCS incomplete; falling back to audit walk"
                                );
                            } else if verify_recursive_aggregation_proof(&rec_ctx, rec_bytes) {
                                eprintln!(
                                    "[Aggregation] Root proof verified (R3-M2 fast path) for task {}",
                                    context.parent_task_id
                                );
                                return true;
                            } else {
                                eprintln!(
                                    "[Aggregation] Root R3-M2 STARK failed; falling back to audit walk"
                                );
                            }
                        }
                        Err(e) => {
                            eprintln!("[Aggregation] Root R3-M2 context rebuild failed: {e}");
                        }
                    }
                }
            }
        }

        // Legacy R2 AggregationAir: digest attestation only — never skip the child audit walk.
        if let Some((v3_part, agg_bytes)) = split_agg_tail(proof) {
            if let Some((header, _, _)) = decode_compose_v3(v3_part) {
                if header.compose_label == "root" {
                    let agg_ctx = AggregationContext {
                        parent_task_id: context.parent_task_id,
                        compose_label: "root",
                        manifest_root_hash: context.manifest_root_hash,
                        left_child_hash: header.left_child_hash,
                        right_child_hash: header.right_child_hash,
                        security_level: context.security_level,
                    };
                    if !context.manifest_root_hash.is_empty()
                        && header.manifest_root_hash != context.manifest_root_hash
                    {
                        eprintln!("[Aggregation] Failed: manifest_root_hash mismatch");
                        return false;
                    }
                    if !verify_aggregation_proof(&agg_ctx, agg_bytes) {
                        eprintln!(
                            "[Aggregation] Root aggregation STARK failed; continuing to audit walk"
                        );
                    } else {
                        eprintln!(
                            "[Aggregation] Root R2 AggregationAir ok; continuing to audit walk for child proofs"
                        );
                    }
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
        security_level: context.security_level,
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
            security_level: "",
        }
    }

    fn sample_trace() -> Vec<f64> {
        crate::trace_spec::idle_qubit0_trace()
    }

    #[test]
    fn split_unitary_aux_compose_born_and_traj_labels() {
        let left = b"left-unitary-bytes";
        let right = b"right-aux-bytes";
        let born = encode_compose_v3("sub-born", UNITARY_BORN_COMPOSE_LABEL, "", left, right);
        let (l, r) = split_unitary_aux_compose(&born).expect("born split");
        assert_eq!(l, left.as_slice());
        assert_eq!(r, right.as_slice());

        let traj = encode_compose_v3("sub-traj", UNITARY_TRAJ_COMPOSE_LABEL, "", left, right);
        let (l, r) = split_unitary_aux_compose(&traj).expect("traj split");
        assert_eq!(l, left.as_slice());
        assert_eq!(r, right.as_slice());

        let root = encode_compose_v3("parent", "root", "m", left, right);
        assert!(split_unitary_aux_compose(&root).is_none());
    }

    #[cfg(feature = "plonky3-stark")]
    #[test]
    fn compose_unitary_born_respects_low_security_level() {
        use crate::distribution::{calculate_probability_digest, BornBinding};
        use crate::generate_plonky3_stark_proof;
        use crate::plonky3_stark::{generate_born_stark_proof, BornStarkContext};

        let inv_sqrt2 = 1.0f64 / 2.0f64.sqrt();
        let sv = vec![(inv_sqrt2, 0.0), (0.0, 0.0), (0.0, 0.0), (inv_sqrt2, 0.0)];
        let probs = vec![("00".into(), 0.5), ("11".into(), 0.5)];
        let binding = BornBinding::from_specs(2, 2, &[(0, 0), (1, 1)], sv).expect("bind");
        let segment = crate::distribution::DistributionSegment {
            sample_seed: 42,
            shots: 128,
            measurement_spec_hash: String::new(),
            probability_digest: calculate_probability_digest(&probs),
            probabilities: probs,
            born_binding: Some(binding),
        };
        let link = segment
            .born_binding
            .as_ref()
            .unwrap()
            .terminal_statevector_digest
            .clone();
        let link_ref: &str = Box::leak(link.into_boxed_str());
        let ctx = StarkContext {
            circuit_id: "circuit-bell",
            sub_task_id: "sub-born-low",
            node_id: "node-1",
            slice_id: "0",
            output_hash: "counts-hash",
            terminal_statevector_digest: link_ref,
            measurement_spec_hash: "",
            security_level: "low",
        };
        let unitary =
            generate_plonky3_stark_proof(&ctx, &crate::trace_spec::golden_h_q0_trace()).expect("u");
        let born_ctx = BornStarkContext {
            sub_task_id: "sub-born-low",
            probability_digest: &segment.probability_digest,
            terminal_statevector_digest: link_ref,
            security_level: "low",
        };
        let born_inner = generate_born_stark_proof(&born_ctx, &segment).expect("born");
        let composed = compose_unitary_born_leaf(&ctx, &unitary, &segment, &born_inner)
            .expect("compose must keep low FRI tier on Born re-verify");

        // Deferred /leaf_pcs receives the full unitary_born compose, not bare children.
        let bundle = crate::plonky3_stark::build_leaf_pcs_bundle_from_child(&composed)
            .expect("leaf PCS from unitary_born compose");
        assert!(bundle.certs.len() >= 2, "expected unitary+born certs");
        crate::plonky3_stark::verify_leaf_pcs_bundle(&composed, &bundle)
            .expect("verify leaf PCS against compose");
    }

    #[cfg(feature = "plonky3-stark")]
    #[test]
    fn verify_child_born_uses_compose_security_fallback() {
        use crate::distribution::{calculate_probability_digest, BornBinding};
        use crate::plonky3_stark::{generate_born_stark_proof, BornStarkContext};

        let inv_sqrt2 = 1.0f64 / 2.0f64.sqrt();
        let sv = vec![(inv_sqrt2, 0.0), (0.0, 0.0), (0.0, 0.0), (inv_sqrt2, 0.0)];
        let probs = vec![("00".into(), 0.5), ("11".into(), 0.5)];
        let binding = BornBinding::from_specs(2, 2, &[(0, 0), (1, 1)], sv).expect("bind");
        let segment = crate::distribution::DistributionSegment {
            sample_seed: 7,
            shots: 64,
            measurement_spec_hash: "spec".into(),
            probability_digest: calculate_probability_digest(&probs),
            probabilities: probs,
            born_binding: Some(binding),
        };
        let link = segment
            .born_binding
            .as_ref()
            .unwrap()
            .terminal_statevector_digest
            .as_str();
        let born_ctx = BornStarkContext {
            sub_task_id: "sub-born-fb",
            probability_digest: &segment.probability_digest,
            terminal_statevector_digest: link,
            security_level: "low",
        };
        let born_inner = generate_born_stark_proof(&born_ctx, &segment).expect("born");
        let child = encode_born_leaf("sub-born-fb", &segment, Some(&born_inner));

        verify_child_proof_with_security(&child, "sub-born-fb", None, "low")
            .expect("fallback low must verify");
        assert!(
            verify_child_proof_with_security(&child, "sub-born-fb", None, "").is_err(),
            "empty fallback must expect 40 queries and reject low proof"
        );
    }

    #[test]
    #[ignore = "slow; local only — not run in CI"]
    fn compose_two_leaves_low_security_and_verify_root() {
        let left_ctx = StarkContext {
            circuit_id: "c",
            sub_task_id: "sub-a",
            node_id: "n1",
            slice_id: "000",
            output_hash: "out",
            terminal_statevector_digest: "",
            measurement_spec_hash: "",
            security_level: "low",
        };
        let right_ctx = StarkContext {
            circuit_id: "c",
            sub_task_id: "sub-b",
            node_id: "n1",
            slice_id: "001",
            output_hash: "out",
            terminal_statevector_digest: "",
            measurement_spec_hash: "",
            security_level: "low",
        };
        let left = crate::generate_stark_proof(&left_ctx, &sample_trace());
        let right = crate::generate_stark_proof(&right_ctx, &sample_trace());

        let root = compose_stark_proofs(
            &ComposeContext {
                parent_task_id: "parent-task",
                compose_label: "root",
                manifest_root_hash: "manifest-abc",
                security_level: "low",
            },
            &left,
            &right,
            Some(&left_ctx),
            Some(&right_ctx),
        )
        .expect("root compose");

        assert!(verify_root_proof(
            &RootVerifyContext {
                parent_task_id: "parent-task",
                manifest_root_hash: "manifest-abc",
                security_level: "low",
            },
            &root,
        ));
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
                security_level: "",
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
                security_level: "",
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
                security_level: "",
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
                security_level: "",
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
                security_level: "",
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
                security_level: "",
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
                security_level: "",
            },
            &bad,
            &left,
            Some(&leaf_context("sub-a", "000")),
            Some(&leaf_context("sub-a", "000")),
        )
        .unwrap_err();
        assert!(err.contains("verification failed"));
    }

    #[cfg(feature = "plonky3-stark")]
    #[test]
    #[ignore = "slow; local only — not run in CI"]
    fn compose_with_prebuilt_leaf_pcs_bundles() {
        use crate::generate_plonky3_stark_proof;
        use crate::plonky3_stark::build_encoded_leaf_pcs_bundle_from_child;

        let left_ctx = leaf_context("sub-pre-l", "000");
        let right_ctx = leaf_context("sub-pre-r", "001");
        let left = generate_plonky3_stark_proof(&left_ctx, &sample_trace()).expect("left prove");
        let right = generate_plonky3_stark_proof(&right_ctx, &sample_trace()).expect("right prove");
        let left_pcs = build_encoded_leaf_pcs_bundle_from_child(&left).expect("left pcs");
        let right_pcs = build_encoded_leaf_pcs_bundle_from_child(&right).expect("right pcs");

        let root = compose_stark_proofs_with_pcs(
            &ComposeContext {
                parent_task_id: "parent-prebuilt",
                compose_label: "root",
                manifest_root_hash: "manifest-prebuilt",
                security_level: "",
            },
            &left,
            &right,
            Some(&left_ctx),
            Some(&right_ctx),
            Some(left_pcs.as_slice()),
            Some(right_pcs.as_slice()),
        )
        .expect("compose with prebuilt pcs");

        assert!(verify_root_proof(
            &RootVerifyContext {
                parent_task_id: "parent-prebuilt",
                manifest_root_hash: "manifest-prebuilt",
                security_level: "",
            },
            &root,
        ));
    }
}

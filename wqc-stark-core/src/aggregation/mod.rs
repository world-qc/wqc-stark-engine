//! Proof-tree aggregation (v3 compose transcripts + R2 AggregationAir).
//!
//! ## Model
//!
//! - **Leaf proofs** (v1/v2) are verified at node ingest before rewards.
//! - **Compose** pairs two already-valid child proofs into a v3 container.
//! - **R2**: each compose step also emits an `AggregationAir` STARK tail binding child digests.
//! - **Root verify (fast path)**: single aggregation STARK verify at the root (O(1) STARK).
//! - **Root verify (audit)**: walks the v3 tree and re-checks every leaf STARK.

mod leaf;
mod transcript_v3;

#[cfg(feature = "plonky3-stark")]
use crate::plonky3_stark::{
    append_agg_tail, generate_aggregation_proof, verify_aggregation_proof, AggregationContext,
    split_agg_tail,
};

pub use leaf::{parse_leaf_binding, parsed_to_stark_context, ParsedLeafBinding};
pub use transcript_v3::{
    child_digest, decode_compose_v3, encode_compose_v3, is_compose_v3, ComposeHeader,
    CHILD_HASH_LEN, V3_COMPOSE_MARKER,
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
    if is_compose_v3(child) {
        return verify_composed_proof(
            &ComposeContext {
                parent_task_id,
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

    let parsed = parse_leaf_binding(child)
        .ok_or_else(|| "cannot parse leaf public inputs".to_string())?;
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
    }

    Ok(out)
}

/// Recursively verifies a v3 compose tree (all embedded leaves).
pub fn verify_composed_proof(context: &ComposeContext<'_>, proof: &[u8]) -> Result<(), String> {
    #[cfg(feature = "plonky3-stark")]
    let (v3_proof, agg_tail) = match split_agg_tail(proof) {
        Some((v3, agg)) => (v3, Some(agg)),
        None => (proof, None),
    };
    #[cfg(not(feature = "plonky3-stark"))]
    let v3_proof = proof;

    if !is_compose_v3(v3_proof) {
        return Err("not a v3 compose proof".to_string());
    }

    let (header, left_child, right_child) = decode_compose_v3(v3_proof).ok_or_else(|| {
        "malformed v3 compose transcript".to_string()
    })?;

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
    if let Some(agg_bytes) = agg_tail {
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

/// Verifies a task root proof tree.
///
/// With `plonky3-stark`, tries the R2 aggregation STARK fast path first (single STARK verify).
/// Falls back to the v3 audit walk when no aggregation tail is present.
pub fn verify_root_proof(context: &RootVerifyContext<'_>, proof: &[u8]) -> bool {
    if context.parent_task_id.is_empty() {
        eprintln!("[Aggregation] Failed: parent_task_id is empty");
        return false;
    }

    #[cfg(feature = "plonky3-stark")]
    {
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
                    eprintln!("[Aggregation] Root aggregation STARK failed; falling back to audit walk");
                }
            }
        }
    }

    if !is_compose_v3(proof) {
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

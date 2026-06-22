//! Proof-tree aggregation (v3 compose transcripts).
//!
//! ## Model
//!
//! - **Leaf proofs** (v1/v2) are verified at node ingest before rewards.
//! - **Compose** pairs two already-valid child proofs into a v3 container.
//! - **Root verify** walks the tree recursively and re-checks every leaf STARK.
//!
//! Phase 4 (future): replace v3 containers with true recursive Plonky3 proofs
//! (`AggregationAir`) so root verification is O(log² N) on a single STARK.

mod leaf;
mod transcript_v3;

pub use leaf::{parse_leaf_binding, parsed_to_stark_context, ParsedLeafBinding};
pub use transcript_v3::{
    child_digest, decode_compose_v3, encode_compose_v3, is_compose_v3, ComposeHeader,
    V3_COMPOSE_MARKER,
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

    Ok(encode_compose_v3(
        context.parent_task_id,
        context.compose_label,
        context.manifest_root_hash,
        left_child,
        right_child,
    ))
}

/// Recursively verifies a v3 compose tree (all embedded leaves).
pub fn verify_composed_proof(context: &ComposeContext<'_>, proof: &[u8]) -> Result<(), String> {
    if !is_compose_v3(proof) {
        return Err("not a v3 compose proof".to_string());
    }

    let (header, left_child, right_child) = decode_compose_v3(proof).ok_or_else(|| {
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
    Ok(())
}

/// Verifies a task root proof tree (v3 at top level).
pub fn verify_root_proof(context: &RootVerifyContext<'_>, proof: &[u8]) -> bool {
    if context.parent_task_id.is_empty() {
        eprintln!("[Aggregation] Failed: parent_task_id is empty");
        return false;
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
                "[Aggregation] Root proof verified for task {}",
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
        }
    }

    fn sample_trace() -> Vec<f64> {
        vec![0.0, 0.0, 0.0, 1.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0]
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

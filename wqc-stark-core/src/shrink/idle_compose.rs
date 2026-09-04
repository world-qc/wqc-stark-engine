//! Idle two-leaf root compose with leaf PCS + RecAgg V6 (E5b shrink benchmark path).

use crate::aggregation::{compose_stark_proofs_with_pcs, ComposeContext, RootVerifyContext};
use crate::plonky3_stark::{
    build_encoded_leaf_pcs_bundle_from_child, has_rec_tail, split_rec_tail,
};
use crate::trace_spec;
use crate::transcript::StarkContext;
use crate::{generate_plonky3_stark_proof, verify_root_proof};

/// Report from the standard E5b shrink benchmark compose.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IdleTwoLeafComposeReport {
    pub root_bytes: usize,
    pub left_leaf_bytes: usize,
    pub right_leaf_bytes: usize,
    pub left_pcs_bytes: usize,
    pub right_pcs_bytes: usize,
    pub has_rec_agg_tail: bool,
}

fn idle_leaf_context<'a>(
    sub_task_id: &'static str,
    slice_id: &'static str,
    security_level: &'a str,
) -> StarkContext<'a> {
    StarkContext {
        circuit_id: "e5b-shrink-idle",
        sub_task_id,
        node_id: "node-shrink-1",
        slice_id,
        output_hash: "out-shrink",
        terminal_statevector_digest: "",
        measurement_spec_hash: "",
        security_level,
    }
}

/// Builds the canonical **idle two-leaf** root with prebuilt leaf PCS bundles (RecAgg V6 when PCS complete).
///
/// This is the path tracked for E5b shrink KPI (`root.bin` pre-wrap size).
pub fn compose_idle_two_leaf_root_with_pcs(
    security_level: &str,
) -> Result<IdleTwoLeafComposeReport, String> {
    compose_idle_two_leaf_root_with_pcs_and_bytes(security_level).map(|(report, _)| report)
}

/// Same as [`compose_idle_two_leaf_root_with_pcs`] but also returns root proof bytes (for fixture export).
pub fn compose_idle_two_leaf_root_with_pcs_and_bytes(
    security_level: &str,
) -> Result<(IdleTwoLeafComposeReport, Vec<u8>), String> {
    let left_ctx = idle_leaf_context("sub-shrink-a", "000", security_level);
    let right_ctx = idle_leaf_context("sub-shrink-b", "001", security_level);
    let trace = trace_spec::idle_qubit0_trace();

    let left = generate_plonky3_stark_proof(&left_ctx, &trace)?;
    let right = generate_plonky3_stark_proof(&right_ctx, &trace)?;
    let left_pcs = build_encoded_leaf_pcs_bundle_from_child(&left)?;
    let right_pcs = build_encoded_leaf_pcs_bundle_from_child(&right)?;

    let compose_ctx = ComposeContext {
        parent_task_id: "e5b-shrink-parent",
        compose_label: "root",
        manifest_root_hash: "manifest-e5b-shrink",
        security_level,
    };

    let root = compose_stark_proofs_with_pcs(
        &compose_ctx,
        &left,
        &right,
        Some(&left_ctx),
        Some(&right_ctx),
        Some(left_pcs.as_slice()),
        Some(right_pcs.as_slice()),
    )?;

    let verify_ctx = RootVerifyContext {
        parent_task_id: compose_ctx.parent_task_id,
        manifest_root_hash: compose_ctx.manifest_root_hash,
        security_level: compose_ctx.security_level,
    };
    if !verify_root_proof(&verify_ctx, &root) {
        return Err("idle two-leaf root verify failed".to_string());
    }

    Ok((
        IdleTwoLeafComposeReport {
            root_bytes: root.len(),
            left_leaf_bytes: left.len(),
            right_leaf_bytes: right.len(),
            left_pcs_bytes: left_pcs.len(),
            right_pcs_bytes: right_pcs.len(),
            has_rec_agg_tail: has_rec_tail(&root),
        },
        root,
    ))
}

/// R2-only path lives in [`crate::shrink::compose_idle_two_leaf_root_r2_only`].
pub fn rec_agg_tail_bytes(proof: &[u8]) -> Option<usize> {
    split_rec_tail(proof).map(|(_, tail)| tail.len())
}

//! R2-only idle two-leaf compose (AggregationAir tail, no RecAgg V6). Fast E5b CI smoke.

use crate::aggregation::{
    compose_stark_proofs, verify_root_proof, ComposeContext, RootVerifyContext,
};
use crate::generate_stark_proof;
use crate::trace_spec;
use crate::transcript::StarkContext;

fn idle_leaf_context(sub_task_id: &'static str, slice_id: &'static str) -> StarkContext<'static> {
    StarkContext {
        circuit_id: "e5b-shrink-idle",
        sub_task_id,
        node_id: "node-shrink-1",
        slice_id,
        output_hash: "out-shrink",
        terminal_statevector_digest: "",
        measurement_spec_hash: "",
        security_level: "",
    }
}

/// R2-only idle two-leaf compose (AggregationAir tail, **no** RecAgg V6). Fast CI smoke.
pub fn compose_idle_two_leaf_root_r2_only() -> Result<usize, String> {
    let left_ctx = idle_leaf_context("sub-r2-a", "000");
    let right_ctx = idle_leaf_context("sub-r2-b", "001");
    let trace = trace_spec::idle_qubit0_trace();
    let left = generate_stark_proof(&left_ctx, &trace);
    let right = generate_stark_proof(&right_ctx, &trace);

    let root = compose_stark_proofs(
        &ComposeContext {
            parent_task_id: "e5b-r2-parent",
            compose_label: "root",
            manifest_root_hash: "manifest-e5b-r2",
            security_level: "",
        },
        &left,
        &right,
        Some(&left_ctx),
        Some(&right_ctx),
    )?;

    let verify_ctx = RootVerifyContext {
        parent_task_id: "e5b-r2-parent",
        manifest_root_hash: "manifest-e5b-r2",
        security_level: "",
    };
    if !verify_root_proof(&verify_ctx, &root) {
        return Err("R2 idle two-leaf root verify failed".to_string());
    }
    Ok(root.len())
}

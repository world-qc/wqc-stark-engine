//! Idle leaf PCS — Poseidon2 Mmcs group size benchmark vs Keccak baseline.

use crate::plonky3_stark::recursion::benchmark_poseidon_mmcs_from_child;
use crate::plonky3_stark::recursion::PoseidonMmcsBenchmarkReport;
use crate::trace_spec;
use crate::transcript::StarkContext;
use crate::generate_plonky3_stark_proof;

/// Reference row from `fixtures/e5b/sweep.json` (`low/chunk24`).
pub const SWEEP_REF_LABEL: &str = "low/chunk24";
pub const SWEEP_REF_ROOT_BYTES: u64 = 5_022_410;
pub const SWEEP_REF_LEFT_PCS_BYTES: u64 = 2_499_954;
pub const SWEEP_REF_MMCS_GROUPS_PER_SIDE: u64 = 2_400_773;

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct IdleLeafPoseidonMmcsReport {
    pub security_level: String,
    pub leaf_pcs_bytes: usize,
    pub mmcs_groups_stark_bytes_keccak: u64,
    pub mmcs_groups_stark_bytes_poseidon_estimate: u64,
    pub mmcs_groups_stark_saved_bytes: i64,
    pub leaf_pcs_poseidon_estimate_bytes: i64,
    pub poseidon: PoseidonMmcsBenchmarkReport,
    pub reference_sweep_label: String,
    pub reference_keccak_root_bytes: u64,
    pub reference_mmcs_groups_per_side: u64,
}

fn idle_leaf_context(sub_task_id: &'static str, security_level: &'static str) -> StarkContext<'static> {
    StarkContext {
        circuit_id: "e5b-shrink-idle",
        sub_task_id,
        node_id: "node-shrink-1",
        slice_id: "000",
        output_hash: "out-shrink",
        terminal_statevector_digest: "",
        measurement_spec_hash: "",
        security_level,
    }
}

/// Prove one idle leaf PCS and compare Keccak vs Poseidon2 group STARK bytes.
pub fn benchmark_idle_leaf_poseidon_mmcs(
    security_level: &str,
) -> Result<IdleLeafPoseidonMmcsReport, String> {
    let level: &'static str = match security_level {
        "" => "",
        "low" => "low",
        "normal" => "normal",
        "high" => "high",
        "ultra" => "ultra",
        other => return Err(format!("unsupported security_level {other}")),
    };
    let ctx = idle_leaf_context("sub-poseidon-bench", level);
    let trace = trace_spec::idle_qubit0_trace();
    let transcript = generate_plonky3_stark_proof(&ctx, &trace)?;
    let (leaf_pcs_bytes, poseidon) = benchmark_poseidon_mmcs_from_child(&transcript, &ctx)?;

    let keccak_mmcs = poseidon.keccak_total;
    let poseidon_mmcs = poseidon.poseidon_total_estimate;
    let saved = keccak_mmcs as i64 - poseidon_mmcs as i64;
    let pcs_poseidon_est = leaf_pcs_bytes as i64 - saved;

    Ok(IdleLeafPoseidonMmcsReport {
        security_level: security_level.to_string(),
        leaf_pcs_bytes,
        mmcs_groups_stark_bytes_keccak: keccak_mmcs,
        mmcs_groups_stark_bytes_poseidon_estimate: poseidon_mmcs,
        mmcs_groups_stark_saved_bytes: saved,
        leaf_pcs_poseidon_estimate_bytes: pcs_poseidon_est,
        poseidon,
        reference_sweep_label: SWEEP_REF_LABEL.to_string(),
        reference_keccak_root_bytes: SWEEP_REF_ROOT_BYTES,
        reference_mmcs_groups_per_side: SWEEP_REF_MMCS_GROUPS_PER_SIDE,
    })
}

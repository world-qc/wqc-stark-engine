//! Idle leaf PCS — Poseidon2 Mmcs group size benchmark vs Keccak baseline.

use crate::generate_plonky3_stark_proof;
use crate::plonky3_stark::recursion::benchmark_poseidon_mmcs_from_child;
use crate::plonky3_stark::recursion::PoseidonMmcsBenchmarkReport;
use crate::plonky3_stark::recursion::PCS_MMCS_HASH_ENV;
use crate::shrink::idle_compose::compose_idle_two_leaf_root_with_pcs;
use crate::shrink::IdleTwoLeafComposeReport;
use crate::trace_spec;
use crate::transcript::StarkContext;

/// Reference row from `fixtures/e5b/sweep.json` (`low/chunk24`).
pub const SWEEP_REF_LABEL: &str = "low/chunk24";
pub const SWEEP_REF_ROOT_BYTES: u64 = 5_022_410;
pub const SWEEP_REF_LEFT_PCS_BYTES: u64 = 2_499_954;
pub const SWEEP_REF_MMCS_GROUPS_PER_SIDE: u64 = 2_400_773;

/// Production Poseidon compose fixture under the §7.1 shrink gate (nested=outer, chunk40).
pub const POSEIDON_COMPOSE_DEFAULT_CHUNK40_JSON: &str =
    "fixtures/e5b/poseidon-compose-default-chunk40.json";
pub const POSEIDON_DEFAULT_CHUNK40_ROOT_BYTES: u64 = 173_483;

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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IdleTwoLeafPoseidonComposeReport {
    pub security_level: String,
    pub keccak_reference_root_bytes: u64,
    pub compose: IdleTwoLeafComposeReport,
    pub root_saved_vs_keccak_ref: i64,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct PoseidonComposeFixture {
    pub benchmark: String,
    pub fri_num_queries: u32,
    pub nested_fri_num_queries: u32,
    pub mmcs_group_chunk: u32,
    pub root_bytes: u64,
    pub left_pcs_bytes: u64,
    pub shrink_gate_bytes: u64,
    pub has_rec_agg_tail: bool,
}

fn idle_leaf_context(
    sub_task_id: &'static str,
    security_level: &'static str,
) -> StarkContext<'static> {
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

fn parse_security_level(security_level: &str) -> Result<&'static str, String> {
    match security_level {
        "" => Ok(""),
        "low" => Ok("low"),
        "normal" => Ok("normal"),
        "high" => Ok("high"),
        "ultra" => Ok("ultra"),
        other => Err(format!("unsupported security_level {other}")),
    }
}

/// Prove one idle leaf PCS and compare Keccak vs Poseidon2 group STARK bytes.
pub fn benchmark_idle_leaf_poseidon_mmcs(
    security_level: &str,
) -> Result<IdleLeafPoseidonMmcsReport, String> {
    let level = parse_security_level(security_level)?;
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

/// Full idle two-leaf RecAgg compose (Poseidon ValMmcs is production default).
pub fn benchmark_idle_two_leaf_poseidon_compose(
    security_level: &str,
) -> Result<IdleTwoLeafPoseidonComposeReport, String> {
    let level = parse_security_level(security_level)?;
    // Explicit poseidon for environments that still default Keccak via env.
    std::env::set_var(PCS_MMCS_HASH_ENV, "poseidon");
    let compose = compose_idle_two_leaf_root_with_pcs(level)?;
    std::env::remove_var(PCS_MMCS_HASH_ENV);
    Ok(IdleTwoLeafPoseidonComposeReport {
        security_level: security_level.to_string(),
        keccak_reference_root_bytes: SWEEP_REF_ROOT_BYTES,
        root_saved_vs_keccak_ref: SWEEP_REF_ROOT_BYTES as i64 - compose.root_bytes as i64,
        compose,
    })
}

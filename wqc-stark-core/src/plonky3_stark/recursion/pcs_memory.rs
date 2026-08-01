//! C13×C11 hybrid PCS memory gate.
//!
//! Before leaf/agg PCS Mmcs group prove: estimate peak RAM for the dominant
//! blowup-16 Keccak group STARK. If over `WQC_MAX_MEMORY_GB`:
//! - `WQC_PCS_MEMORY_POLICY=refuse` (default) → error
//! - `WQC_PCS_MEMORY_POLICY=spill` → lower session Mmcs chunk until estimate fits
//!   (min chunk = 1); if still over → refuse
//!
//! `WQC_MAX_MEMORY_GB` unset → no gate (compat).

use super::fri_fold_bind::LEAF_FRI_PROVEN_QUERIES;
use super::fri_mmcs_group_m4b::{m4b_group_chunk_from_env, M4bChunkGuard, M4B_MAX_PATHS};

const GIB: f64 = 1024.0 * 1024.0 * 1024.0;

/// Fixed prove/orchestration overhead outside the Mmcs group matrix.
const BASE_BYTES: u64 = 512 * 1024 * 1024;
/// FriFold group + OOD (+ occasional DeepRo) residual workspace.
const FIXED_FRI_FOLD_OOD_BYTES: u64 = 256 * 1024 * 1024;
/// Rough bytes per (path × merkle-depth) in one blowup-16 Mmcs group prove.
/// Calibrated so unitary-scale PCS at chunk=24 / depth≈8 is multi-GiB.
const PER_PATH_DEPTH_BYTES: u64 = 18 * 1024 * 1024;

/// Stable error / log prefix for node and orch.
pub const PCS_MEMORY_ERR_PREFIX: &str = "PCS memory:";

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PcsMemoryPolicy {
    Refuse,
    Spill,
}

impl PcsMemoryPolicy {
    pub fn from_env() -> Self {
        match std::env::var("WQC_PCS_MEMORY_POLICY")
            .ok()
            .as_deref()
            .map(str::trim)
            .map(str::to_ascii_lowercase)
            .as_deref()
        {
            Some("spill") => Self::Spill,
            _ => Self::Refuse,
        }
    }

    pub fn as_str(self) -> &'static str {
        match self {
            Self::Refuse => "refuse",
            Self::Spill => "spill",
        }
    }
}

/// Plan for one PCS certificate build.
#[derive(Debug, Clone)]
pub struct PcsMemoryPlan {
    pub effective_chunk: usize,
    pub requested_chunk: usize,
    pub spilled: bool,
    pub estimate_bytes: u64,
    /// `None` = no budget gate (`WQC_MAX_MEMORY_GB` unset).
    pub budget_bytes: Option<u64>,
}

impl PcsMemoryPlan {
    /// Install a thread-local Mmcs chunk override for this build (cleared on drop).
    pub fn enter_chunk_override(&self) -> M4bChunkGuard {
        M4bChunkGuard::set(self.effective_chunk)
    }
}

/// Read `WQC_MAX_MEMORY_GB` as bytes. `None` if unset / empty / invalid → no gate.
pub fn budget_bytes_from_env() -> Option<u64> {
    let raw = std::env::var("WQC_MAX_MEMORY_GB").ok()?;
    let trimmed = raw.trim();
    if trimmed.is_empty() {
        return None;
    }
    let gib: f64 = trimmed.parse().ok()?;
    if !(gib.is_finite() && gib > 0.0) {
        return None;
    }
    Some((gib * GIB) as u64)
}

fn estimate_scale_from_env() -> f64 {
    std::env::var("WQC_PCS_MEMORY_ESTIMATE_SCALE")
        .ok()
        .and_then(|v| v.trim().parse::<f64>().ok())
        .filter(|s| s.is_finite() && *s > 0.0)
        .unwrap_or(1.0)
}

/// Conservative Merkle depth hint from STARK degree (trace log-height ≈ degree_bits + blowup).
pub fn depth_hint_from_degree_bits(degree_bits: usize) -> usize {
    // Devnet blowup is 1 for leaf; Keccak group uses blowup 16 but path depth tracks
    // the committed Merkle height ≈ degree_bits + log_blowup (~1–2).
    degree_bits
        .saturating_add(2)
        .clamp(4, FRI_MMCS_MAX_DEPTH_HINT)
}

const FRI_MMCS_MAX_DEPTH_HINT: usize = 24;

/// Peak RAM estimate for one PCS build at the given Mmcs group chunk.
///
/// `num_queries` is the outer FRI query count for this proof (`1..=LEAF_FRI_PROVEN_QUERIES`).
pub fn estimate_pcs_peak_bytes(
    degree_bits: usize,
    chunk: usize,
    depth_hint: Option<usize>,
    num_queries: usize,
) -> u64 {
    let chunk = chunk.clamp(1, M4B_MAX_PATHS) as u64;
    let depth = depth_hint
        .unwrap_or_else(|| depth_hint_from_degree_bits(degree_bits))
        .max(1) as u64;
    // Outer query slots scale sequential residual work; normalize so ultra (40) ≈ prior estimate.
    let n = num_queries.clamp(1, LEAF_FRI_PROVEN_QUERIES) as u64;
    let group = PER_PATH_DEPTH_BYTES
        .saturating_mul(chunk)
        .saturating_mul(depth)
        .saturating_mul(n)
        / (LEAF_FRI_PROVEN_QUERIES as u64).max(1);
    let raw = BASE_BYTES
        .saturating_add(FIXED_FRI_FOLD_OOD_BYTES)
        .saturating_add(group);
    let scale = estimate_scale_from_env();
    ((raw as f64) * scale) as u64
}

fn format_gib(bytes: u64) -> String {
    format!("{:.2}", bytes as f64 / GIB)
}

fn refuse_err(estimate: u64, budget: u64, policy: PcsMemoryPolicy) -> String {
    format!(
        "{PCS_MEMORY_ERR_PREFIX} estimate={} GiB exceeds budget={} GiB (policy={})",
        format_gib(estimate),
        format_gib(budget),
        policy.as_str()
    )
}

/// Spill candidates: requested, then 16/8/4/2/1 (unique, descending).
pub fn spill_chunk_candidates(requested: usize) -> Vec<usize> {
    let requested = requested.clamp(1, M4B_MAX_PATHS);
    let mut out = vec![requested];
    for s in [16, 8, 4, 2, 1] {
        if s < requested {
            out.push(s);
        }
    }
    out
}

/// Decide effective Mmcs chunk (and whether to refuse) for a PCS build.
pub fn plan_pcs_memory(
    degree_bits: usize,
    depth_hint: Option<usize>,
    num_queries: usize,
) -> Result<PcsMemoryPlan, String> {
    let requested = m4b_group_chunk_from_env();
    let budget = budget_bytes_from_env();
    let Some(budget_bytes) = budget else {
        let estimate = estimate_pcs_peak_bytes(degree_bits, requested, depth_hint, num_queries);
        return Ok(PcsMemoryPlan {
            effective_chunk: requested,
            requested_chunk: requested,
            spilled: false,
            estimate_bytes: estimate,
            budget_bytes: None,
        });
    };

    let estimate_req = estimate_pcs_peak_bytes(degree_bits, requested, depth_hint, num_queries);
    if estimate_req <= budget_bytes {
        return Ok(PcsMemoryPlan {
            effective_chunk: requested,
            requested_chunk: requested,
            spilled: false,
            estimate_bytes: estimate_req,
            budget_bytes: Some(budget_bytes),
        });
    }

    let policy = PcsMemoryPolicy::from_env();
    match policy {
        PcsMemoryPolicy::Refuse => Err(refuse_err(estimate_req, budget_bytes, policy)),
        PcsMemoryPolicy::Spill => {
            for chunk in spill_chunk_candidates(requested) {
                let est = estimate_pcs_peak_bytes(degree_bits, chunk, depth_hint, num_queries);
                if est <= budget_bytes {
                    eprintln!(
                        "{PCS_MEMORY_ERR_PREFIX} spill: chunk {requested} → {chunk} (est {} GiB ≤ budget {} GiB)",
                        format_gib(est),
                        format_gib(budget_bytes),
                    );
                    return Ok(PcsMemoryPlan {
                        effective_chunk: chunk,
                        requested_chunk: requested,
                        spilled: chunk != requested,
                        estimate_bytes: est,
                        budget_bytes: Some(budget_bytes),
                    });
                }
            }
            let est1 = estimate_pcs_peak_bytes(degree_bits, 1, depth_hint, num_queries);
            Err(refuse_err(est1, budget_bytes, policy))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::fri_mmcs_group_m4b::{M4B_GROUP_CHUNK_DEFAULT, PCS_MMCS_GROUP_CHUNK_ENV};
    use super::*;
    use std::sync::Mutex;

    /// Serialize env-mutating tests (process-global env).
    static ENV_LOCK: Mutex<()> = Mutex::new(());

    fn with_clean_env<R>(f: impl FnOnce() -> R) -> R {
        let _g = ENV_LOCK.lock().unwrap();
        std::env::remove_var("WQC_MAX_MEMORY_GB");
        std::env::remove_var("WQC_PCS_MEMORY_POLICY");
        std::env::remove_var("WQC_PCS_MEMORY_ESTIMATE_SCALE");
        std::env::remove_var(PCS_MMCS_GROUP_CHUNK_ENV);
        f()
    }

    #[test]
    fn estimate_monotonic_in_chunk() {
        with_clean_env(|| {
            let d = 8usize;
            let e1 = estimate_pcs_peak_bytes(d, 1, Some(8), 40);
            let e8 = estimate_pcs_peak_bytes(d, 8, Some(8), 40);
            let e24 = estimate_pcs_peak_bytes(d, 24, Some(8), 40);
            assert!(e1 < e8 && e8 < e24);
            // Unitary-scale chunk=24 should be multi-GiB.
            assert!(e24 > 2 * 1024 * 1024 * 1024);
        });
    }

    #[test]
    fn no_budget_skips_gate() {
        with_clean_env(|| {
            let plan = plan_pcs_memory(8, Some(8), 40).expect("plan");
            assert!(plan.budget_bytes.is_none());
            assert!(!plan.spilled);
            assert_eq!(plan.effective_chunk, M4B_GROUP_CHUNK_DEFAULT);
        });
    }

    #[test]
    fn under_budget_keeps_requested_chunk() {
        with_clean_env(|| {
            std::env::set_var("WQC_MAX_MEMORY_GB", "64");
            std::env::set_var(PCS_MMCS_GROUP_CHUNK_ENV, "24");
            let plan = plan_pcs_memory(8, Some(8), 40).expect("plan");
            assert!(!plan.spilled);
            assert_eq!(plan.effective_chunk, 24);
        });
    }

    #[test]
    fn refuse_when_over_budget() {
        with_clean_env(|| {
            std::env::set_var("WQC_MAX_MEMORY_GB", "1");
            std::env::set_var(PCS_MMCS_GROUP_CHUNK_ENV, "24");
            // default policy = refuse
            let err = plan_pcs_memory(8, Some(8), 40).expect_err("refuse");
            assert!(err.starts_with(PCS_MEMORY_ERR_PREFIX));
            assert!(err.contains("policy=refuse"));
        });
    }

    #[test]
    fn spill_lowers_chunk() {
        with_clean_env(|| {
            std::env::set_var("WQC_MAX_MEMORY_GB", "2");
            std::env::set_var("WQC_PCS_MEMORY_POLICY", "spill");
            std::env::set_var(PCS_MMCS_GROUP_CHUNK_ENV, "24");
            let plan = plan_pcs_memory(8, Some(8), 40).expect("spill");
            assert!(plan.spilled || plan.effective_chunk < 24);
            assert!(plan.effective_chunk <= 24);
            assert!(plan.estimate_bytes <= plan.budget_bytes.unwrap());
        });
    }

    #[test]
    fn spill_then_refuse_when_impossible() {
        with_clean_env(|| {
            std::env::set_var("WQC_MAX_MEMORY_GB", "0.1");
            std::env::set_var("WQC_PCS_MEMORY_POLICY", "spill");
            std::env::set_var(PCS_MMCS_GROUP_CHUNK_ENV, "24");
            let err = plan_pcs_memory(8, Some(8), 40).expect_err("still refuse");
            assert!(err.contains("policy=spill"));
        });
    }

    #[test]
    fn spill_candidates_descend() {
        assert_eq!(spill_chunk_candidates(24), vec![24, 16, 8, 4, 2, 1]);
        assert_eq!(spill_chunk_candidates(8), vec![8, 4, 2, 1]);
        assert_eq!(spill_chunk_candidates(1), vec![1]);
    }

    #[test]
    fn chunk_override_guard_restores() {
        with_clean_env(|| {
            std::env::set_var(PCS_MMCS_GROUP_CHUNK_ENV, "24");
            assert_eq!(super::super::fri_mmcs_group_m4b::m4b_group_chunk(), 24);
            {
                let _g = M4bChunkGuard::set(4);
                assert_eq!(super::super::fri_mmcs_group_m4b::m4b_group_chunk(), 4);
            }
            assert_eq!(super::super::fri_mmcs_group_m4b::m4b_group_chunk(), 24);
        });
    }
}

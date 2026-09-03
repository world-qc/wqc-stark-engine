//! E5b shrink optimization profiles — knobs that affect R3/PCS wire size.
//!
//! Dominant cost today: Poseidon2 M4b `mmcs_groups` (~90% of leaf PCS nested STARK bytes).
//! Levers (see README Roadmap):
//! 1. **`security_level`** → outer FRI query count (8/16/32/40) — linear on Mmcs paths;
//!    nested Mmcs/FriFold STARKs default to this count
//! 2. **`WQC_PCS_MMCS_GROUP_CHUNK`** → fewer/larger group STARKs (sublinear wire savings;
//!    chunk40 helps when fri_num_queries > chunk; exhausted at 40q/chunk40 = 1 group/cat)
//! 3. Group AIR / public-value shrink — both Mmcs group AIRs pack publics by actual
//!    depth with a shared-root header and chain layer digests through segment
//!    transitions; FriFold groups hoist a shared `beta`. These cut publics ~4x but
//!    barely move `group_stark`, which is dominated by nested FRI commitments.
//! 4. Wire dedup — leaf/layer digests are recomputed from path statements at verify
//!    time instead of shipped (mmcs fold wire v5); this is where PCS metadata shrank.
//! 5. **`WQC_PCS_NESTED_FRI_QUERIES`** → nested Mmcs/FriFold FRI query count (≤ outer);
//!    default matches outer. Remaining soft size lever on `group_stark` at 40q/chunk40.

use crate::plonky3_stark::{fri_num_queries_for_security_level, DEVNET_FRI_NUM_QUERIES};

/// Default Mmcs group chunk when `WQC_PCS_MMCS_GROUP_CHUNK` is unset (see zk-STARK §8.4).
const DEFAULT_MMCS_GROUP_CHUNK: usize = 24;

/// Active shrink compose profile (mirrors devnet orch task fields + PCS env).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShrinkComposeProfile {
    /// Orchestrator ladder: `low` | `normal` | `high` | `ultra` | `""` (devnet default = 40 queries).
    pub security_level: String,
    /// `WQC_PCS_MMCS_GROUP_CHUNK` at prove time (default 24).
    pub mmcs_group_chunk: usize,
    /// Nested Mmcs/FriFold FRI queries (`WQC_PCS_NESTED_FRI_QUERIES`); `None` = match outer.
    pub nested_fri_queries: Option<usize>,
}

impl Default for ShrinkComposeProfile {
    fn default() -> Self {
        Self {
            security_level: String::new(),
            mmcs_group_chunk: DEFAULT_MMCS_GROUP_CHUNK,
            nested_fri_queries: None,
        }
    }
}

impl ShrinkComposeProfile {
    pub fn from_env() -> Self {
        let mmcs_group_chunk = std::env::var("WQC_PCS_MMCS_GROUP_CHUNK")
            .ok()
            .and_then(|v| v.trim().parse().ok())
            .filter(|&n| n >= 1)
            .unwrap_or(DEFAULT_MMCS_GROUP_CHUNK);
        let outer = fri_num_queries_for_security_level("");
        let nested = nested_fri_queries_from_env(outer);
        Self {
            security_level: String::new(),
            mmcs_group_chunk,
            nested_fri_queries: if nested == outer { None } else { Some(nested) },
        }
    }

    pub fn with_security_level(mut self, level: &str) -> Self {
        self.security_level = level.trim().to_string();
        let outer = self.fri_num_queries();
        let nested = nested_fri_queries_from_env(outer);
        self.nested_fri_queries = if nested == outer { None } else { Some(nested) };
        self
    }

    pub fn fri_num_queries(&self) -> usize {
        fri_num_queries_for_security_level(&self.security_level)
    }

    /// Effective nested FRI query count for group STARKs.
    pub fn nested_fri_num_queries(&self) -> usize {
        nested_fri_queries_from_env(self.fri_num_queries())
    }

    pub fn label(&self) -> String {
        let level = if self.security_level.is_empty() {
            "default(40q)"
        } else {
            self.security_level.as_str()
        };
        let nested = self.nested_fri_num_queries();
        let outer = self.fri_num_queries();
        if nested == outer {
            format!("{level}/chunk{}", self.mmcs_group_chunk)
        } else {
            format!("{level}/chunk{}/nested{nested}q", self.mmcs_group_chunk)
        }
    }
}

/// Mirror of `nested_fri_queries` for shrink tooling (avoids a plonky3-feature cycle).
fn nested_fri_queries_from_env(outer_queries: usize) -> usize {
    let outer = outer_queries.max(1).min(DEVNET_FRI_NUM_QUERIES);
    match std::env::var("WQC_PCS_NESTED_FRI_QUERIES")
        .ok()
        .and_then(|v| v.trim().parse::<usize>().ok())
    {
        Some(n) if (1..=outer).contains(&n) => n,
        _ => outer,
    }
}

/// Rough linear scale vs devnet max queries (for planning only — not a size predictor).
pub fn query_count_shrink_factor(security_level: &str) -> f64 {
    fri_num_queries_for_security_level(security_level) as f64 / DEVNET_FRI_NUM_QUERIES as f64
}

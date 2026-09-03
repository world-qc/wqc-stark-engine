//! E5b shrink optimization profiles — knobs that affect R3/PCS wire size.
//!
//! Dominant cost today: Poseidon2 M4b `mmcs_groups` (~90% of leaf PCS nested STARK bytes).
//! Levers (see README Roadmap):
//! 1. **`security_level`** → outer FRI query count (8/16/32/40) — linear on Mmcs paths;
//!    nested Mmcs/FriFold STARKs now match this count
//! 2. **`WQC_PCS_MMCS_GROUP_CHUNK`** → fewer/larger group STARKs (sublinear wire savings;
//!    chunk40 helps when fri_num_queries > chunk)
//! 3. Group AIR / public-value shrink — both Mmcs group AIRs pack publics by actual
//!    depth with a shared-root header and chain layer digests through segment
//!    transitions; FriFold groups hoist a shared `beta`. These cut publics ~4x but
//!    barely move `group_stark`, which is dominated by nested FRI commitments.
//! 4. Wire dedup — leaf/layer digests are recomputed from path statements at verify
//!    time instead of shipped (mmcs fold wire v5); this is where PCS metadata shrank.

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
}

impl Default for ShrinkComposeProfile {
    fn default() -> Self {
        Self {
            security_level: String::new(),
            mmcs_group_chunk: DEFAULT_MMCS_GROUP_CHUNK,
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
        Self {
            security_level: String::new(),
            mmcs_group_chunk,
        }
    }

    pub fn with_security_level(mut self, level: &str) -> Self {
        self.security_level = level.trim().to_string();
        self
    }

    pub fn fri_num_queries(&self) -> usize {
        fri_num_queries_for_security_level(&self.security_level)
    }

    pub fn label(&self) -> String {
        let level = if self.security_level.is_empty() {
            "default(40q)"
        } else {
            self.security_level.as_str()
        };
        format!("{level}/chunk{}", self.mmcs_group_chunk)
    }
}

/// Rough linear scale vs devnet max queries (for planning only — not a size predictor).
pub fn query_count_shrink_factor(security_level: &str) -> f64 {
    fri_num_queries_for_security_level(security_level) as f64 / DEVNET_FRI_NUM_QUERIES as f64
}

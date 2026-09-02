//! Recorded E5b shrink optimization sweep (`fixtures/e5b/sweep.json`).

use std::fs;
use std::path::Path;

use serde::{Deserialize, Serialize};

pub const SWEEP_JSON: &str = "fixtures/e5b/sweep.json";

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ShrinkSweepRow {
    pub label: String,
    pub security_level: String,
    pub fri_num_queries: u32,
    pub mmcs_group_chunk: u32,
    pub root_bytes: u64,
    pub left_pcs_bytes: u64,
    pub mmcs_groups_per_side: u64,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub note: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ShrinkSweepBest {
    pub label: String,
    pub root_bytes: u64,
    pub vs_default_pct: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ShrinkSweep {
    pub benchmark: String,
    pub measured_at: String,
    pub shrink_gate_bytes: u64,
    pub rows: Vec<ShrinkSweepRow>,
    pub best_knob_only: ShrinkSweepBest,
    pub next_levers: Vec<String>,
}

impl ShrinkSweep {
    pub fn load_from_repo(repo_root: &Path) -> Result<Self, String> {
        let path = repo_root.join(SWEEP_JSON);
        let raw = fs::read_to_string(&path).map_err(|e| format!("read {}: {e}", path.display()))?;
        serde_json::from_str(&raw).map_err(|e| format!("parse {}: {e}", path.display()))
    }

    pub fn default_row(&self) -> Option<&ShrinkSweepRow> {
        self.rows.iter().find(|r| r.label == "default/chunk24")
    }

    pub fn best_row(&self) -> Option<&ShrinkSweepRow> {
        self.rows
            .iter()
            .min_by_key(|r| r.root_bytes)
            .or_else(|| self.rows.first())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::shrink::baseline::stark_engine_repo_root;
    use crate::shrink::SHRINK_GATE_BYTES;

    #[test]
    fn sweep_json_loads_and_best_beats_default() {
        let repo = stark_engine_repo_root();
        let sweep = ShrinkSweep::load_from_repo(&repo).expect("load sweep");
        assert_eq!(sweep.shrink_gate_bytes, SHRINK_GATE_BYTES);
        let default = sweep.default_row().expect("default row");
        let best = sweep.best_row().expect("best row");
        assert!(
            best.root_bytes < default.root_bytes,
            "best {} should beat default {}",
            best.root_bytes,
            default.root_bytes
        );
        assert!(
            best.root_bytes > SHRINK_GATE_BYTES,
            "knob-only sweep still above shrink gate"
        );
    }
}

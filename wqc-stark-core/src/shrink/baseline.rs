//! JSON baseline for E5b shrink regression (optional golden `root.bin` fixture).

use std::fs;
use std::path::{Path, PathBuf};

#[cfg(feature = "plonky3-stark")]
use crate::aggregation::{verify_root_proof, RootVerifyContext};
use crate::shrink::{
    IDLE_TWO_LEAF_DOCUMENTED_BASELINE_BYTES, IDLE_TWO_LEAF_REGRESSION_CEILING_BYTES,
    SHRINK_GATE_BYTES,
};

/// Relative to `wqc-stark-engine/` workspace root.
pub const BASELINE_JSON: &str = "fixtures/e5b/baseline.json";

/// Optional golden root proof (gitignored until generated locally).
pub const FIXTURE_ROOT_BIN: &str = "fixtures/e5b/idle_two_leaf_root.bin";

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct ShrinkBaseline {
    /// Last measured full RecAgg root size (bytes). `null` until first local run.
    pub root_bytes: Option<u64>,
    pub regression_ceiling_bytes: u64,
    pub shrink_gate_bytes: u64,
    pub documented_baseline_bytes: u64,
    pub fixture_path: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub security_level: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub mmcs_group_chunk: Option<u32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub fri_num_queries: Option<u32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub updated_at: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub note: Option<String>,
}

impl Default for ShrinkBaseline {
    fn default() -> Self {
        Self {
            root_bytes: None,
            regression_ceiling_bytes: IDLE_TWO_LEAF_REGRESSION_CEILING_BYTES,
            shrink_gate_bytes: SHRINK_GATE_BYTES,
            documented_baseline_bytes: IDLE_TWO_LEAF_DOCUMENTED_BASELINE_BYTES,
            fixture_path: FIXTURE_ROOT_BIN.to_string(),
            security_level: None,
            mmcs_group_chunk: None,
            fri_num_queries: None,
            updated_at: None,
            note: Some(
                "Run `cargo run -p wqc-stark-core --bin shrink-baseline --features plonky3-stark --release` to refresh."
                    .to_string(),
            ),
        }
    }
}

impl ShrinkBaseline {
    pub fn load_from_repo(repo_root: &Path) -> Result<Self, String> {
        let path = repo_root.join(BASELINE_JSON);
        if !path.is_file() {
            return Ok(Self::default());
        }
        let raw = fs::read_to_string(&path).map_err(|e| format!("read {}: {e}", path.display()))?;
        serde_json::from_str(&raw).map_err(|e| format!("parse {}: {e}", path.display()))
    }

    pub fn save_to_repo(&self, repo_root: &Path) -> Result<(), String> {
        let path = repo_root.join(BASELINE_JSON);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).map_err(|e| format!("mkdir {}: {e}", parent.display()))?;
        }
        let raw =
            serde_json::to_string_pretty(self).map_err(|e| format!("serialize baseline: {e}"))?;
        fs::write(&path, raw).map_err(|e| format!("write {}: {e}", path.display()))
    }

    pub fn fixture_path(&self, repo_root: &Path) -> PathBuf {
        repo_root.join(&self.fixture_path)
    }

    /// When a golden fixture exists, verify it and enforce ceiling (+ optional exact baseline).
    pub fn check_fixture_if_present(repo_root: &Path) -> Result<Option<usize>, String> {
        let baseline = Self::load_from_repo(repo_root)?;
        let fixture = baseline.fixture_path(repo_root);
        if !fixture.is_file() {
            return Ok(None);
        }
        let root = fs::read(&fixture).map_err(|e| format!("read {}: {e}", fixture.display()))?;
        let size = root.len();
        if size as u64 > baseline.regression_ceiling_bytes {
            return Err(format!(
                "fixture {} is {} bytes, above ceiling {}",
                fixture.display(),
                size,
                baseline.regression_ceiling_bytes
            ));
        }
        if let Some(expected) = baseline.root_bytes {
            if size as u64 != expected {
                return Err(format!(
                    "fixture {} is {} bytes but baseline.json records {}",
                    fixture.display(),
                    size,
                    expected
                ));
            }
        }
        #[cfg(feature = "plonky3-stark")]
        if !verify_root_proof(
            &RootVerifyContext {
                parent_task_id: "e5b-shrink-parent",
                manifest_root_hash: "manifest-e5b-shrink",
                security_level: "",
            },
            &root,
        ) {
            return Err(format!(
                "fixture {} fails verify_root_proof",
                fixture.display()
            ));
        }
        Ok(Some(size))
    }
}

/// Resolve `wqc-stark-engine` repo root from `CARGO_MANIFEST_DIR` (crate dir).
pub fn stark_engine_repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .map(Path::to_path_buf)
        .expect("wqc-stark-core has a parent directory")
}

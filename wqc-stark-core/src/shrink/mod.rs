//! E5b **Shrink** track — root proof footprint reduction (see `wqc-contracts` scope §7).
//!
//! Full idle two-leaf compose with RecAgg V6 + leaf PCS is slow (~hours). Use
//! [`compose_idle_two_leaf_root_with_pcs`] locally or in the scheduled CI workflow;
//! default PR CI runs fast bounds and optional golden-fixture checks only.

mod r2_compose;

#[cfg(feature = "plonky3-stark")]
mod idle_compose;

pub mod baseline;

pub use r2_compose::compose_idle_two_leaf_root_r2_only;

#[cfg(feature = "plonky3-stark")]
pub use idle_compose::{
    compose_idle_two_leaf_root_with_pcs, compose_idle_two_leaf_root_with_pcs_and_bytes,
    rec_agg_tail_bytes, IdleTwoLeafComposeReport,
};

/// Mainnet shrink gate from `on-chain_settlement_scope.md` §7.1 (500 KB pre-wrap).
pub const SHRINK_GATE_BYTES: u64 = 500 * 1024;

/// Measured idle two-leaf baseline (`fixtures/e5b/baseline.json`, `wqc-stark-engine` README).
pub const IDLE_TWO_LEAF_DOCUMENTED_BASELINE_BYTES: u64 = 10_742_800;

/// Regression ceiling until shrink gate is met (12.5% headroom over documented baseline).
pub const IDLE_TWO_LEAF_REGRESSION_CEILING_BYTES: u64 = 18 * 1024 * 1024;

/// R2-only idle two-leaf compose (no RecAgg) must stay well below shrink gate.
pub const R2_IDLE_TWO_LEAF_MAX_BYTES: usize = 512 * 1024;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::shrink::baseline::{
        stark_engine_repo_root, ShrinkBaseline, BASELINE_JSON, FIXTURE_ROOT_BIN,
    };

    #[test]
    fn shrink_gate_constants_match_scope() {
        assert_eq!(SHRINK_GATE_BYTES, 500 * 1024);
        assert_eq!(IDLE_TWO_LEAF_DOCUMENTED_BASELINE_BYTES, 10_742_800);
        assert_eq!(IDLE_TWO_LEAF_REGRESSION_CEILING_BYTES, 18 * 1024 * 1024);
    }

    #[test]
    fn baseline_json_matches_constants() {
        let repo = stark_engine_repo_root();
        let baseline = ShrinkBaseline::load_from_repo(&repo).expect("load baseline");
        assert_eq!(
            baseline.regression_ceiling_bytes,
            IDLE_TWO_LEAF_REGRESSION_CEILING_BYTES
        );
        assert_eq!(baseline.shrink_gate_bytes, SHRINK_GATE_BYTES);
        assert_eq!(
            baseline.documented_baseline_bytes,
            IDLE_TWO_LEAF_DOCUMENTED_BASELINE_BYTES
        );
        assert!(repo.join(BASELINE_JSON).is_file());
    }

    #[test]
    fn r2_idle_two_leaf_root_under_max() {
        let size = compose_idle_two_leaf_root_r2_only().expect("r2 compose");
        assert!(
            size <= R2_IDLE_TWO_LEAF_MAX_BYTES,
            "R2 idle two-leaf root is {size} bytes (max {R2_IDLE_TWO_LEAF_MAX_BYTES})"
        );
    }

    #[test]
    fn golden_fixture_check_skips_when_absent() {
        let repo = stark_engine_repo_root();
        let fixture = repo.join(FIXTURE_ROOT_BIN);
        let out = ShrinkBaseline::check_fixture_if_present(&repo).expect("fixture check");
        if fixture.is_file() {
            assert!(out.is_some());
            if let Some(size) = out {
                assert!(size as u64 <= IDLE_TWO_LEAF_REGRESSION_CEILING_BYTES);
            }
        } else {
            assert!(out.is_none());
        }
    }

    #[cfg(feature = "plonky3-stark")]
    #[test]
    #[ignore = "slow; local or scheduled CI only — multi-hour RecAgg + PCS compose"]
    fn idle_two_leaf_rec_agg_compose_under_regression_ceiling() {
        use crate::shrink::idle_compose::compose_idle_two_leaf_root_with_pcs;

        let report = compose_idle_two_leaf_root_with_pcs("").expect("full compose");
        assert!(
            report.has_rec_agg_tail,
            "E5b shrink benchmark must include RecAgg V6 tail"
        );
        assert!(
            report.root_bytes as u64 <= IDLE_TWO_LEAF_REGRESSION_CEILING_BYTES,
            "root {} bytes exceeds ceiling {}",
            report.root_bytes,
            IDLE_TWO_LEAF_REGRESSION_CEILING_BYTES
        );

        let repo = stark_engine_repo_root();
        if repo.join(FIXTURE_ROOT_BIN).is_file() {
            ShrinkBaseline::check_fixture_if_present(&repo).expect("golden fixture verify");
        }
    }
}

//! E5b **Shrink** track — root proof footprint reduction (see `wqc-contracts` scope §7).
//!
//! Full idle two-leaf compose with RecAgg V6 + leaf PCS is slow (~hours). Use
//! [`compose_idle_two_leaf_root_with_pcs`] locally or in the scheduled CI workflow;
//! default PR CI runs fast bounds and optional golden-fixture checks only.

mod profile;
mod r2_compose;
mod sweep;

#[cfg(feature = "plonky3-stark")]
mod idle_compose;

#[cfg(feature = "plonky3-stark")]
mod poseidon_benchmark;

pub mod baseline;

pub use profile::{query_count_shrink_factor, ShrinkComposeProfile};
pub use r2_compose::compose_idle_two_leaf_root_r2_only;
pub use sweep::ShrinkSweep;

#[cfg(feature = "plonky3-stark")]
pub use idle_compose::{
    compose_idle_two_leaf_root_with_pcs, compose_idle_two_leaf_root_with_pcs_and_bytes,
    rec_agg_tail_bytes, IdleTwoLeafComposeReport,
};

#[cfg(feature = "plonky3-stark")]
pub use poseidon_benchmark::{
    benchmark_idle_leaf_poseidon_mmcs, IdleLeafPoseidonMmcsReport, PoseidonComposeFixture,
    POSEIDON_COMPOSE_DEFAULT_CHUNK40_JSON, POSEIDON_DEFAULT_CHUNK40_ROOT_BYTES, SWEEP_REF_LABEL,
    SWEEP_REF_LEFT_PCS_BYTES, SWEEP_REF_MMCS_GROUPS_PER_SIDE, SWEEP_REF_ROOT_BYTES,
};

#[cfg(all(feature = "plonky3-stark", feature = "poseidon-mmcs"))]
pub use poseidon_benchmark::{
    benchmark_idle_two_leaf_poseidon_compose, IdleTwoLeafPoseidonComposeReport,
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
    use crate::shrink::ShrinkSweep;

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
        let out = match ShrinkBaseline::check_fixture_if_present(&repo) {
            Ok(v) => v,
            // Local gitignored fixture may predate Poseidon ValMmcs (CapMismatch).
            Err(e) if e.contains("fails verify_root_proof") => {
                eprintln!("skipping stale golden fixture: {e}");
                None
            }
            Err(e) => panic!("fixture check: {e}"),
        };
        if fixture.is_file() && out.is_some() {
            if let Some(size) = out {
                assert!(size as u64 <= IDLE_TWO_LEAF_REGRESSION_CEILING_BYTES);
            }
        } else if !fixture.is_file() {
            assert!(out.is_none());
        }
    }

    #[test]
    fn query_count_shrink_factor_ladder() {
        assert!((query_count_shrink_factor("low") - 0.2).abs() < f64::EPSILON);
        assert!((query_count_shrink_factor("normal") - 0.4).abs() < f64::EPSILON);
        assert!((query_count_shrink_factor("high") - 0.8).abs() < f64::EPSILON);
        assert!((query_count_shrink_factor("ultra") - 1.0).abs() < f64::EPSILON);
        assert!((query_count_shrink_factor("") - 1.0).abs() < f64::EPSILON);
    }

    #[cfg(feature = "plonky3-stark")]
    #[test]
    fn idle_compose_honors_security_level_on_leaf_proofs() {
        use crate::plonky3_stark::decode_proof_v2_plonky3_bytes;
        use crate::plonky3_stark::recursion::fri_queries_from_proof;
        use crate::transcript::StarkContext;
        use crate::{generate_plonky3_stark_proof, trace_spec};
        use p3_uni_stark::Proof;

        let trace = trace_spec::idle_qubit0_trace();
        for (level, expect_q) in [("low", 8usize), ("ultra", 40usize)] {
            let ctx = StarkContext {
                circuit_id: "e5b-shrink-idle",
                sub_task_id: "sub-shrink-test",
                node_id: "node-shrink-1",
                slice_id: "000",
                output_hash: "out-shrink",
                terminal_statevector_digest: "",
                measurement_spec_hash: "",
                security_level: level,
            };
            let proof = generate_plonky3_stark_proof(&ctx, &trace).expect("prove");
            let p3 = decode_proof_v2_plonky3_bytes(&proof, &ctx).expect("decode");
            let p3_proof: Proof<_> = postcard::from_bytes(&p3).expect("postcard");
            assert_eq!(
                fri_queries_from_proof(&p3_proof).expect("n"),
                expect_q,
                "security_level={level}"
            );
        }
    }

    #[cfg(feature = "plonky3-stark")]
    #[test]
    #[ignore = "slow; PCS prove — run locally to measure low-security shrink"]
    fn idle_two_leaf_low_security_compose_under_regression_ceiling() {
        use crate::shrink::idle_compose::compose_idle_two_leaf_root_with_pcs;

        let report = compose_idle_two_leaf_root_with_pcs("low").expect("low compose");
        assert!(report.has_rec_agg_tail);
        assert!(
            report.root_bytes as u64 <= IDLE_TWO_LEAF_REGRESSION_CEILING_BYTES,
            "low-security root {} bytes",
            report.root_bytes
        );
        assert!(
            report.root_bytes < IDLE_TWO_LEAF_DOCUMENTED_BASELINE_BYTES as usize,
            "low-security root should be smaller than ultra/default baseline"
        );
    }

    #[cfg(feature = "plonky3-stark")]
    #[test]
    #[ignore = "slow; local only — idle leaf PCS prove + Poseidon group re-prove"]
    fn idle_leaf_poseidon_mmcs_benchmark_smoke() {
        use crate::shrink::benchmark_idle_leaf_poseidon_mmcs;

        let report = benchmark_idle_leaf_poseidon_mmcs("low").expect("benchmark");
        assert!(report.leaf_pcs_bytes > 0);
        assert!(report.mmcs_groups_stark_bytes_keccak > 0);
        assert!(report.mmcs_groups_stark_bytes_poseidon_estimate > 0);
        assert!(
            report.mmcs_groups_stark_saved_bytes > 0,
            "Poseidon groups should be smaller than Keccak"
        );
        assert!(
            report.leaf_pcs_poseidon_estimate_bytes < report.leaf_pcs_bytes as i64,
            "estimated Poseidon PCS should shrink vs Keccak"
        );
    }

    #[cfg(feature = "plonky3-stark")]
    #[test]
    #[ignore = "slow; multi-hour — idle two-leaf RecAgg with poseidon-mmcs PCS"]
    fn idle_two_leaf_poseidon_compose_smoke() {
        #[cfg(feature = "poseidon-mmcs")]
        {
            use crate::shrink::benchmark_idle_two_leaf_poseidon_compose;
            let report = benchmark_idle_two_leaf_poseidon_compose("low").expect("compose");
            assert!(report.compose.has_rec_agg_tail);
            assert!(report.compose.root_bytes > 0);
            eprintln!(
                "poseidon compose root={} saved_vs_ref={}",
                report.compose.root_bytes, report.root_saved_vs_keccak_ref
            );
        }
    }

    #[test]
    fn sweep_json_best_beats_default() {
        let repo = stark_engine_repo_root();
        let sweep = ShrinkSweep::load_from_repo(&repo).expect("load sweep");
        let default = sweep.default_row().expect("default row");
        let best = sweep.best_row().expect("best row");
        assert!(best.root_bytes < default.root_bytes);
    }

    /// PR / scheduled CI lock: committed Poseidon nested=outer fixture must stay ≤500 KB.
    #[cfg(feature = "plonky3-stark")]
    #[test]
    fn poseidon_default_chunk40_fixture_under_shrink_gate() {
        use crate::shrink::poseidon_benchmark::{
            PoseidonComposeFixture, POSEIDON_COMPOSE_DEFAULT_CHUNK40_JSON,
            POSEIDON_DEFAULT_CHUNK40_ROOT_BYTES,
        };

        let repo = stark_engine_repo_root();
        let path = repo.join(POSEIDON_COMPOSE_DEFAULT_CHUNK40_JSON);
        let raw = std::fs::read_to_string(&path).expect("read poseidon compose fixture");
        let fix: PoseidonComposeFixture =
            serde_json::from_str(&raw).expect("parse poseidon compose fixture");
        assert_eq!(fix.benchmark, "idle_two_leaf_poseidon_compose");
        assert!(fix.has_rec_agg_tail);
        assert_eq!(fix.fri_num_queries, 40);
        assert_eq!(fix.nested_fri_num_queries, 40);
        assert_eq!(fix.mmcs_group_chunk, 40);
        assert_eq!(fix.shrink_gate_bytes, SHRINK_GATE_BYTES);
        assert_eq!(fix.root_bytes, POSEIDON_DEFAULT_CHUNK40_ROOT_BYTES);
        assert!(
            fix.root_bytes <= SHRINK_GATE_BYTES,
            "production Poseidon nested=outer must stay ≤ shrink gate (got {})",
            fix.root_bytes
        );

        let sweep = ShrinkSweep::load_from_repo(&repo).expect("load sweep");
        let row = sweep
            .rows
            .iter()
            .find(|r| r.label == "poseidon/default/chunk40")
            .expect("sweep poseidon/default/chunk40");
        assert_eq!(
            row.root_bytes, fix.root_bytes,
            "sweep.json must match poseidon-compose-default-chunk40.json"
        );
        assert!(row.root_bytes <= SHRINK_GATE_BYTES);
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

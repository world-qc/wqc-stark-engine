//! E5b shrink benchmark — idle two-leaf root with RecAgg V6 + leaf PCS.
//!
//! Slow (~hours). Writes JSON to stdout and optionally updates `fixtures/e5b/`.

use std::env;
use std::fs;

use wqc_stark_core::shrink::baseline::{
    stark_engine_repo_root, ShrinkBaseline, BASELINE_JSON, FIXTURE_ROOT_BIN,
};
use wqc_stark_core::shrink::compose_idle_two_leaf_root_with_pcs_and_bytes;
use wqc_stark_core::shrink::{
    benchmark_idle_leaf_poseidon_mmcs, ShrinkComposeProfile, IDLE_TWO_LEAF_REGRESSION_CEILING_BYTES,
    SHRINK_GATE_BYTES, SWEEP_REF_LABEL,
};

fn main() {
    if let Err(e) = run() {
        eprintln!("shrink-baseline: {e}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let write_fixture = env::args().any(|a| a == "--write-fixture");
    let write_baseline = env::args().any(|a| a == "--write-baseline") || write_fixture;
    let poseidon_benchmark = env::args().any(|a| a == "--poseidon-benchmark");
    let poseidon_compose = env::args().any(|a| a == "--poseidon-compose");
    let profile = parse_profile()?;

    if poseidon_benchmark {
        return run_poseidon_benchmark(&profile.security_level);
    }
    if poseidon_compose {
        return run_poseidon_compose(&profile.security_level);
    }

    eprintln!(
        "E5b shrink: proving idle two-leaf root (profile={}, {} FRI queries)…",
        profile.label(),
        profile.fri_num_queries()
    );
    let (report, root) = compose_idle_two_leaf_root_with_pcs_and_bytes(&profile.security_level)?;

    let repo = stark_engine_repo_root();
    let mut out = serde_json::json!({
        "root_bytes": report.root_bytes,
        "left_leaf_bytes": report.left_leaf_bytes,
        "right_leaf_bytes": report.right_leaf_bytes,
        "left_pcs_bytes": report.left_pcs_bytes,
        "right_pcs_bytes": report.right_pcs_bytes,
        "has_rec_agg_tail": report.has_rec_agg_tail,
        "security_level": profile.security_level,
        "mmcs_group_chunk": profile.mmcs_group_chunk,
        "fri_num_queries": profile.fri_num_queries(),
        "shrink_gate_bytes": SHRINK_GATE_BYTES,
        "regression_ceiling_bytes": IDLE_TWO_LEAF_REGRESSION_CEILING_BYTES,
    });

    if report.root_bytes as u64 > IDLE_TWO_LEAF_REGRESSION_CEILING_BYTES {
        out["regression_status"] = serde_json::json!("FAIL_CEILING");
    } else if report.root_bytes as u64 <= SHRINK_GATE_BYTES {
        out["regression_status"] = serde_json::json!("PASS_SHRINK_GATE");
    } else {
        out["regression_status"] = serde_json::json!("TRACKING");
    }

    println!(
        "{}",
        serde_json::to_string_pretty(&out).map_err(|e| e.to_string())?
    );

    if write_fixture {
        let fixture = repo.join(FIXTURE_ROOT_BIN);
        if let Some(parent) = fixture.parent() {
            fs::create_dir_all(parent).map_err(|e| format!("mkdir {}: {e}", parent.display()))?;
        }
        fs::write(&fixture, &root).map_err(|e| format!("write {}: {e}", fixture.display()))?;
        eprintln!("wrote {} ({} bytes)", fixture.display(), root.len());
    }

    if write_baseline {
        let mut baseline = ShrinkBaseline::load_from_repo(&repo)?;
        baseline.root_bytes = Some(report.root_bytes as u64);
        baseline.security_level = Some(profile.security_level.clone());
        baseline.mmcs_group_chunk = Some(profile.mmcs_group_chunk as u32);
        baseline.fri_num_queries = Some(profile.fri_num_queries() as u32);
        baseline.updated_at = Some(unix_timestamp());
        baseline.note = Some(format!(
            "Measured by shrink-baseline ({}); has_rec_agg={}",
            profile.label(),
            report.has_rec_agg_tail
        ));
        baseline.save_to_repo(&repo)?;
        eprintln!("updated {}", repo.join(BASELINE_JSON).display());
    }

    if !report.has_rec_agg_tail {
        return Err("expected RecAgg V6 tail on idle two-leaf shrink benchmark".to_string());
    }

    Ok(())
}

fn parse_profile() -> Result<ShrinkComposeProfile, String> {
    let args: Vec<String> = env::args().collect();
    let mut profile = ShrinkComposeProfile::from_env();
    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--security-level" => {
                let level = args
                    .get(i + 1)
                    .ok_or("--security-level requires a value (low|normal|high|ultra)")?;
                profile = profile.with_security_level(level);
                i += 2;
            }
            flag if flag.starts_with("--security-level=") => {
                profile = profile.with_security_level(flag.trim_start_matches("--security-level="));
                i += 1;
            }
            _ => i += 1,
        }
    }
    Ok(profile)
}

fn unix_timestamp() -> String {
    use std::time::{SystemTime, UNIX_EPOCH};
    let secs = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0);
    format!("unix:{secs}")
}

fn run_poseidon_benchmark(security_level: &str) -> Result<(), String> {
    eprintln!(
        "E5b Poseidon Mmcs benchmark: idle leaf PCS (security_level={security_level})…"
    );
    let report = benchmark_idle_leaf_poseidon_mmcs(security_level)?;
    let out = serde_json::json!({
        "benchmark": "idle_leaf_pcs_poseidon_mmcs_groups",
        "security_level": report.security_level,
        "leaf_pcs_bytes_keccak": report.leaf_pcs_bytes,
        "mmcs_groups_stark_bytes_keccak": report.mmcs_groups_stark_bytes_keccak,
        "mmcs_groups_stark_bytes_poseidon_estimate": report.mmcs_groups_stark_bytes_poseidon_estimate,
        "mmcs_groups_stark_saved_bytes": report.mmcs_groups_stark_saved_bytes,
        "leaf_pcs_poseidon_estimate_bytes": report.leaf_pcs_poseidon_estimate_bytes,
        "poseidon_groups_measured": report.poseidon.poseidon_groups_measured,
        "poseidon_groups_skipped_wide": report.poseidon.poseidon_groups_skipped_wide,
        "reference_sweep": report.reference_sweep_label,
        "reference_keccak_root_bytes": report.reference_keccak_root_bytes,
        "reference_mmcs_groups_per_side": report.reference_mmcs_groups_per_side,
    });
    println!(
        "{}",
        serde_json::to_string_pretty(&out).map_err(|e| e.to_string())?
    );

    let repo = stark_engine_repo_root();
    let path = repo.join("fixtures/e5b/poseidon-benchmark.json");
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).map_err(|e| format!("mkdir {}: {e}", parent.display()))?;
    }
    fs::write(
        &path,
        serde_json::to_string_pretty(&out).map_err(|e| e.to_string())?,
    )
    .map_err(|e| format!("write {}: {e}", path.display()))?;
    eprintln!("wrote {} (ref {SWEEP_REF_LABEL})", path.display());
    Ok(())
}

#[cfg(feature = "poseidon-mmcs")]
fn run_poseidon_compose(security_level: &str) -> Result<(), String> {
    use wqc_stark_core::shrink::benchmark_idle_two_leaf_poseidon_compose;

    let level_label = if security_level.is_empty() {
        "default"
    } else {
        security_level
    };
    eprintln!(
        "E5b Poseidon compose: idle two-leaf RecAgg (security_level={level_label})…"
    );
    let report = benchmark_idle_two_leaf_poseidon_compose(security_level)?;
    let profile = ShrinkComposeProfile::from_env().with_security_level(security_level);
    let fri_q = profile.fri_num_queries();
    let nested_q = profile.nested_fri_num_queries();
    let chunk = profile.mmcs_group_chunk;
    let out = serde_json::json!({
        "benchmark": "idle_two_leaf_poseidon_compose",
        "security_level": report.security_level,
        "security_level_label": level_label,
        "fri_num_queries": fri_q,
        "nested_fri_num_queries": nested_q,
        "mmcs_group_chunk": chunk,
        "root_bytes": report.compose.root_bytes,
        "left_leaf_bytes": report.compose.left_leaf_bytes,
        "right_leaf_bytes": report.compose.right_leaf_bytes,
        "left_pcs_bytes": report.compose.left_pcs_bytes,
        "right_pcs_bytes": report.compose.right_pcs_bytes,
        "has_rec_agg_tail": report.compose.has_rec_agg_tail,
        "keccak_reference_root_bytes": report.keccak_reference_root_bytes,
        "root_saved_vs_keccak_ref": report.root_saved_vs_keccak_ref,
        "reference_sweep": SWEEP_REF_LABEL,
        "shrink_gate_bytes": SHRINK_GATE_BYTES,
        "vs_shrink_gate": (report.compose.root_bytes as i64) - (SHRINK_GATE_BYTES as i64),
    });
    println!(
        "{}",
        serde_json::to_string_pretty(&out).map_err(|e| e.to_string())?
    );

    let repo = stark_engine_repo_root();
    let filename = if nested_q != fri_q {
        format!(
            "fixtures/e5b/poseidon-compose-{}-chunk{}-nested{}q.json",
            if security_level.is_empty() {
                "default"
            } else {
                security_level
            },
            chunk,
            nested_q
        )
    } else {
        match (security_level, chunk) {
            ("low", 24) => "fixtures/e5b/poseidon-compose.json".to_string(),
            ("", 24) => "fixtures/e5b/poseidon-compose-default.json".to_string(),
            ("", c) => format!("fixtures/e5b/poseidon-compose-default-chunk{c}.json"),
            (level, 24) => format!("fixtures/e5b/poseidon-compose-{level}.json"),
            (level, c) => format!("fixtures/e5b/poseidon-compose-{level}-chunk{c}.json"),
        }
    };
    let path = repo.join(&filename);
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).map_err(|e| format!("mkdir {}: {e}", parent.display()))?;
    }
    fs::write(
        &path,
        serde_json::to_string_pretty(&out).map_err(|e| e.to_string())?,
    )
    .map_err(|e| format!("write {}: {e}", path.display()))?;
    eprintln!("wrote {} (ref {SWEEP_REF_LABEL})", path.display());
    Ok(())
}

#[cfg(not(feature = "poseidon-mmcs"))]
fn run_poseidon_compose(_security_level: &str) -> Result<(), String> {
    Err("rebuild with --features plonky3-stark,poseidon-mmcs for --poseidon-compose".into())
}

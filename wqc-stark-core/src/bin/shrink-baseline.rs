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
    ShrinkComposeProfile, IDLE_TWO_LEAF_REGRESSION_CEILING_BYTES, SHRINK_GATE_BYTES,
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
    let profile = parse_profile()?;

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

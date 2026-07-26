//! B5 FriFold M4c-style apply: group-fold Y/X steps and strip nested `fold_stark` bytes.

use p3_uni_stark::Proof;

use crate::plonky3_stark::config::WqcStarkConfig;

use super::fri_fold_air::{
    verify_fri_fold_proof, verify_fri_fold_x_native, verify_fri_fold_y_native,
    verify_fri_fold_y_proof, FriFoldStepProof,
};
use super::fri_fold_bind::{bind_fri_fold_bundle_to_proof_width, AggFriFoldBundle};
use super::fri_fold_group::{
    generate_fri_fold_group_proof, verify_fri_fold_group_proof, FriFoldGroupProof,
    FRI_FOLD_GROUP_MAX_STEPS, FRI_FOLD_KIND_X, FRI_FOLD_KIND_Y,
};

/// Leaf/Agg PCS FriFold wire version (after Mmcs fold version in V6 cert).
pub const LEAF_FRI_FOLD_V: u8 = 1;

/// Group folds attached to a PCS certificate (FriFold B5).
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct LeafFriFoldGroups {
    /// All first-layer fold_y steps across proven queries.
    pub fold_ys: Option<FriFoldGroupProof>,
    /// Commit-phase fold_x groups, one per distinct `log_folded_height` (ascending).
    pub fold_xs_by_log_h: Vec<FriFoldGroupProof>,
}

fn strip_fold_starks(steps: &mut [FriFoldStepProof]) {
    for s in steps {
        s.fold_stark.clear();
    }
}

/// Prove one FriFold-X group per distinct height, sequentially (C10′: do not
/// clone every height's steps into a map at once).
fn group_fold_xs_by_log_h(fold_xs: &[FriFoldStepProof]) -> Result<Vec<FriFoldGroupProof>, String> {
    let mut heights: Vec<u32> = fold_xs.iter().map(|s| s.log_folded_height).collect();
    heights.sort_unstable();
    heights.dedup();
    let mut out = Vec::with_capacity(heights.len());
    for log_h in heights {
        let steps: Vec<FriFoldStepProof> = fold_xs
            .iter()
            .filter(|s| s.log_folded_height == log_h)
            .cloned()
            .collect();
        if steps.len() > FRI_FOLD_GROUP_MAX_STEPS {
            return Err(format!(
                "fold_x group at log_h={log_h} too large: {}",
                steps.len()
            ));
        }
        let g = generate_fri_fold_group_proof(FRI_FOLD_KIND_X, &steps, Some(log_h))?;
        drop(steps);
        out.push(g);
    }
    out.shrink_to_fit();
    Ok(out)
}

/// Prove FriFold groups from a limb-only (or mixed) bundle and strip nested STARKs.
pub fn apply_leaf_fri_fold_m4c_folds(
    bundle: &mut AggFriFoldBundle,
) -> Result<LeafFriFoldGroups, String> {
    let fold_ys = if bundle.fold_ys.is_empty() {
        None
    } else {
        if bundle.fold_ys.len() > FRI_FOLD_GROUP_MAX_STEPS {
            return Err(format!("fold_y group too large: {}", bundle.fold_ys.len()));
        }
        Some(generate_fri_fold_group_proof(
            FRI_FOLD_KIND_Y,
            &bundle.fold_ys,
            None,
        )?)
    };

    let fold_xs_by_log_h = if bundle.fold_xs.is_empty() {
        Vec::new()
    } else {
        group_fold_xs_by_log_h(&bundle.fold_xs)?
    };

    strip_fold_starks(&mut bundle.fold_ys);
    strip_fold_starks(&mut bundle.fold_xs);

    Ok(LeafFriFoldGroups {
        fold_ys,
        fold_xs_by_log_h,
    })
}

fn collect_xs_for_group<'a>(
    fold_xs: &'a [FriFoldStepProof],
    group: &FriFoldGroupProof,
) -> Result<Vec<&'a FriFoldStepProof>, String> {
    let selected: Vec<_> = fold_xs
        .iter()
        .filter(|s| s.log_folded_height == group.log_folded_height)
        .collect();
    if selected.len() as u32 != group.step_count {
        return Err(format!(
            "fold_x group log_h={} expects {} steps, found {}",
            group.log_folded_height,
            group.step_count,
            selected.len()
        ));
    }
    Ok(selected)
}

/// Verify FriFold groups when present; otherwise fall back to per-step STARKs.
pub fn bind_fri_fold_with_groups(
    proof: &Proof<WqcStarkConfig>,
    fold_ys: &[FriFoldStepProof],
    fold_xs: &[FriFoldStepProof],
    groups: &LeafFriFoldGroups,
    trace_width: usize,
) -> Result<(), String> {
    bind_fri_fold_bundle_to_proof_width(proof, fold_ys, fold_xs, trace_width)?;

    if let Some(gy) = &groups.fold_ys {
        if !verify_fri_fold_group_proof(fold_ys, gy) {
            return Err("FriFold Y group verification failed".into());
        }
        if fold_ys.iter().any(|s| !s.fold_stark.is_empty()) {
            return Err("FriFold Y residual steps must have empty fold_stark".into());
        }
    } else {
        for (i, step) in fold_ys.iter().enumerate() {
            if step.fold_stark.is_empty() {
                if !verify_fri_fold_y_native(step) {
                    return Err(format!("legacy fold_y native failed at {i}"));
                }
            } else if !verify_fri_fold_y_proof(step) {
                return Err(format!("legacy fold_y STARK failed at {i}"));
            }
        }
    }

    if groups.fold_xs_by_log_h.is_empty() {
        for (i, step) in fold_xs.iter().enumerate() {
            if step.fold_stark.is_empty() {
                if !verify_fri_fold_x_native(step) {
                    return Err(format!("legacy fold_x native failed at {i}"));
                }
            } else if !verify_fri_fold_proof(step) {
                return Err(format!("legacy fold_x STARK failed at {i}"));
            }
        }
    } else {
        let mut covered = 0usize;
        for gx in &groups.fold_xs_by_log_h {
            let selected = collect_xs_for_group(fold_xs, gx)?;
            let owned: Vec<FriFoldStepProof> = selected.into_iter().cloned().collect();
            if !verify_fri_fold_group_proof(&owned, gx) {
                return Err(format!(
                    "FriFold X group verification failed at log_h={}",
                    gx.log_folded_height
                ));
            }
            covered += owned.len();
        }
        if covered != fold_xs.len() {
            return Err(format!(
                "FriFold X group coverage {covered} != cert {}",
                fold_xs.len()
            ));
        }
        if fold_xs.iter().any(|s| !s.fold_stark.is_empty()) {
            return Err("FriFold X residual steps must have empty fold_stark".into());
        }
    }

    Ok(())
}

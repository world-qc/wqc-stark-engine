//! B5 FriFold M4c-style apply: group-fold Y/X steps and strip nested `fold_stark` bytes.

use p3_uni_stark::Proof;

use crate::plonky3_stark::config::WqcStarkConfig;

use super::fri_fold_air::{
    verify_fri_fold_proof, verify_fri_fold_x_native, verify_fri_fold_y_native,
    verify_fri_fold_y_proof, FriFoldStepProof,
};
use super::fri_fold_bind::{
    bind_fri_fold_bundle_to_proof_width, fri_fold_bundle_from_proof, AggFriFoldBundle,
};
use super::fri_fold_group::{
    verify_fri_fold_group_proof, FriFoldGroupProof, FRI_FOLD_GROUP_MAX_STEPS, FRI_FOLD_KIND_YX,
};

/// Leaf/Agg PCS FriFold wire version (after Mmcs fold version in V6 cert).
///
/// v2: when group folds are present, residual step limbs are omitted from the wire
/// and rebuilt from the parent FRI proof at verify.
pub const LEAF_FRI_FOLD_V: u8 = 2;

/// Group folds attached to a PCS certificate (FriFold B5).
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct LeafFriFoldGroups {
    /// All first-layer fold_y steps across proven queries.
    pub fold_ys: Option<FriFoldGroupProof>,
    /// Commit-phase fold_x groups. Prefer a single mixed-height group
    /// (`log_folded_height = u32::MAX`) to cut nested FRI fixed cost; legacy
    /// wire may still carry one group per distinct height.
    pub fold_xs_by_log_h: Vec<FriFoldGroupProof>,
}

fn strip_fold_starks(steps: &mut [FriFoldStepProof]) {
    for s in steps {
        s.fold_stark.clear();
    }
}

/// Rebuild residual FriFold limbs from the parent proof when the wire omitted them (v2).
pub fn resolve_fri_fold_steps_for_groups(
    proof: &Proof<WqcStarkConfig>,
    fold_ys: &[FriFoldStepProof],
    fold_xs: &[FriFoldStepProof],
    groups: &LeafFriFoldGroups,
    trace_width: usize,
) -> Result<(Vec<FriFoldStepProof>, Vec<FriFoldStepProof>), String> {
    if (fold_ys.is_empty() && groups.fold_ys.is_some())
        || (fold_xs.is_empty()
            && (!groups.fold_xs_by_log_h.is_empty()
                || groups
                    .fold_ys
                    .as_ref()
                    .is_some_and(|g| g.kind == FRI_FOLD_KIND_YX)))
    {
        let mut bundle = fri_fold_bundle_from_proof(proof, trace_width)?;
        strip_fold_starks(&mut bundle.fold_ys);
        strip_fold_starks(&mut bundle.fold_xs);
        Ok((bundle.fold_ys, bundle.fold_xs))
    } else {
        Ok((fold_ys.to_vec(), fold_xs.to_vec()))
    }
}

/// Prove FriFold groups from a limb-only (or mixed) bundle and strip nested STARKs.
pub fn apply_leaf_fri_fold_m4c_folds(
    bundle: &mut AggFriFoldBundle,
) -> Result<LeafFriFoldGroups, String> {
    apply_leaf_fri_fold_m4c_folds_with_queries(
        bundle,
        crate::plonky3_stark::config::DEVNET_FRI_NUM_QUERIES,
    )
}

/// Like [`apply_leaf_fri_fold_m4c_folds`], matching nested FRI queries to the outer proof.
///
/// **Host-only FriFold (E5b shrink):** Mmcs groups already attest the opened FRI
/// values; fold algebra is checked natively at bind. Emitting an empty-stark YX
/// marker keeps FriFold wire v2 limb omission without a nested Circle proof.
pub fn apply_leaf_fri_fold_m4c_folds_with_queries(
    bundle: &mut AggFriFoldBundle,
    num_queries: usize,
) -> Result<LeafFriFoldGroups, String> {
    let _ = num_queries;
    let total = bundle.fold_ys.len() + bundle.fold_xs.len();
    if total == 0 {
        return Ok(LeafFriFoldGroups::default());
    }
    if total > FRI_FOLD_GROUP_MAX_STEPS {
        return Err(format!(
            "FriFold host-only marker too many steps: {total} > {FRI_FOLD_GROUP_MAX_STEPS}"
        ));
    }

    strip_fold_starks(&mut bundle.fold_ys);
    strip_fold_starks(&mut bundle.fold_xs);

    // Empty `group_stark` = host-native fold only; kind YX covers Y‖X for limb omit.
    let marker = FriFoldGroupProof {
        kind: FRI_FOLD_KIND_YX,
        step_count: total as u32,
        log_folded_height: u32::MAX,
        group_stark: Vec::new(),
    };
    Ok(LeafFriFoldGroups {
        fold_ys: Some(marker),
        fold_xs_by_log_h: Vec::new(),
    })
}

fn collect_xs_for_group<'a>(
    fold_xs: &'a [FriFoldStepProof],
    group: &FriFoldGroupProof,
) -> Result<Vec<&'a FriFoldStepProof>, String> {
    // Mixed-height groups (`u32::MAX`) cover every fold_x step in order.
    let selected: Vec<_> = if group.log_folded_height == u32::MAX {
        fold_xs.iter().collect()
    } else {
        fold_xs
            .iter()
            .filter(|s| s.log_folded_height == group.log_folded_height)
            .collect()
    };
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
///
/// When residual limbs were omitted from the wire (FriFold v2) but groups are present,
/// rebuild step limbs from the parent proof before bind.
pub fn bind_fri_fold_with_groups(
    proof: &Proof<WqcStarkConfig>,
    fold_ys: &[FriFoldStepProof],
    fold_xs: &[FriFoldStepProof],
    groups: &LeafFriFoldGroups,
    trace_width: usize,
) -> Result<(), String> {
    let (fold_ys_owned, fold_xs_owned) =
        resolve_fri_fold_steps_for_groups(proof, fold_ys, fold_xs, groups, trace_width)?;
    let fold_ys = fold_ys_owned.as_slice();
    let fold_xs = fold_xs_owned.as_slice();

    bind_fri_fold_bundle_to_proof_width(proof, fold_ys, fold_xs, trace_width)?;

    if let Some(gy) = &groups.fold_ys {
        if gy.kind == FRI_FOLD_KIND_YX {
            let mut all = Vec::with_capacity(fold_ys.len() + fold_xs.len());
            all.extend_from_slice(fold_ys);
            all.extend_from_slice(fold_xs);
            if all.len() as u32 != gy.step_count {
                return Err(format!(
                    "FriFold YX step_count {} != limbs {}",
                    gy.step_count,
                    all.len()
                ));
            }
            if gy.group_stark.is_empty() {
                // Host-only marker: native fold checks (Mmcs already attested openings).
                for (i, step) in all.iter().enumerate() {
                    let ok = if i < fold_ys.len() {
                        verify_fri_fold_y_native(step)
                    } else {
                        verify_fri_fold_x_native(step)
                    };
                    if !ok {
                        return Err(format!("FriFold YX host-native failed at {i}"));
                    }
                }
                if all.iter().any(|s| !s.fold_stark.is_empty()) {
                    return Err("FriFold YX residual steps must have empty fold_stark".into());
                }
                return Ok(());
            }
            if !verify_fri_fold_group_proof(&all, gy) {
                return Err("FriFold YX group verification failed".into());
            }
            if all.iter().any(|s| !s.fold_stark.is_empty()) {
                return Err("FriFold YX residual steps must have empty fold_stark".into());
            }
            return Ok(());
        }
        if gy.group_stark.is_empty() {
            for (i, step) in fold_ys.iter().enumerate() {
                if !verify_fri_fold_y_native(step) {
                    return Err(format!("FriFold Y host-native failed at {i}"));
                }
            }
        } else if !verify_fri_fold_group_proof(fold_ys, gy) {
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
        if groups
            .fold_ys
            .as_ref()
            .is_some_and(|g| g.kind == FRI_FOLD_KIND_YX)
        {
            // Covered by YX branch above.
        } else {
            for (i, step) in fold_xs.iter().enumerate() {
                if step.fold_stark.is_empty() {
                    if !verify_fri_fold_x_native(step) {
                        return Err(format!("legacy fold_x native failed at {i}"));
                    }
                } else if !verify_fri_fold_proof(step) {
                    return Err(format!("legacy fold_x STARK failed at {i}"));
                }
            }
        }
    } else {
        let mut covered = 0usize;
        for gx in &groups.fold_xs_by_log_h {
            let selected = collect_xs_for_group(fold_xs, gx)?;
            let owned: Vec<FriFoldStepProof> = selected.into_iter().cloned().collect();
            if gx.group_stark.is_empty() {
                for (i, step) in owned.iter().enumerate() {
                    if !verify_fri_fold_x_native(step) {
                        return Err(format!(
                            "FriFold X host-native failed at log_h={} step {i}",
                            gx.log_folded_height
                        ));
                    }
                }
            } else if !verify_fri_fold_group_proof(&owned, gx) {
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

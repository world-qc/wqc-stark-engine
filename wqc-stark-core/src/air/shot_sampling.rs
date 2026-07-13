//! C2c extension: per-shot MEASURE Bernoulli sampling constraints.
//!
//! Host algebraic path replays `StdRng::seed_from_u64(shot_seed)` exactly as
//! `wqc-core` mid-circuit noiseless MEASURE (`rng.gen::<f64>() < p0/(p0+p1)`).
//! Plonky3 `ShotSamplingAir` then zk-proves the fixed-point Bernoulli relation
//! for the same reconstructed `u` values (seed→u remains host-bound).

use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

use crate::trajectory::{TrajectoryMeasureEvent, TrajectorySegment};

/// Fixed-point scale for Plonky3 shot-sampling AIR (`p0`, `p1`, `u`).
pub const SHOT_SAMPLING_SCALE: u32 = 1_000;

/// Bits allocated to the non-negative Bernoulli gap witness (`< SCALE²`).
pub const SHOT_SAMPLING_GAP_BITS: usize = 20;

/// Soft cap on total MEASURE events included in one shot-sampling STARK.
pub const TRAJ_SHOT_SAMPLING_ZK_MAX_EVENTS: usize = 2_048;

/// One MEASURE coin-flip after reconstructing `u` from the shot PRNG.
#[derive(Debug, Clone, PartialEq)]
pub struct ShotSamplingEvent {
    pub shot_index: u64,
    pub measure_index: u32,
    pub p0: f64,
    pub p1: f64,
    pub sample_u: f64,
    pub outcome: u8,
}

/// Expected Bernoulli bit from `(p0, p1, u)` — matches mid-circuit noiseless MEASURE.
pub fn bernoulli_outcome(p0: f64, p1: f64, sample_u: f64) -> u8 {
    let denom = (p0 + p1).max(1e-30);
    if sample_u < p0 / denom {
        0
    } else {
        1
    }
}

/// Replays `StdRng` per shot and collects every MEASURE sample (noiseless semantics).
pub fn collect_shot_sampling_events(segment: &TrajectorySegment) -> Option<Vec<ShotSamplingEvent>> {
    let mut events = Vec::new();
    for shot in &segment.traces {
        let mut rng = StdRng::seed_from_u64(shot.shot_seed);
        for (measure_index, m) in shot.measures.iter().enumerate() {
            let sample_u: f64 = rng.gen();
            events.push(ShotSamplingEvent {
                shot_index: shot.shot_index,
                measure_index: measure_index as u32,
                p0: m.p0,
                p1: m.p1,
                sample_u,
                outcome: m.outcome,
            });
        }
    }
    Some(events)
}

fn measure_matches_sample(m: &TrajectoryMeasureEvent, sample_u: f64) -> bool {
    m.outcome == bernoulli_outcome(m.p0, m.p1, sample_u)
}

/// Algebraic verify: each claimed MEASURE outcome follows `StdRng(shot_seed)`.
pub fn evaluate_trajectory_shot_sampling_constraints(segment: &TrajectorySegment) -> bool {
    for shot in &segment.traces {
        let mut rng = StdRng::seed_from_u64(shot.shot_seed);
        for m in &shot.measures {
            let sample_u: f64 = rng.gen();
            if !measure_matches_sample(m, sample_u) {
                return false;
            }
        }
    }
    true
}

/// Returns true when the segment can carry a Plonky3 shot-sampling STARK.
pub fn segment_supports_shot_sampling_zk(segment: &TrajectorySegment) -> bool {
    let mut total = 0usize;
    for shot in &segment.traces {
        total = total.saturating_add(shot.measures.len());
        if total > TRAJ_SHOT_SAMPLING_ZK_MAX_EVENTS {
            return false;
        }
        for m in &shot.measures {
            if m.outcome > 1 {
                return false;
            }
        }
    }
    total > 0 && evaluate_trajectory_shot_sampling_constraints(segment)
}

/// Quantize probability / sample into `[0, SCALE]` integers for the AIR.
pub fn quantize_unit(val: f64) -> u32 {
    let scaled = (val * f64::from(SHOT_SAMPLING_SCALE)).round();
    if !scaled.is_finite() || scaled <= 0.0 {
        0
    } else if scaled >= f64::from(SHOT_SAMPLING_SCALE) {
        SHOT_SAMPLING_SCALE
    } else {
        scaled as u32
    }
}

/// Builds fixed-point Bernoulli witnesses `(p0, p1, u, outcome, gap)` matching `outcome`.
///
/// Integer rule: `outcome == 0` iff `u * (p0 + p1) < p0 * SCALE` (after optional ±1 nudge of `u`
/// so quantization agrees with the exact f64 decision already checked algebraically).
pub fn fixed_point_bernoulli_witnesses(
    p0: f64,
    p1: f64,
    sample_u: f64,
    outcome: u8,
) -> Option<(u32, u32, u32, u32)> {
    if outcome > 1 {
        return None;
    }
    let mut p0_i = quantize_unit(p0);
    let mut p1_i = quantize_unit(p1);
    if p0_i + p1_i == 0 {
        // Degenerate mass — treat as deterministic outcome 0 when p-mass vanished.
        p0_i = SHOT_SAMPLING_SCALE;
        p1_i = 0;
    }
    let mut u_i = quantize_unit(sample_u);
    let scale = u64::from(SHOT_SAMPLING_SCALE);

    let lhs = |u: u32, p0: u32, p1: u32| -> u64 { u64::from(u) * u64::from(p0 + p1) };
    let rhs = |p0: u32| -> u64 { u64::from(p0) * scale };

    let matches = |u: u32, p0: u32, p1: u32| -> bool {
        let lt = lhs(u, p0, p1) < rhs(p0);
        if outcome == 0 {
            lt
        } else {
            !lt
        }
    };

    if !matches(u_i, p0_i, p1_i) {
        // Nudge u by at most a few ulps of the SCALE grid toward the claimed outcome.
        let mut found = false;
        for delta in 1..=4u32 {
            for cand in [u_i.saturating_add(delta), u_i.saturating_sub(delta)] {
                let cand = cand.min(SHOT_SAMPLING_SCALE);
                if matches(cand, p0_i, p1_i) {
                    u_i = cand;
                    found = true;
                    break;
                }
            }
            if found {
                break;
            }
        }
        if !found {
            return None;
        }
    }

    let left = lhs(u_i, p0_i, p1_i);
    let right = rhs(p0_i);
    let gap = if outcome == 0 {
        right.checked_sub(left)?.checked_sub(1)?
    } else {
        left.checked_sub(right)?
    };
    if gap >= (1u64 << SHOT_SAMPLING_GAP_BITS) {
        return None;
    }
    Some((p0_i, p1_i, u_i, gap as u32))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::trajectory::{TrajectoryShotTrace, TrajectoryMeasureEvent};

    fn demo_segment(outcome0: u8) -> TrajectorySegment {
        let mut rng = StdRng::seed_from_u64(7);
        let u: f64 = rng.gen();
        let p0 = 0.5;
        let p1 = 0.5;
        let expected = bernoulli_outcome(p0, p1, u);
        let _ = expected;
        TrajectorySegment {
            sample_seed: 7,
            shots: 1,
            measurement_spec_hash: "spec".into(),
            trajectory_digest: "digest".into(),
            qubit_count: 1,
            unitary_link_digest: String::new(),
            traces: vec![TrajectoryShotTrace {
                shot_index: 0,
                shot_seed: 7,
                final_outcome: format!("{outcome0}"),
                classical_bits: vec![outcome0],
                measures: vec![TrajectoryMeasureEvent {
                    gate_index: 0,
                    qubit: 0,
                    cbit: 0,
                    p0,
                    p1,
                    outcome: {
                        let mut rng = StdRng::seed_from_u64(7);
                        let u: f64 = rng.gen();
                        bernoulli_outcome(p0, p1, u)
                    },
                    pre_measure_statevector_digest: String::new(),
                }],
            }],
            marginal_witnesses: Vec::new(),
        }
    }

    #[test]
    fn shot_sampling_accepts_rng_consistent_outcome() {
        let segment = demo_segment(0);
        assert!(evaluate_trajectory_shot_sampling_constraints(&segment));
        assert!(segment_supports_shot_sampling_zk(&segment));
    }

    #[test]
    fn shot_sampling_rejects_flipped_outcome() {
        let mut segment = demo_segment(0);
        segment.traces[0].measures[0].outcome ^= 1;
        assert!(!evaluate_trajectory_shot_sampling_constraints(&segment));
    }

    #[test]
    fn fixed_point_witnesses_agree_with_outcome() {
        let segment = demo_segment(0);
        let m = &segment.traces[0].measures[0];
        let mut rng = StdRng::seed_from_u64(7);
        let u: f64 = rng.gen();
        let (p0_i, p1_i, u_i, gap) =
            fixed_point_bernoulli_witnesses(m.p0, m.p1, u, m.outcome).expect("witness");
        let lhs = u64::from(u_i) * u64::from(p0_i + p1_i);
        let rhs = u64::from(p0_i) * u64::from(SHOT_SAMPLING_SCALE);
        if m.outcome == 0 {
            assert!(lhs < rhs);
            assert_eq!(rhs - lhs - 1, u64::from(gap));
        } else {
            assert!(lhs >= rhs);
            assert_eq!(lhs - rhs, u64::from(gap));
        }
    }
}

//! C2c: Z-marginal constraints linking mid-circuit MEASURE probabilities to pre-measure statevectors.

use p3_field::PrimeCharacteristicRing;

use crate::trajectory::{TrajectoryMarginalWitness, TrajectorySegment};

/// Fixed-point scale shared with Born / quantum execution AIR.
pub const TRAJ_MARGINAL_SCALE: f64 = 10_000.0;

/// Allowed absolute error when comparing Z marginals (f64).
pub const TRAJ_MARGINAL_EPSILON: f64 = 1e-5;

/// Maximum qubit width for in-segment trajectory marginal zk (streaming Born AIR).
pub const TRAJ_MARGINAL_ZK_MAX_QUBITS: usize = 16;

/// Dense host marginal check. Matches `wqc-core` mid-circuit sampling (`qubit_count <= 20`).
/// Wider than the zk cap: algebraic verify still runs when a zk tail is not emitted.
pub const TRAJ_MARGINAL_HOST_MAX_QUBITS: usize = 20;

/// Computational-basis indices where `qubit` reads 0 / 1.
pub fn z_marginal_basis_groups(
    qubit: usize,
    qubit_count: usize,
) -> Option<(Vec<usize>, Vec<usize>)> {
    if qubit_count == 0 || qubit_count > TRAJ_MARGINAL_HOST_MAX_QUBITS || qubit >= qubit_count {
        return None;
    }
    let dim = 1usize << qubit_count;
    let mut group0 = Vec::new();
    let mut group1 = Vec::new();
    for basis in 0..dim {
        if (basis >> qubit) & 1 == 0 {
            group0.push(basis);
        } else {
            group1.push(basis);
        }
    }
    Some((group0, group1))
}

/// Born-style Z marginals `(p0, p1)` from a dense pre-measure statevector.
pub fn z_marginal_from_statevector(
    statevector: &[(f64, f64)],
    qubit: usize,
    qubit_count: usize,
) -> Option<(f64, f64)> {
    let dim = 1usize << qubit_count;
    if statevector.len() != dim {
        return None;
    }
    let (group0, group1) = z_marginal_basis_groups(qubit, qubit_count)?;
    let mass = |group: &[usize]| -> f64 {
        group
            .iter()
            .map(|&basis| {
                let (re, im) = statevector[basis];
                re * re + im * im
            })
            .sum()
    };
    Some((mass(&group0), mass(&group1)))
}

/// Host-side constraint accumulator for one marginal witness (`ZERO` iff binding holds).
pub fn evaluate_marginal_witness_sum<FR: PrimeCharacteristicRing + Copy>(
    statevector: &[(f64, f64)],
    qubit: usize,
    qubit_count: usize,
    claimed_p0: f64,
    claimed_p1: f64,
    f64_to_field: impl Fn(f64) -> FR,
) -> FR {
    use super::distribution::BORN_FIXED_POINT_SCALE;
    let scale = FR::from_u32(BORN_FIXED_POINT_SCALE as u32);
    let mut acc = FR::ZERO;

    let Some((group0, group1)) = z_marginal_basis_groups(qubit, qubit_count) else {
        return FR::ONE;
    };

    for (claimed, group) in [(claimed_p0, group0), (claimed_p1, group1)] {
        let claimed_f = f64_to_field(claimed);
        let mut mass = FR::ZERO;
        for basis in group {
            let (re, im) = statevector[basis];
            let re_f = f64_to_field(re);
            let im_f = f64_to_field(im);
            mass += re_f * re_f + im_f * im_f;
        }
        acc += claimed_f * scale - mass;
    }

    acc
}

fn within_marginal_epsilon(claimed: f64, actual: f64) -> bool {
    claimed.is_finite() && actual.is_finite() && (claimed - actual).abs() <= TRAJ_MARGINAL_EPSILON
}

fn witness_matches_claimed_probs(witness: &TrajectoryMarginalWitness, qubit_count: usize) -> bool {
    let Some((p0, p1)) = z_marginal_from_statevector(
        &witness.pre_measure_statevector,
        witness.qubit as usize,
        qubit_count,
    ) else {
        return false;
    };
    within_marginal_epsilon(witness.reference_p0, p0)
        && within_marginal_epsilon(witness.reference_p1, p1)
}

/// Why a marginal witness fails, without printing. `None` when the constraints hold.
pub fn marginal_constraint_error(segment: &TrajectorySegment) -> Option<&'static str> {
    if segment.marginal_witnesses.is_empty() {
        return None;
    }
    let qubit_count = segment.qubit_count as usize;
    if qubit_count == 0 || qubit_count > TRAJ_MARGINAL_HOST_MAX_QUBITS {
        return Some("qubit_count out of range");
    }

    for witness in &segment.marginal_witnesses {
        let recomputed = crate::distribution::calculate_terminal_statevector_digest(
            &witness.pre_measure_statevector,
        );
        if recomputed != witness.pre_measure_statevector_digest {
            return Some("witness digest mismatch");
        }
        if !witness_matches_claimed_probs(witness, qubit_count) {
            return Some("witness probabilities do not match pre-measure statevector");
        }
    }

    for shot in &segment.traces {
        for m in &shot.measures {
            if m.pre_measure_statevector_digest.is_empty() {
                return Some("shot pre-measure digest missing");
            }
            let witness = segment.marginal_witnesses.iter().find(|w| {
                w.pre_measure_statevector_digest == m.pre_measure_statevector_digest
                    && w.qubit == m.qubit
            });
            let Some(witness) = witness else {
                return Some("shot has no matching witness");
            };
            if !within_marginal_epsilon(m.p0, witness.reference_p0)
                || !within_marginal_epsilon(m.p1, witness.reference_p1)
            {
                // Branch-dependent states share digest; recompute from witness statevector.
                let Some((oracle_p0, oracle_p1)) = z_marginal_from_statevector(
                    &witness.pre_measure_statevector,
                    m.qubit as usize,
                    qubit_count,
                ) else {
                    return Some("witness statevector shape invalid");
                };
                if !within_marginal_epsilon(m.p0, oracle_p0)
                    || !within_marginal_epsilon(m.p1, oracle_p1)
                {
                    return Some("shot probabilities do not match witness");
                }
            }
        }
    }

    None
}

/// Algebraic verify: witnesses + per-shot claimed `p0/p1` vs pre-measure statevectors.
pub fn evaluate_trajectory_marginal_constraints(segment: &TrajectorySegment) -> bool {
    marginal_constraint_error(segment).is_none()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::distribution::calculate_terminal_statevector_digest;
    use crate::trajectory::{TrajectoryMeasureEvent, TrajectoryShotTrace};

    fn plus_state() -> (Vec<(f64, f64)>, f64, f64) {
        let inv_sqrt2 = 1.0f64 / 2.0f64.sqrt();
        let sv = vec![(inv_sqrt2, 0.0), (inv_sqrt2, 0.0)];
        let (p0, p1) = z_marginal_from_statevector(&sv, 0, 1).unwrap();
        (sv, p0, p1)
    }

    fn segment_from(
        sv: Vec<(f64, f64)>,
        qubit_count: u32,
        reference_p0: f64,
        reference_p1: f64,
        shot_p0: f64,
        shot_p1: f64,
    ) -> TrajectorySegment {
        let digest = calculate_terminal_statevector_digest(&sv);
        TrajectorySegment {
            sample_seed: 1,
            shots: 1,
            measurement_spec_hash: "spec".into(),
            trajectory_digest: "ignored".into(),
            qubit_count,
            unitary_link_digest: String::new(),
            traces: vec![TrajectoryShotTrace {
                shot_index: 0,
                shot_seed: 1,
                final_outcome: "0".into(),
                classical_bits: vec![0],
                measures: vec![TrajectoryMeasureEvent {
                    gate_index: 0,
                    qubit: 0,
                    cbit: 0,
                    p0: shot_p0,
                    p1: shot_p1,
                    outcome: 0,
                    pre_measure_statevector_digest: digest.clone(),
                }],
            }],
            marginal_witnesses: vec![TrajectoryMarginalWitness {
                qubit: 0,
                reference_p0,
                reference_p1,
                pre_measure_statevector: sv,
                pre_measure_statevector_digest: digest,
            }],
        }
    }

    #[test]
    fn plus_state_z_marginal_on_qubit0() {
        let (_sv, p0, p1) = plus_state();
        assert!((p0 - 0.5).abs() < 1e-9);
        assert!((p1 - 0.5).abs() < 1e-9);
    }

    #[test]
    fn marginal_accepts_shot_inside_epsilon_of_oracle() {
        let (sv, p0, p1) = plus_state();
        let segment = segment_from(sv, 1, p0 + 6e-6, p1 - 6e-6, p0 - 6e-6, p1 + 6e-6);
        assert_eq!(marginal_constraint_error(&segment), None);
    }

    #[test]
    fn marginal_rejects_shot_outside_epsilon_nan_and_bad_links() {
        let (sv, p0, p1) = plus_state();
        let drifted = segment_from(sv.clone(), 1, p0, p1, p0 + 2e-5, p1);
        assert_eq!(
            marginal_constraint_error(&drifted),
            Some("shot probabilities do not match witness")
        );

        let nan = segment_from(sv.clone(), 1, p0, p1, f64::NAN, p1);
        assert_eq!(
            marginal_constraint_error(&nan),
            Some("shot probabilities do not match witness")
        );

        let mut digest = segment_from(sv.clone(), 1, p0, p1, p0, p1);
        digest.marginal_witnesses[0].pre_measure_statevector_digest = "other".into();
        assert_eq!(
            marginal_constraint_error(&digest),
            Some("witness digest mismatch")
        );

        let mut missing = segment_from(sv, 1, p0, p1, p0, p1);
        missing.traces[0].measures[0].pre_measure_statevector_digest = "missing".into();
        assert_eq!(
            marginal_constraint_error(&missing),
            Some("shot has no matching witness")
        );
    }

    #[test]
    fn host_marginal_allows_seventeen_qubits_and_rejects_past_twenty() {
        let mut sv = vec![(0.0, 0.0); 1 << 17];
        sv[0] = (1.0, 0.0);
        let (p0, p1) = z_marginal_from_statevector(&sv, 0, 17).expect("host marginal");
        assert!((p0 - 1.0).abs() < 1e-12);
        assert!(p1.abs() < 1e-12);
        let segment = segment_from(sv, 17, p0, p1, p0, p1);
        assert_eq!(marginal_constraint_error(&segment), None);

        let (plus, pp0, pp1) = plus_state();
        let wide = segment_from(plus, 21, pp0, pp1, pp0, pp1);
        assert_eq!(
            marginal_constraint_error(&wide),
            Some("qubit_count out of range")
        );
    }
}

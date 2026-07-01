//! C2c: Z-marginal constraints linking mid-circuit MEASURE probabilities to pre-measure statevectors.

use p3_field::PrimeCharacteristicRing;
use p3_mersenne_31::Mersenne31;

use crate::trajectory::{TrajectoryMarginalWitness, TrajectorySegment};

/// Fixed-point scale shared with Born / quantum execution AIR.
pub const TRAJ_MARGINAL_SCALE: f64 = 10_000.0;

/// Allowed absolute error when comparing Z marginals (f64).
pub const TRAJ_MARGINAL_EPSILON: f64 = 1e-5;

/// Maximum qubit width for in-segment trajectory marginal zk (single-row wide trace).
pub const TRAJ_MARGINAL_ZK_MAX_QUBITS: usize = 4;

/// Computational-basis indices where `qubit` reads 0 / 1.
pub fn z_marginal_basis_groups(qubit: usize, qubit_count: usize) -> Option<(Vec<usize>, Vec<usize>)> {
    if qubit_count > TRAJ_MARGINAL_ZK_MAX_QUBITS || qubit >= qubit_count {
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

fn witness_matches_claimed_probs(witness: &TrajectoryMarginalWitness, qubit_count: usize) -> bool {
    let Some((p0, p1)) =
        z_marginal_from_statevector(&witness.pre_measure_statevector, witness.qubit as usize, qubit_count)
    else {
        return false;
    };
    (witness.reference_p0 - p0).abs() <= TRAJ_MARGINAL_EPSILON
        && (witness.reference_p1 - p1).abs() <= TRAJ_MARGINAL_EPSILON
}

/// Algebraic verify: witnesses + per-shot claimed `p0/p1` vs pre-measure statevectors.
pub fn evaluate_trajectory_marginal_constraints(segment: &TrajectorySegment) -> bool {
    if segment.marginal_witnesses.is_empty() {
        return true;
    }
    let qubit_count = segment.qubit_count as usize;
    if qubit_count == 0 || qubit_count > TRAJ_MARGINAL_ZK_MAX_QUBITS {
        return false;
    }

    for witness in &segment.marginal_witnesses {
        let recomputed =
            crate::distribution::calculate_terminal_statevector_digest(&witness.pre_measure_statevector);
        if recomputed != witness.pre_measure_statevector_digest {
            return false;
        }
        if !witness_matches_claimed_probs(witness, qubit_count) {
            return false;
        }
        let sum = evaluate_marginal_witness_sum::<Mersenne31>(
            &witness.pre_measure_statevector,
            witness.qubit as usize,
            qubit_count,
            witness.reference_p0,
            witness.reference_p1,
            super::f64_to_m31,
        );
        if sum != Mersenne31::ZERO {
            return false;
        }
    }

    for shot in &segment.traces {
        for m in &shot.measures {
            if m.pre_measure_statevector_digest.is_empty() {
                return false;
            }
            let witness = segment.marginal_witnesses.iter().find(|w| {
                w.pre_measure_statevector_digest == m.pre_measure_statevector_digest
                    && w.qubit == m.qubit
            });
            let Some(witness) = witness else {
                return false;
            };
            if (m.p0 - witness.reference_p0).abs() > TRAJ_MARGINAL_EPSILON
                || (m.p1 - witness.reference_p1).abs() > TRAJ_MARGINAL_EPSILON
            {
                // Branch-dependent states share digest; recompute from witness statevector.
                let Some((oracle_p0, oracle_p1)) = z_marginal_from_statevector(
                    &witness.pre_measure_statevector,
                    m.qubit as usize,
                    qubit_count,
                ) else {
                    return false;
                };
                if (m.p0 - oracle_p0).abs() > TRAJ_MARGINAL_EPSILON
                    || (m.p1 - oracle_p1).abs() > TRAJ_MARGINAL_EPSILON
                {
                    return false;
                }
            }
        }
    }

    true
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn plus_state_z_marginal_on_qubit0() {
        let inv_sqrt2 = 1.0f64 / 2.0f64.sqrt();
        let sv = vec![(inv_sqrt2, 0.0), (inv_sqrt2, 0.0)];
        let (p0, p1) = z_marginal_from_statevector(&sv, 0, 1).unwrap();
        assert!((p0 - 0.5).abs() < 1e-9);
        assert!((p1 - 0.5).abs() < 1e-9);
    }
}

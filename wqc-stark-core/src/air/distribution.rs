//! C2b: Born-rule constraints linking terminal statevector amplitudes to outcome probabilities.

use std::collections::BTreeMap;

use p3_field::PrimeCharacteristicRing;
use p3_mersenne_31::Mersenne31;

use crate::distribution::DistributionSegment;

/// Maximum qubit width for in-segment terminal statevector (C2b v1).
pub const BORN_AIR_MAX_QUBITS: usize = 16;

/// Fixed-point scale shared with quantum execution AIR.
pub const BORN_FIXED_POINT_SCALE: f64 = 10_000.0;

/// Allowed absolute error when comparing Born probabilities (f64).
pub const BORN_PROB_EPSILON: f64 = 1e-5;

/// One terminal MEASURE wire in program order.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BornMeasureSpec {
    pub qubit: u32,
    pub cbit: u32,
}

/// Qiskit-order bitstring from classical register contents (`cbit 0` = rightmost).
pub fn outcome_key_from_classical(classical: &[u8]) -> String {
    let n = classical.len();
    let mut bits = vec![b'0'; n];
    for (cbit, &val) in classical.iter().enumerate() {
        let pos = n - 1 - cbit;
        bits[pos] = if val == 1 { b'1' } else { b'0' };
    }
    unsafe { String::from_utf8_unchecked(bits) }
}

fn outcome_key(
    basis_index: usize,
    measures: &[BornMeasureSpec],
    classical_bit_count: usize,
) -> String {
    let mut bits = vec![0u8; classical_bit_count];
    for spec in measures {
        let bit = (basis_index >> spec.qubit) & 1;
        bits[spec.cbit as usize] = bit as u8;
    }
    outcome_key_from_classical(&bits)
}

/// Born probabilities for terminal Z measurements from a dense terminal statevector.
pub fn born_probabilities_from_statevector(
    statevector: &[(f64, f64)],
    qubit_count: usize,
    measures: &[BornMeasureSpec],
    classical_bit_count: usize,
) -> Option<BTreeMap<String, f64>> {
    if qubit_count > BORN_AIR_MAX_QUBITS {
        return None;
    }
    let dim = 1usize << qubit_count;
    if statevector.len() != dim {
        return None;
    }
    if classical_bit_count == 0 || measures.is_empty() {
        return None;
    }

    let mut probs: BTreeMap<String, f64> = BTreeMap::new();
    for (basis, (re, im)) in statevector.iter().enumerate() {
        let p = re * re + im * im;
        if p == 0.0 {
            continue;
        }
        let key = outcome_key(basis, measures, classical_bit_count);
        *probs.entry(key).or_insert(0.0) += p;
    }
    Some(probs)
}

fn probabilities_match(claimed: &[(String, f64)], recomputed: &BTreeMap<String, f64>) -> bool {
    if claimed.len() != recomputed.len() {
        return false;
    }
    for (key, claimed_p) in claimed {
        let Some(actual) = recomputed.get(key) else {
            return false;
        };
        if (claimed_p - actual).abs() > BORN_PROB_EPSILON {
            return false;
        }
    }
    true
}

/// Returns `0` when Born binding data is present and consistent; nonzero error code otherwise.
pub fn evaluate_born_constraint_sum(segment: &DistributionSegment) -> u32 {
    let Some(binding) = &segment.born_binding else {
        return 0;
    };

    if binding.qubit_count as usize > BORN_AIR_MAX_QUBITS {
        eprintln!("[STARK Core][Born] qubit_count exceeds C2b limit");
        return 1;
    }

    let measures: Vec<BornMeasureSpec> = binding
        .measures
        .iter()
        .map(|(q, c)| BornMeasureSpec {
            qubit: *q,
            cbit: *c,
        })
        .collect();

    let recomputed = match born_probabilities_from_statevector(
        &binding.terminal_statevector,
        binding.qubit_count as usize,
        &measures,
        binding.classical_bit_count as usize,
    ) {
        Some(probs) => probs,
        None => {
            eprintln!("[STARK Core][Born] invalid terminal statevector shape");
            return 2;
        }
    };

    if !probabilities_match(&segment.probabilities, &recomputed) {
        eprintln!("[STARK Core][Born] claimed probabilities do not match statevector Born rule");
        return 3;
    }

    let total: f64 = recomputed.values().sum();
    if (total - 1.0).abs() > BORN_PROB_EPSILON && total > 0.0 {
        eprintln!("[STARK Core][Born] probability mass deviates from 1.0 (sum={total})");
        return 4;
    }

    0
}

/// Mersenne31-style accumulator for Born constraints (`ZERO` iff satisfied or not applicable).
pub fn born_constraint_accumulator(segment: &DistributionSegment) -> Mersenne31 {
    if evaluate_born_constraint_sum(segment) == 0 {
        Mersenne31::ZERO
    } else {
        Mersenne31::ONE
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::distribution::{calculate_probability_digest, BornBinding};

    #[test]
    fn bell_state_born_probs_match_segment() {
        let inv_sqrt2 = 1.0f64 / 2.0f64.sqrt();
        let sv = vec![(inv_sqrt2, 0.0), (0.0, 0.0), (0.0, 0.0), (inv_sqrt2, 0.0)];
        let measures = vec![
            BornMeasureSpec { qubit: 0, cbit: 0 },
            BornMeasureSpec { qubit: 1, cbit: 1 },
        ];
        let probs = born_probabilities_from_statevector(&sv, 2, &measures, 2).expect("born");
        let p00 = probs.get("00").copied().unwrap_or(0.0);
        let p11 = probs.get("11").copied().unwrap_or(0.0);
        assert!((p00 - 0.5).abs() < 1e-9);
        assert!((p11 - 0.5).abs() < 1e-9);

        let prob_vec: Vec<(String, f64)> = probs.into_iter().collect();
        let binding = BornBinding::from_specs(2, 2, &[(0, 0), (1, 1)], sv).expect("bind");
        let segment = DistributionSegment {
            sample_seed: 1,
            shots: 128,
            measurement_spec_hash: "spec".into(),
            probability_digest: calculate_probability_digest(&prob_vec),
            probabilities: prob_vec,
            born_binding: Some(binding),
        };
        assert_eq!(evaluate_born_constraint_sum(&segment), 0);
    }

    #[test]
    fn tampered_born_probs_rejected() {
        let inv_sqrt2 = 1.0f64 / 2.0f64.sqrt();
        let sv = vec![(inv_sqrt2, 0.0), (0.0, 0.0), (0.0, 0.0), (inv_sqrt2, 0.0)];
        let binding = BornBinding::from_specs(2, 2, &[(0, 0), (1, 1)], sv).expect("bind");
        let segment = DistributionSegment {
            sample_seed: 1,
            shots: 128,
            measurement_spec_hash: "spec".into(),
            probability_digest: calculate_probability_digest(&[("0".into(), 1.0)]),
            probabilities: vec![("0".into(), 1.0)],
            born_binding: Some(binding),
        };
        assert_ne!(evaluate_born_constraint_sum(&segment), 0);
    }

    #[test]
    fn single_qubit_h_state_born_roundtrip() {
        let inv_sqrt2 = 1.0f64 / 2.0f64.sqrt();
        let sv = vec![(inv_sqrt2, 0.0), (inv_sqrt2, 0.0)];
        let measures = vec![BornMeasureSpec { qubit: 0, cbit: 0 }];
        let probs = born_probabilities_from_statevector(&sv, 1, &measures, 1).expect("born");
        assert!((probs.get("0").copied().unwrap_or(0.0) - 0.5).abs() < 1e-9);
        assert!((probs.get("1").copied().unwrap_or(0.0) - 0.5).abs() < 1e-9);
    }
}

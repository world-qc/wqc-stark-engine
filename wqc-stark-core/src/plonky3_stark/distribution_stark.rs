//! C2b Born-rule Plonky3 uni-STARK prove / verify.

pub use super::distribution_air::{DistributionAir, BORN_ZK_MAX_QUBITS, BORN_ZK_SCALE};

use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::dense::RowMajorMatrix;
use p3_mersenne_31::Mersenne31;
use p3_uni_stark::{prove, verify};

use crate::air::distribution::{born_probabilities_from_statevector, BornMeasureSpec};
use crate::air::{f64_to_m31, pad_air_matrix_for_uni_stark};
use crate::distribution::{BornBinding, DistributionSegment};

use super::config::{devnet_circle_config, WqcStarkConfig};
use super::transcript_born::{decode_born_stark_owned, encode_born_stark};

/// Public binding for a Born-rule distribution STARK.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BornStarkContext<'a> {
    pub sub_task_id: &'a str,
    pub probability_digest: &'a str,
}

/// Lists computational-basis indices per outcome key (segment probability order).
pub fn outcome_basis_groups(
    binding: &BornBinding,
    outcome_keys: &[String],
) -> Option<Vec<Vec<usize>>> {
    let qubit_count = binding.qubit_count as usize;
    if qubit_count > BORN_ZK_MAX_QUBITS {
        return None;
    }
    let dim = 1usize << qubit_count;
    if binding.terminal_statevector.len() != dim {
        return None;
    }

    let measures: Vec<BornMeasureSpec> = binding
        .measures
        .iter()
        .map(|(q, c)| BornMeasureSpec {
            qubit: *q,
            cbit: *c,
        })
        .collect();

    let mut groups = Vec::with_capacity(outcome_keys.len());
    for key in outcome_keys {
        let mut indices = Vec::new();
        for basis in 0..dim {
            let mut bits = vec![0u8; binding.classical_bit_count as usize];
            for spec in &measures {
                let bit = (basis >> spec.qubit) & 1;
                bits[spec.cbit as usize] = bit as u8;
            }
            let outcome =
                crate::air::distribution::outcome_key_from_classical(&bits);
            if &outcome == key {
                indices.push(basis);
            }
        }
        if indices.is_empty() {
            return None;
        }
        groups.push(indices);
    }
    Some(groups)
}

fn build_distribution_air(segment: &DistributionSegment) -> Option<DistributionAir> {
    let binding = segment.born_binding.as_ref()?;
    let qubit_count = binding.qubit_count as usize;
    if qubit_count > BORN_ZK_MAX_QUBITS {
        return None;
    }
    let outcome_keys: Vec<String> = segment.probabilities.iter().map(|(k, _)| k.clone()).collect();
    let outcome_groups = outcome_basis_groups(binding, &outcome_keys)?;
    Some(DistributionAir {
        dim: 1usize << qubit_count,
        outcome_groups,
    })
}

fn build_distribution_matrix(
    air: &DistributionAir,
    segment: &DistributionSegment,
) -> Option<RowMajorMatrix<Mersenne31>> {
    let binding = segment.born_binding.as_ref()?;
    let scale = Mersenne31::from_u32(BORN_ZK_SCALE);
    let scale_inv = scale.inverse();
    let mut row = Vec::with_capacity(air.width());

    for (re, im) in &binding.terminal_statevector {
        row.push(f64_to_m31(*re));
        row.push(f64_to_m31(*im));
    }

    for group in &air.outcome_groups {
        let mut mass = Mersenne31::ZERO;
        for &basis in group {
            let re = row[2 * basis];
            let im = row[2 * basis + 1];
            mass += re * re + im * im;
        }
        row.push(mass * scale_inv);
    }

    if air.evaluate_first_row_sum::<Mersenne31>(&row) != Mersenne31::ZERO {
        return None;
    }

    let mut values = row.clone();
    values.extend(row);
    Some(RowMajorMatrix::new(values, air.width()))
}

/// Returns true when a segment can be zk-proved with `DistributionAir`.
pub fn segment_supports_born_zk(segment: &DistributionSegment) -> bool {
    if segment.born_binding.is_none() {
        return false;
    }
    let binding = segment.born_binding.as_ref().unwrap();
    (binding.qubit_count as usize) <= BORN_ZK_MAX_QUBITS
        && build_distribution_air(segment).is_some()
}

/// Generates a Born-rule Plonky3 STARK transcript bound to `probability_digest`.
pub fn generate_born_stark_proof(
    context: &BornStarkContext<'_>,
    segment: &DistributionSegment,
) -> Result<Vec<u8>, String> {
    if context.sub_task_id.is_empty() || context.probability_digest.is_empty() {
        return Err("sub_task_id and probability_digest are required".to_string());
    }
    if context.probability_digest != segment.probability_digest {
        return Err("probability_digest mismatch".to_string());
    }

    let air = build_distribution_air(segment)
        .ok_or_else(|| "segment does not support Born zk (qubit width or shape)".to_string())?;

    let matrix = build_distribution_matrix(&air, segment)
        .ok_or_else(|| "Born constraints not satisfied on trace row".to_string())?;

    // Cross-check against host Born oracle.
    let binding = segment.born_binding.as_ref().unwrap();
    let measures: Vec<BornMeasureSpec> = binding
        .measures
        .iter()
        .map(|(q, c)| BornMeasureSpec {
            qubit: *q,
            cbit: *c,
        })
        .collect();
    let oracle = born_probabilities_from_statevector(
        &binding.terminal_statevector,
        binding.qubit_count as usize,
        &measures,
        binding.classical_bit_count as usize,
    )
    .ok_or_else(|| "invalid born binding".to_string())?;
    for (key, claimed) in &segment.probabilities {
        let actual = oracle.get(key).copied().unwrap_or(0.0);
        if (claimed - actual).abs() > 1e-4 {
            return Err(format!("oracle mismatch for outcome {key}"));
        }
    }

    let matrix = pad_air_matrix_for_uni_stark(matrix);
    let config = devnet_circle_config();
    let proof = prove(&config, &air, matrix, &[]);
    let plonky3_bytes =
        postcard::to_allocvec(&proof).map_err(|e| format!("postcard encode failed: {e}"))?;

    Ok(encode_born_stark(context, &plonky3_bytes))
}

/// Verifies a Born-rule Plonky3 STARK transcript against a distribution segment.
pub fn verify_born_stark_proof(
    context: &BornStarkContext<'_>,
    segment: &DistributionSegment,
    proof: &[u8],
) -> bool {
    if context.sub_task_id.is_empty() || context.probability_digest.is_empty() {
        eprintln!("[DistributionAir] Failed: context fields empty");
        return false;
    }
    if context.probability_digest != segment.probability_digest {
        eprintln!("[DistributionAir] Failed: probability_digest mismatch");
        return false;
    }

    let air = match build_distribution_air(segment) {
        Some(air) => air,
        None => {
            eprintln!("[DistributionAir] Failed: cannot build AIR from segment");
            return false;
        }
    };

    let plonky3_bytes = match decode_born_stark_owned(proof, context) {
        Some(bytes) => bytes,
        None => {
            eprintln!("[DistributionAir] Failed: malformed Born STARK transcript");
            return false;
        }
    };

    let p3_proof: p3_uni_stark::Proof<WqcStarkConfig> = match postcard::from_bytes(&plonky3_bytes) {
        Ok(proof) => proof,
        Err(e) => {
            eprintln!("[DistributionAir] Failed: postcard decode: {e}");
            return false;
        }
    };

    let config = devnet_circle_config();
    match verify(&config, &air, &p3_proof, &[]) {
        Ok(()) => {
            eprintln!("[DistributionAir] Verification success (Born zk, dim={})", air.dim);
            true
        }
        Err(e) => {
            eprintln!("[DistributionAir] Failed: Plonky3 verify error: {e:?}");
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::distribution::{calculate_probability_digest, BornBinding};

    fn bell_segment() -> DistributionSegment {
        let inv_sqrt2 = 1.0f64 / 2.0f64.sqrt();
        let sv = vec![
            (inv_sqrt2, 0.0),
            (0.0, 0.0),
            (0.0, 0.0),
            (inv_sqrt2, 0.0),
        ];
        let probs = vec![("00".into(), 0.5), ("11".into(), 0.5)];
        let binding = BornBinding::from_specs(2, 2, &[(0, 0), (1, 1)], sv).expect("bind");
        DistributionSegment {
            sample_seed: 42,
            shots: 128,
            measurement_spec_hash: "spec".into(),
            probability_digest: calculate_probability_digest(&probs),
            probabilities: probs,
            born_binding: Some(binding),
        }
    }

    #[test]
    fn bell_born_stark_roundtrip() {
        let segment = bell_segment();
        let ctx = BornStarkContext {
            sub_task_id: "sub-born",
            probability_digest: &segment.probability_digest,
        };
        let proof = generate_born_stark_proof(&ctx, &segment).expect("prove");
        assert!(verify_born_stark_proof(&ctx, &segment, &proof));
    }

    #[test]
    fn bell_born_stark_rejects_tampered_digest() {
        let segment = bell_segment();
        let ctx = BornStarkContext {
            sub_task_id: "sub-born",
            probability_digest: &segment.probability_digest,
        };
        let proof = generate_born_stark_proof(&ctx, &segment).expect("prove");
        let bad = BornStarkContext {
            sub_task_id: "sub-born",
            probability_digest: "deadbeef",
        };
        assert!(!verify_born_stark_proof(&bad, &segment, &proof));
    }
}

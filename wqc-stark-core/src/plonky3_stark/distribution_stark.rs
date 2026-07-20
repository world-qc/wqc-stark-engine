//! C2b Born-rule Plonky3 uni-STARK prove / verify (streaming DistributionAir).

pub use super::distribution_air::{DistributionAir, BORN_ZK_MAX_OUTCOMES, BORN_ZK_MAX_QUBITS};

use p3_uni_stark::{prove, verify};

use crate::air::distribution::{born_probabilities_from_statevector, BornMeasureSpec};
use crate::distribution::DistributionSegment;

use super::config::{devnet_circle_config, WqcStarkConfig};
use super::streaming_distribution::{build_streaming_distribution_matrix, streaming_zk_shape_ok};
use super::transcript_born::{decode_born_stark_owned, encode_born_stark};

/// Public binding for a Born-rule distribution STARK.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BornStarkContext<'a> {
    pub sub_task_id: &'a str,
    pub probability_digest: &'a str,
    pub terminal_statevector_digest: &'a str,
}

/// Maps each computational basis to an outcome index in `outcome_keys` order.
pub fn outcome_index_of_basis(
    binding: &crate::distribution::BornBinding,
    outcome_keys: &[String],
    basis: usize,
) -> Option<usize> {
    let measures: Vec<BornMeasureSpec> = binding
        .measures
        .iter()
        .map(|(q, c)| BornMeasureSpec {
            qubit: *q,
            cbit: *c,
        })
        .collect();
    let mut bits = vec![0u8; binding.classical_bit_count as usize];
    for spec in &measures {
        let bit = (basis >> spec.qubit) & 1;
        bits[spec.cbit as usize] = bit as u8;
    }
    let outcome = crate::air::distribution::outcome_key_from_classical(&bits);
    outcome_keys.iter().position(|k| k == &outcome)
}

/// Outcome keys for streaming AIR: segment probs plus any basis-implied keys (p=0 fillers).
fn streaming_outcome_keys(segment: &DistributionSegment) -> Option<Vec<String>> {
    use std::collections::BTreeSet;
    let binding = segment.born_binding.as_ref()?;
    let mut keys: BTreeSet<String> = segment
        .probabilities
        .iter()
        .map(|(k, _)| k.clone())
        .collect();
    let dim = 1usize << binding.qubit_count as usize;
    let measures: Vec<BornMeasureSpec> = binding
        .measures
        .iter()
        .map(|(q, c)| BornMeasureSpec {
            qubit: *q,
            cbit: *c,
        })
        .collect();
    for basis in 0..dim {
        let mut bits = vec![0u8; binding.classical_bit_count as usize];
        for spec in &measures {
            let bit = (basis >> spec.qubit) & 1;
            bits[spec.cbit as usize] = bit as u8;
        }
        keys.insert(crate::air::distribution::outcome_key_from_classical(&bits));
    }
    if keys.len() > BORN_ZK_MAX_OUTCOMES {
        return None;
    }
    Some(keys.into_iter().collect())
}

fn build_distribution_air(segment: &DistributionSegment) -> Option<DistributionAir> {
    let binding = segment.born_binding.as_ref()?;
    let qubit_count = binding.qubit_count as usize;
    let dim = 1usize << qubit_count;
    let outcome_keys = streaming_outcome_keys(segment)?;
    let num_outcomes = outcome_keys.len();
    if !streaming_zk_shape_ok(qubit_count, num_outcomes, dim) {
        return None;
    }
    if binding.terminal_statevector.len() != dim {
        return None;
    }
    for basis in 0..dim {
        outcome_index_of_basis(binding, &outcome_keys, basis)?;
    }
    Some(DistributionAir { dim, num_outcomes })
}

fn build_distribution_matrix(
    air: &DistributionAir,
    segment: &DistributionSegment,
) -> Option<p3_matrix::dense::RowMajorMatrix<p3_mersenne_31::Mersenne31>> {
    let binding = segment.born_binding.as_ref()?;
    let outcome_keys = streaming_outcome_keys(segment)?;
    if outcome_keys.len() != air.num_outcomes {
        return None;
    }
    build_streaming_distribution_matrix(air, &binding.terminal_statevector, |basis| {
        outcome_index_of_basis(binding, &outcome_keys, basis)
    })
}

/// Returns true when a segment can be zk-proved with streaming `DistributionAir`.
pub fn segment_supports_born_zk(segment: &DistributionSegment) -> bool {
    build_distribution_air(segment).is_some()
}

/// Born zk segment that also fits R3 leaf PCS (K ≤ 21, W ≤ 68 for in-circuit Keccak).
pub fn segment_supports_born_recursion_zk(segment: &DistributionSegment) -> bool {
    let air = match build_distribution_air(segment) {
        Some(a) => a,
        None => return false,
    };
    let binding = match segment.born_binding.as_ref() {
        Some(b) => b,
        None => return false,
    };
    super::streaming_distribution::streaming_recursion_zk_shape_ok(
        binding.qubit_count as usize,
        air.num_outcomes,
        air.dim,
    )
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
    if let Some(binding) = &segment.born_binding {
        if !binding.terminal_statevector_digest.is_empty()
            && context.terminal_statevector_digest != binding.terminal_statevector_digest
        {
            return Err("terminal_statevector_digest mismatch".to_string());
        }
    }

    let air = build_distribution_air(segment)
        .ok_or_else(|| "segment does not support Born zk (qubit width or shape)".to_string())?;

    let matrix = build_distribution_matrix(&air, segment)
        .ok_or_else(|| "Born constraints not satisfied on streaming trace".to_string())?;

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
    if let Some(binding) = &segment.born_binding {
        if !binding.terminal_statevector_digest.is_empty() {
            if context.terminal_statevector_digest != binding.terminal_statevector_digest {
                eprintln!("[DistributionAir] Failed: terminal_statevector_digest mismatch");
                return false;
            }
            let recomputed = crate::distribution::calculate_terminal_statevector_digest(
                &binding.terminal_statevector,
            );
            if recomputed != binding.terminal_statevector_digest {
                eprintln!("[DistributionAir] Failed: statevector digest recomputation mismatch");
                return false;
            }
        }
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
            eprintln!(
                "[DistributionAir] Verification success (Born zk streaming, dim={}, outcomes={})",
                air.dim, air.num_outcomes
            );
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
        let sv = vec![(inv_sqrt2, 0.0), (0.0, 0.0), (0.0, 0.0), (inv_sqrt2, 0.0)];
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

    /// Uniform |+>^n measured in Z on qubit 0 only → p0=p1=0.5 (classical bitstring length 1).
    fn wide_plus_segment(qubit_count: usize) -> DistributionSegment {
        let dim = 1usize << qubit_count;
        let amp = 1.0 / (dim as f64).sqrt();
        let sv = vec![(amp, 0.0); dim];
        let probs = vec![("0".into(), 0.5), ("1".into(), 0.5)];
        let binding = BornBinding::from_specs(qubit_count as u32, 1, &[(0, 0)], sv).expect("bind");
        DistributionSegment {
            sample_seed: 7,
            shots: 64,
            measurement_spec_hash: "spec".into(),
            probability_digest: calculate_probability_digest(&probs),
            probabilities: probs,
            born_binding: Some(binding),
        }
    }

    #[test]
    fn bell_born_stark_roundtrip() {
        let segment = bell_segment();
        let sv_digest = segment
            .born_binding
            .as_ref()
            .map(|b| b.terminal_statevector_digest.as_str())
            .unwrap_or("");
        let ctx = BornStarkContext {
            sub_task_id: "sub-born",
            probability_digest: &segment.probability_digest,
            terminal_statevector_digest: sv_digest,
        };
        let proof = generate_born_stark_proof(&ctx, &segment).expect("prove");
        assert!(verify_born_stark_proof(&ctx, &segment, &proof));
    }

    #[test]
    fn bell_born_stark_rejects_tampered_digest() {
        let segment = bell_segment();
        let sv_digest = segment
            .born_binding
            .as_ref()
            .map(|b| b.terminal_statevector_digest.as_str())
            .unwrap_or("");
        let ctx = BornStarkContext {
            sub_task_id: "sub-born",
            probability_digest: &segment.probability_digest,
            terminal_statevector_digest: sv_digest,
        };
        let proof = generate_born_stark_proof(&ctx, &segment).expect("prove");
        let bad = BornStarkContext {
            sub_task_id: "sub-born",
            probability_digest: "deadbeef",
            terminal_statevector_digest: sv_digest,
        };
        assert!(!verify_born_stark_proof(&bad, &segment, &proof));
    }

    #[test]
    fn streaming_born_zk_supports_8_qubits() {
        let segment = wide_plus_segment(8);
        assert!(segment_supports_born_zk(&segment));
        let sv_digest = segment
            .born_binding
            .as_ref()
            .map(|b| b.terminal_statevector_digest.as_str())
            .unwrap_or("");
        let ctx = BornStarkContext {
            sub_task_id: "sub-born-8q",
            probability_digest: &segment.probability_digest,
            terminal_statevector_digest: sv_digest,
        };
        let proof = generate_born_stark_proof(&ctx, &segment).expect("prove 8q");
        assert!(verify_born_stark_proof(&ctx, &segment, &proof));
    }
}

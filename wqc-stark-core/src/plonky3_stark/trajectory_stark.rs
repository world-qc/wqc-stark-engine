//! C2c trajectory marginal Plonky3 uni-STARK prove / verify (+ per-shot sampling).

pub use super::distribution_air::DistributionAir;
pub use super::transcript_trajectory_stark::TrajectoryMarginalStarkContext;
pub use crate::air::trajectory::TRAJ_MARGINAL_ZK_MAX_QUBITS;

use p3_uni_stark::{prove, verify};

use crate::air::shot_sampling::{collect_shot_sampling_events, segment_supports_shot_sampling_zk};
use crate::trajectory::{TrajectoryMarginalWitness, TrajectorySegment};

use super::config::{circle_config_for_security_level, WqcStarkConfig};
use super::shot_sampling_stark::{
    append_shot_sampling_to_bundle, generate_shot_sampling_stark, split_shot_sampling_from_bundle,
    verify_shot_sampling_stark,
};
use super::streaming_distribution::{build_streaming_distribution_matrix, streaming_zk_shape_ok};
use super::transcript_trajectory_stark::{
    decode_trajectory_marginal_stark_owned, encode_trajectory_marginal_stark,
    TrajectoryShotSamplingStarkContext,
};

fn build_marginal_air(
    witness: &TrajectoryMarginalWitness,
    qubit_count: usize,
) -> Option<DistributionAir> {
    let dim = 1usize << qubit_count;
    if !streaming_zk_shape_ok(qubit_count, 2, dim) {
        return None;
    }
    if witness.pre_measure_statevector.len() != dim {
        return None;
    }
    if witness.qubit as usize >= qubit_count {
        return None;
    }
    Some(DistributionAir {
        dim,
        num_outcomes: 2,
    })
}

fn build_marginal_matrix(
    air: &DistributionAir,
    witness: &TrajectoryMarginalWitness,
) -> Option<p3_matrix::dense::RowMajorMatrix<p3_mersenne_31::Mersenne31>> {
    let measured = witness.qubit as usize;
    build_streaming_distribution_matrix(air, &witness.pre_measure_statevector, |basis| {
        Some((basis >> measured) & 1)
    })
}

/// Returns true when a trajectory segment can be zk-proved with marginal `DistributionAir`s
/// and per-shot Bernoulli sampling.
pub fn segment_supports_trajectory_zk(segment: &TrajectorySegment) -> bool {
    if segment.marginal_witnesses.is_empty() {
        return false;
    }
    let qubit_count = segment.qubit_count as usize;
    if qubit_count == 0 || qubit_count > TRAJ_MARGINAL_ZK_MAX_QUBITS {
        return false;
    }
    if !segment
        .marginal_witnesses
        .iter()
        .all(|w| build_marginal_air(w, qubit_count).is_some())
    {
        return false;
    }
    segment_supports_shot_sampling_zk(segment)
}

fn prove_one_marginal(
    context: &TrajectoryMarginalStarkContext<'_>,
    witness: &TrajectoryMarginalWitness,
    qubit_count: usize,
    security_level: &str,
) -> Result<Vec<u8>, String> {
    if context.witness_digest != witness.pre_measure_statevector_digest {
        return Err("witness_digest mismatch".to_string());
    }

    let air = build_marginal_air(witness, qubit_count)
        .ok_or_else(|| "witness does not support trajectory marginal zk".to_string())?;
    let matrix = build_marginal_matrix(&air, witness)
        .ok_or_else(|| "marginal constraints not satisfied on streaming trace".to_string())?;

    let config = circle_config_for_security_level(security_level, 1);
    let proof = prove(&config, &air, matrix, &[]);
    let plonky3_bytes =
        postcard::to_allocvec(&proof).map_err(|e| format!("postcard encode failed: {e}"))?;
    Ok(encode_trajectory_marginal_stark(context, &plonky3_bytes))
}

/// Generates one Plonky3 STARK per unique marginal witness, plus a shot-sampling STARK.
pub fn generate_trajectory_stark_bundle(
    sub_task_id: &str,
    segment: &TrajectorySegment,
    security_level: &str,
) -> Result<Vec<u8>, String> {
    if sub_task_id.is_empty() || segment.trajectory_digest.is_empty() {
        return Err("sub_task_id and trajectory_digest are required".to_string());
    }
    if !segment_supports_trajectory_zk(segment) {
        return Err("segment does not support trajectory marginal zk".to_string());
    }

    let qubit_count = segment.qubit_count as usize;
    let mut bundle = Vec::new();
    bundle.extend_from_slice(&(segment.marginal_witnesses.len() as u32).to_le_bytes());

    for witness in &segment.marginal_witnesses {
        let link = if !segment.unitary_link_digest.is_empty()
            && witness.pre_measure_statevector_digest == segment.unitary_link_digest
        {
            segment.unitary_link_digest.as_str()
        } else {
            ""
        };
        let ctx = TrajectoryMarginalStarkContext {
            sub_task_id,
            trajectory_digest: &segment.trajectory_digest,
            witness_digest: &witness.pre_measure_statevector_digest,
            unitary_link_digest: link,
        };
        let inner = prove_one_marginal(&ctx, witness, qubit_count, security_level)?;
        bundle.extend_from_slice(&(inner.len() as u32).to_le_bytes());
        bundle.extend_from_slice(&inner);
    }

    let events = collect_shot_sampling_events(segment)
        .ok_or_else(|| "failed to collect shot sampling events".to_string())?;
    let shot_ctx = TrajectoryShotSamplingStarkContext {
        sub_task_id,
        trajectory_digest: &segment.trajectory_digest,
        sample_seed: segment.sample_seed,
        shots: segment.shots,
        event_count: events.len() as u32,
    };
    let shot_inner = generate_shot_sampling_stark(&shot_ctx, segment, security_level)?;
    Ok(append_shot_sampling_to_bundle(bundle, &shot_inner))
}

fn verify_one_marginal(
    context: &TrajectoryMarginalStarkContext<'_>,
    witness: &TrajectoryMarginalWitness,
    qubit_count: usize,
    proof: &[u8],
    security_level: &str,
) -> bool {
    let air = match build_marginal_air(witness, qubit_count) {
        Some(air) => air,
        None => {
            eprintln!("[TrajectoryAir] Failed: cannot build AIR from witness");
            return false;
        }
    };

    let plonky3_bytes = match decode_trajectory_marginal_stark_owned(proof, context) {
        Some(bytes) => bytes,
        None => {
            eprintln!("[TrajectoryAir] Failed: malformed marginal STARK transcript");
            return false;
        }
    };

    let p3_proof: p3_uni_stark::Proof<WqcStarkConfig> = match postcard::from_bytes(&plonky3_bytes) {
        Ok(proof) => proof,
        Err(e) => {
            eprintln!("[TrajectoryAir] Failed: postcard decode: {e}");
            return false;
        }
    };

    let config = circle_config_for_security_level(security_level, 1);
    match verify(&config, &air, &p3_proof, &[]) {
        Ok(()) => true,
        Err(e) => {
            eprintln!("[TrajectoryAir] Failed: Plonky3 verify error: {e:?}");
            false
        }
    }
}

/// Verifies a trajectory marginal + shot-sampling STARK bundle against a trajectory segment.
pub fn verify_trajectory_stark_bundle(
    sub_task_id: &str,
    segment: &TrajectorySegment,
    bundle: &[u8],
    security_level: &str,
) -> bool {
    if sub_task_id.is_empty() || segment.trajectory_digest.is_empty() {
        eprintln!("[TrajectoryAir] Failed: context fields empty");
        return false;
    }
    if !segment_supports_trajectory_zk(segment) {
        eprintln!("[TrajectoryAir] Failed: segment does not support trajectory zk");
        return false;
    }

    let Some((marginal_bundle, shot_inner)) = split_shot_sampling_from_bundle(bundle) else {
        eprintln!("[TrajectoryAir] Failed: missing shot sampling section in bundle");
        return false;
    };

    let qubit_count = segment.qubit_count as usize;
    let (witness_count, mut cursor) = match read_u32_le(marginal_bundle, 0) {
        Some(v) => v,
        None => {
            eprintln!("[TrajectoryAir] Failed: malformed bundle header");
            return false;
        }
    };
    if witness_count as usize != segment.marginal_witnesses.len() {
        eprintln!("[TrajectoryAir] Failed: witness count mismatch");
        return false;
    }

    for witness in &segment.marginal_witnesses {
        let (inner_len, next) = match read_u32_le(marginal_bundle, cursor) {
            Some(v) => v,
            None => {
                eprintln!("[TrajectoryAir] Failed: malformed inner length");
                return false;
            }
        };
        cursor = next;
        let end = cursor + inner_len as usize;
        let inner = match marginal_bundle.get(cursor..end) {
            Some(slice) => slice,
            None => {
                eprintln!("[TrajectoryAir] Failed: truncated inner proof");
                return false;
            }
        };
        cursor = end;

        let link = if !segment.unitary_link_digest.is_empty()
            && witness.pre_measure_statevector_digest == segment.unitary_link_digest
        {
            segment.unitary_link_digest.as_str()
        } else {
            ""
        };
        let ctx = TrajectoryMarginalStarkContext {
            sub_task_id,
            trajectory_digest: &segment.trajectory_digest,
            witness_digest: &witness.pre_measure_statevector_digest,
            unitary_link_digest: link,
        };
        if !verify_one_marginal(&ctx, witness, qubit_count, inner, security_level) {
            return false;
        }
    }

    if cursor != marginal_bundle.len() {
        eprintln!("[TrajectoryAir] Failed: trailing marginal bundle bytes");
        return false;
    }

    let Some(events) = collect_shot_sampling_events(segment) else {
        eprintln!("[TrajectoryAir] Failed: collect shot sampling events");
        return false;
    };
    let shot_ctx = TrajectoryShotSamplingStarkContext {
        sub_task_id,
        trajectory_digest: &segment.trajectory_digest,
        sample_seed: segment.sample_seed,
        shots: segment.shots,
        event_count: events.len() as u32,
    };
    if !verify_shot_sampling_stark(&shot_ctx, segment, shot_inner, security_level) {
        return false;
    }

    eprintln!(
        "[TrajectoryAir] Verification success (marginal + shot sampling zk, witnesses={}, events={})",
        witness_count,
        events.len()
    );
    true
}

fn read_u32_le(buf: &[u8], offset: usize) -> Option<(u32, usize)> {
    let bytes = buf.get(offset..offset + 4)?;
    let mut raw = [0u8; 4];
    raw.copy_from_slice(bytes);
    Some((u32::from_le_bytes(raw), offset + 4))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::trajectory::{TrajectoryMeasureEvent, TrajectoryShotTrace};
    use rand::rngs::StdRng;
    use rand::{Rng, SeedableRng};

    fn if_demo_segment() -> TrajectorySegment {
        let inv_sqrt2 = 1.0f64 / 2.0f64.sqrt();
        let pre_first = vec![(inv_sqrt2, 0.0), (0.0, 0.0), (inv_sqrt2, 0.0), (0.0, 0.0)];
        let pre_second_branch0 = vec![(1.0, 0.0), (0.0, 0.0), (0.0, 0.0), (0.0, 0.0)];
        let pre_second_branch1 = vec![(0.0, 0.0), (0.0, 0.0), (1.0, 0.0), (0.0, 0.0)];
        let d0 = crate::distribution::calculate_terminal_statevector_digest(&pre_first);
        let d1 = crate::distribution::calculate_terminal_statevector_digest(&pre_second_branch0);
        let d2 = crate::distribution::calculate_terminal_statevector_digest(&pre_second_branch1);

        let mut rng = StdRng::seed_from_u64(7);
        let u0: f64 = rng.gen();
        let o0 = if u0 < 0.5 { 0u8 } else { 1 };
        let (p0_1, p1_1, digest_1): (f64, f64, String) = if o0 == 0 {
            (1.0, 0.0, d1.clone())
        } else {
            (0.0, 1.0, d2.clone())
        };
        let u1: f64 = rng.gen();
        let denom = (p0_1 + p1_1).max(1e-30);
        let o1 = if u1 < p0_1 / denom { 0u8 } else { 1 };

        let witnesses = vec![
            TrajectoryMarginalWitness {
                qubit: 0,
                reference_p0: 0.5,
                reference_p1: 0.5,
                pre_measure_statevector: pre_first.clone(),
                pre_measure_statevector_digest: d0.clone(),
            },
            TrajectoryMarginalWitness {
                qubit: 1,
                reference_p0: 1.0,
                reference_p1: 0.0,
                pre_measure_statevector: pre_second_branch0.clone(),
                pre_measure_statevector_digest: d1.clone(),
            },
            TrajectoryMarginalWitness {
                qubit: 1,
                reference_p0: 0.0,
                reference_p1: 1.0,
                pre_measure_statevector: pre_second_branch1.clone(),
                pre_measure_statevector_digest: d2.clone(),
            },
        ];

        let traces = vec![TrajectoryShotTrace {
            shot_index: 0,
            shot_seed: 7,
            final_outcome: format!("{o0}{o1}"),
            classical_bits: vec![o0, o1],
            measures: vec![
                TrajectoryMeasureEvent {
                    gate_index: 1,
                    qubit: 0,
                    cbit: 0,
                    p0: 0.5,
                    p1: 0.5,
                    outcome: o0,
                    pre_measure_statevector_digest: d0.clone(),
                },
                TrajectoryMeasureEvent {
                    gate_index: 3,
                    qubit: 1,
                    cbit: 1,
                    p0: p0_1,
                    p1: p1_1,
                    outcome: o1,
                    pre_measure_statevector_digest: digest_1,
                },
            ],
        }];

        TrajectorySegment {
            sample_seed: 7,
            shots: 1,
            measurement_spec_hash: "spec".into(),
            trajectory_digest: crate::trajectory::calculate_trajectory_digest(&traces),
            qubit_count: 2,
            unitary_link_digest: d0,
            traces,
            marginal_witnesses: witnesses,
        }
    }

    #[test]
    fn if_demo_trajectory_marginal_stark_roundtrip() {
        let segment = if_demo_segment();
        let bundle = generate_trajectory_stark_bundle("sub-traj", &segment, "").expect("prove");
        assert!(split_shot_sampling_from_bundle(&bundle).is_some());
        assert!(verify_trajectory_stark_bundle(
            "sub-traj", &segment, &bundle, ""
        ));
    }

    #[test]
    fn streaming_marginal_zk_supports_8_qubits() {
        let qubit_count = 8usize;
        let dim = 1usize << qubit_count;
        let amp = 1.0 / (dim as f64).sqrt();
        let sv = vec![(amp, 0.0); dim];
        let digest = crate::distribution::calculate_terminal_statevector_digest(&sv);
        let witness = TrajectoryMarginalWitness {
            qubit: 0,
            reference_p0: 0.5,
            reference_p1: 0.5,
            pre_measure_statevector: sv,
            pre_measure_statevector_digest: digest.clone(),
        };
        let mut rng = StdRng::seed_from_u64(11);
        let u: f64 = rng.gen();
        let o = if u < 0.5 { 0u8 } else { 1 };
        let traces = vec![TrajectoryShotTrace {
            shot_index: 0,
            shot_seed: 11,
            final_outcome: format!("{o}"),
            classical_bits: vec![o],
            measures: vec![TrajectoryMeasureEvent {
                gate_index: 0,
                qubit: 0,
                cbit: 0,
                p0: 0.5,
                p1: 0.5,
                outcome: o,
                pre_measure_statevector_digest: digest.clone(),
            }],
        }];
        let segment = TrajectorySegment {
            sample_seed: 11,
            shots: 1,
            measurement_spec_hash: "spec".into(),
            trajectory_digest: crate::trajectory::calculate_trajectory_digest(&traces),
            qubit_count: qubit_count as u32,
            unitary_link_digest: digest,
            traces,
            marginal_witnesses: vec![witness],
        };
        assert!(segment_supports_trajectory_zk(&segment));
        let bundle = generate_trajectory_stark_bundle("sub-8q", &segment, "").expect("prove 8q");
        assert!(verify_trajectory_stark_bundle(
            "sub-8q", &segment, &bundle, ""
        ));
    }
}

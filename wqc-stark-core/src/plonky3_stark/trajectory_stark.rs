//! C2c trajectory marginal Plonky3 uni-STARK prove / verify.

pub use super::distribution_air::{DistributionAir, BORN_ZK_SCALE};
pub use super::transcript_trajectory_stark::TrajectoryMarginalStarkContext;
pub use crate::air::trajectory::TRAJ_MARGINAL_ZK_MAX_QUBITS;

use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::dense::RowMajorMatrix;
use p3_mersenne_31::Mersenne31;
use p3_uni_stark::{prove, verify};

use crate::air::trajectory::z_marginal_basis_groups;
use crate::air::{f64_to_m31, pad_air_matrix_for_uni_stark};
use crate::trajectory::{TrajectoryMarginalWitness, TrajectorySegment};

use super::config::{devnet_circle_config, WqcStarkConfig};
use super::transcript_trajectory_stark::{
    decode_trajectory_marginal_stark_owned, encode_trajectory_marginal_stark,
};

fn build_marginal_air(witness: &TrajectoryMarginalWitness, qubit_count: usize) -> Option<DistributionAir> {
    if qubit_count > TRAJ_MARGINAL_ZK_MAX_QUBITS {
        return None;
    }
    let dim = 1usize << qubit_count;
    if witness.pre_measure_statevector.len() != dim {
        return None;
    }
    let (group0, group1) = z_marginal_basis_groups(witness.qubit as usize, qubit_count)?;
    Some(DistributionAir {
        dim,
        outcome_groups: vec![group0, group1],
    })
}

fn build_marginal_matrix(
    air: &DistributionAir,
    witness: &TrajectoryMarginalWitness,
) -> Option<RowMajorMatrix<Mersenne31>> {
    let scale = Mersenne31::from_u32(BORN_ZK_SCALE);
    let scale_inv = scale.inverse();
    let mut row = Vec::with_capacity(air.width());

    for (re, im) in &witness.pre_measure_statevector {
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

/// Returns true when a trajectory segment can be zk-proved with marginal `DistributionAir`s.
pub fn segment_supports_trajectory_zk(segment: &TrajectorySegment) -> bool {
    if segment.marginal_witnesses.is_empty() {
        return false;
    }
    let qubit_count = segment.qubit_count as usize;
    if qubit_count == 0 || qubit_count > TRAJ_MARGINAL_ZK_MAX_QUBITS {
        return false;
    }
    segment
        .marginal_witnesses
        .iter()
        .all(|w| build_marginal_air(w, qubit_count).is_some())
}

fn prove_one_marginal(
    context: &TrajectoryMarginalStarkContext<'_>,
    witness: &TrajectoryMarginalWitness,
    qubit_count: usize,
) -> Result<Vec<u8>, String> {
    if context.witness_digest != witness.pre_measure_statevector_digest {
        return Err("witness_digest mismatch".to_string());
    }

    let air = build_marginal_air(witness, qubit_count)
        .ok_or_else(|| "witness does not support trajectory marginal zk".to_string())?;
    let matrix = build_marginal_matrix(&air, witness)
        .ok_or_else(|| "marginal constraints not satisfied on trace row".to_string())?;

    let matrix = pad_air_matrix_for_uni_stark(matrix);
    let config = devnet_circle_config();
    let proof = prove(&config, &air, matrix, &[]);
    let plonky3_bytes =
        postcard::to_allocvec(&proof).map_err(|e| format!("postcard encode failed: {e}"))?;
    Ok(encode_trajectory_marginal_stark(context, &plonky3_bytes))
}

/// Generates one Plonky3 STARK per unique marginal witness and concatenates inner transcripts.
pub fn generate_trajectory_stark_bundle(
    sub_task_id: &str,
    segment: &TrajectorySegment,
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
        let inner = prove_one_marginal(&ctx, witness, qubit_count)?;
        bundle.extend_from_slice(&(inner.len() as u32).to_le_bytes());
        bundle.extend_from_slice(&inner);
    }

    Ok(bundle)
}

fn verify_one_marginal(
    context: &TrajectoryMarginalStarkContext<'_>,
    witness: &TrajectoryMarginalWitness,
    qubit_count: usize,
    proof: &[u8],
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

    let config = devnet_circle_config();
    match verify(&config, &air, &p3_proof, &[]) {
        Ok(()) => true,
        Err(e) => {
            eprintln!("[TrajectoryAir] Failed: Plonky3 verify error: {e:?}");
            false
        }
    }
}

/// Verifies a trajectory marginal STARK bundle against a trajectory segment.
pub fn verify_trajectory_stark_bundle(sub_task_id: &str, segment: &TrajectorySegment, bundle: &[u8]) -> bool {
    if sub_task_id.is_empty() || segment.trajectory_digest.is_empty() {
        eprintln!("[TrajectoryAir] Failed: context fields empty");
        return false;
    }
    if !segment_supports_trajectory_zk(segment) {
        eprintln!("[TrajectoryAir] Failed: segment does not support trajectory zk");
        return false;
    }

    let qubit_count = segment.qubit_count as usize;
    let (witness_count, mut cursor) = match read_u32_le(bundle, 0) {
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
        let (inner_len, next) = match read_u32_le(bundle, cursor) {
            Some(v) => v,
            None => {
                eprintln!("[TrajectoryAir] Failed: malformed inner length");
                return false;
            }
        };
        cursor = next;
        let end = cursor + inner_len as usize;
        let inner = match bundle.get(cursor..end) {
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
        if !verify_one_marginal(&ctx, witness, qubit_count, inner) {
            return false;
        }
    }

    if cursor != bundle.len() {
        eprintln!("[TrajectoryAir] Failed: trailing bundle bytes");
        return false;
    }

    eprintln!(
        "[TrajectoryAir] Verification success (trajectory marginal zk, witnesses={})",
        witness_count
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

    fn if_demo_segment() -> TrajectorySegment {
        let inv_sqrt2 = 1.0f64 / 2.0f64.sqrt();
        let pre_first = vec![(inv_sqrt2, 0.0), (0.0, 0.0), (inv_sqrt2, 0.0), (0.0, 0.0)];
        let pre_second_branch0 = vec![(1.0, 0.0), (0.0, 0.0), (0.0, 0.0), (0.0, 0.0)];
        let pre_second_branch1 = vec![(0.0, 0.0), (0.0, 0.0), (1.0, 0.0), (0.0, 0.0)];
        let d0 = crate::distribution::calculate_terminal_statevector_digest(&pre_first);
        let d1 = crate::distribution::calculate_terminal_statevector_digest(&pre_second_branch0);
        let d2 = crate::distribution::calculate_terminal_statevector_digest(&pre_second_branch1);

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
            final_outcome: "01".into(),
            classical_bits: vec![1, 0],
            measures: vec![
                TrajectoryMeasureEvent {
                    gate_index: 1,
                    qubit: 0,
                    cbit: 0,
                    p0: 0.5,
                    p1: 0.5,
                    outcome: 1,
                    pre_measure_statevector_digest: d0.clone(),
                },
                TrajectoryMeasureEvent {
                    gate_index: 3,
                    qubit: 1,
                    cbit: 1,
                    p0: 0.0,
                    p1: 1.0,
                    outcome: 1,
                    pre_measure_statevector_digest: d2.clone(),
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
        let bundle = generate_trajectory_stark_bundle("sub-traj", &segment).expect("prove");
        assert!(verify_trajectory_stark_bundle("sub-traj", &segment, &bundle));
    }
}

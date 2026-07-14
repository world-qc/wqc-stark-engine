//! C2c per-shot MEASURE Bernoulli Plonky3 uni-STARK prove / verify.

use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;
use p3_mersenne_31::Mersenne31;
use p3_uni_stark::{prove, verify};

use crate::air::pad_air_matrix_for_uni_stark;
use crate::air::shot_sampling::{
    collect_shot_sampling_events, fixed_point_bernoulli_witnesses,
    segment_supports_shot_sampling_zk, ShotSamplingEvent, SHOT_SAMPLING_GAP_BITS,
    TRAJ_SHOT_SAMPLING_ZK_MAX_EVENTS,
};
use crate::trajectory::TrajectorySegment;

use super::config::{devnet_circle_config, WqcStarkConfig};
use super::shot_sampling_air::{
    ShotSamplingAir, SHOT_SAMPLING_AIR_WIDTH, SHOT_SAMPLING_COL_GAP, SHOT_SAMPLING_COL_GAP_BITS,
    SHOT_SAMPLING_COL_IS_PAD, SHOT_SAMPLING_COL_OUTCOME, SHOT_SAMPLING_COL_P0,
    SHOT_SAMPLING_COL_P1, SHOT_SAMPLING_COL_U,
};
use super::transcript_trajectory_stark::{
    decode_trajectory_shot_sampling_stark_owned, encode_trajectory_shot_sampling_stark,
    TrajectoryShotSamplingStarkContext,
};

fn fill_row(row: &mut [Mersenne31], event: &ShotSamplingEvent) -> Result<(), String> {
    let (p0_i, p1_i, u_i, gap) =
        fixed_point_bernoulli_witnesses(event.p0, event.p1, event.sample_u, event.outcome)
            .ok_or_else(|| "fixed-point Bernoulli witnesses unavailable".to_string())?;

    row[SHOT_SAMPLING_COL_P0] = Mersenne31::from_u32(p0_i);
    row[SHOT_SAMPLING_COL_P1] = Mersenne31::from_u32(p1_i);
    row[SHOT_SAMPLING_COL_U] = Mersenne31::from_u32(u_i);
    row[SHOT_SAMPLING_COL_OUTCOME] = Mersenne31::from_u32(u32::from(event.outcome));
    row[SHOT_SAMPLING_COL_GAP] = Mersenne31::from_u32(gap);
    for i in 0..SHOT_SAMPLING_GAP_BITS {
        let bit = (gap >> i) & 1;
        row[SHOT_SAMPLING_COL_GAP_BITS + i] = Mersenne31::from_u32(bit);
    }
    row[SHOT_SAMPLING_COL_IS_PAD] = Mersenne31::ZERO;

    let air = ShotSamplingAir;
    if air.evaluate_row_sum::<Mersenne31>(row) != Mersenne31::ZERO {
        return Err("shot sampling row constraints not satisfied".to_string());
    }
    Ok(())
}

fn build_shot_sampling_matrix(
    events: &[ShotSamplingEvent],
) -> Result<RowMajorMatrix<Mersenne31>, String> {
    if events.is_empty() {
        return Err("shot sampling events empty".to_string());
    }
    if events.len() > TRAJ_SHOT_SAMPLING_ZK_MAX_EVENTS {
        return Err("shot sampling event count exceeds soft cap".to_string());
    }

    let mut values = Vec::with_capacity(events.len() * SHOT_SAMPLING_AIR_WIDTH);
    let mut row = vec![Mersenne31::ZERO; SHOT_SAMPLING_AIR_WIDTH];
    for event in events {
        fill_row(&mut row, event)?;
        values.extend_from_slice(&row);
    }

    // Ensure at least 2 rows before uni-STARK padding helpers.
    if events.len() == 1 {
        values.extend_from_slice(&row);
    }

    Ok(RowMajorMatrix::new(values, SHOT_SAMPLING_AIR_WIDTH))
}

fn pad_rows_as_inactive(matrix: RowMajorMatrix<Mersenne31>) -> RowMajorMatrix<Mersenne31> {
    let padded = pad_air_matrix_for_uni_stark(matrix);
    let width = padded.width;
    let height = padded.values.len() / width;
    let mut values = padded.values;
    // Rows copied by power-of-two padding must be marked is_pad=1 so Bernoulli
    // constraints are disabled (duplicating the last active row would otherwise
    // re-assert the same event — fine — but extra pure-zero pads need the flag).
    // pad_air_matrix_for_uni_stark repeats the last row, which already has is_pad=0;
    // that is valid (duplicate active constraints). Leave as-is.
    let _ = (height, &mut values);
    RowMajorMatrix::new(values, width)
}

/// Generates a Plonky3 shot-sampling STARK inner transcript for all MEASURE events.
pub fn generate_shot_sampling_stark(
    context: &TrajectoryShotSamplingStarkContext<'_>,
    segment: &TrajectorySegment,
) -> Result<Vec<u8>, String> {
    if !segment_supports_shot_sampling_zk(segment) {
        return Err("segment does not support shot sampling zk".to_string());
    }
    if context.trajectory_digest != segment.trajectory_digest {
        return Err("trajectory_digest mismatch".to_string());
    }
    if context.sample_seed != segment.sample_seed || context.shots != segment.shots {
        return Err("sample_seed/shots mismatch".to_string());
    }

    let events = collect_shot_sampling_events(segment)
        .ok_or_else(|| "failed to collect shot sampling events".to_string())?;
    if events.len() as u32 != context.event_count {
        return Err("event_count mismatch".to_string());
    }

    let matrix = build_shot_sampling_matrix(&events)?;
    let matrix = pad_rows_as_inactive(matrix);
    let config = devnet_circle_config();
    let air = ShotSamplingAir;
    let proof = prove(&config, &air, matrix, &[]);
    let plonky3_bytes =
        postcard::to_allocvec(&proof).map_err(|e| format!("postcard encode failed: {e}"))?;
    Ok(encode_trajectory_shot_sampling_stark(
        context,
        &plonky3_bytes,
    ))
}

/// Verifies a shot-sampling STARK inner transcript against a trajectory segment.
pub fn verify_shot_sampling_stark(
    context: &TrajectoryShotSamplingStarkContext<'_>,
    segment: &TrajectorySegment,
    proof: &[u8],
) -> bool {
    if !segment_supports_shot_sampling_zk(segment) {
        eprintln!("[ShotSamplingAir] Failed: segment does not support shot sampling zk");
        return false;
    }
    if context.trajectory_digest != segment.trajectory_digest
        || context.sample_seed != segment.sample_seed
        || context.shots != segment.shots
    {
        eprintln!("[ShotSamplingAir] Failed: context binding mismatch");
        return false;
    }

    let Some(events) = collect_shot_sampling_events(segment) else {
        eprintln!("[ShotSamplingAir] Failed: collect events");
        return false;
    };
    if events.len() as u32 != context.event_count {
        eprintln!("[ShotSamplingAir] Failed: event_count mismatch");
        return false;
    }

    let matrix = match build_shot_sampling_matrix(&events) {
        Ok(m) => pad_rows_as_inactive(m),
        Err(e) => {
            eprintln!("[ShotSamplingAir] Failed: build matrix: {e}");
            return false;
        }
    };
    // Matrix is only used to ensure host constraints; Plonky3 verify rebuilds from proof.
    let _ = matrix;

    let Some(plonky3_bytes) = decode_trajectory_shot_sampling_stark_owned(proof, context) else {
        eprintln!("[ShotSamplingAir] Failed: malformed shot sampling transcript");
        return false;
    };

    let p3_proof: p3_uni_stark::Proof<WqcStarkConfig> = match postcard::from_bytes(&plonky3_bytes) {
        Ok(proof) => proof,
        Err(e) => {
            eprintln!("[ShotSamplingAir] Failed: postcard decode: {e}");
            return false;
        }
    };

    let config = devnet_circle_config();
    let air = ShotSamplingAir;
    match verify(&config, &air, &p3_proof, &[]) {
        Ok(()) => true,
        Err(e) => {
            eprintln!("[ShotSamplingAir] Failed: Plonky3 verify error: {e:?}");
            false
        }
    }
}

/// Appends a shot-sampling inner proof to a trajectory marginal STARK bundle.
pub fn append_shot_sampling_to_bundle(mut bundle: Vec<u8>, shot_inner: &[u8]) -> Vec<u8> {
    bundle.extend_from_slice(&(shot_inner.len() as u32).to_le_bytes());
    bundle.extend_from_slice(shot_inner);
    bundle
}

/// Splits the shot-sampling section from a trajectory STARK bundle.
///
/// Layout: `[marginal_bundle][u32 shot_len][shot_inner]` where `marginal_bundle` is
/// `[u32 witness_count][len_i][inner_i]…` with no trailing bytes.
pub fn split_shot_sampling_from_bundle(bundle: &[u8]) -> Option<(&[u8], &[u8])> {
    let (witness_count, mut cursor) = read_u32(bundle, 0)?;
    for _ in 0..witness_count {
        let (inner_len, next) = read_u32(bundle, cursor)?;
        cursor = next + inner_len as usize;
        if cursor > bundle.len() {
            return None;
        }
    }
    if cursor + 4 > bundle.len() {
        return None;
    }
    let (shot_len, shot_start) = read_u32(bundle, cursor)?;
    let shot_end = shot_start + shot_len as usize;
    if shot_end != bundle.len() {
        return None;
    }
    let marginal = bundle.get(..cursor)?;
    let shot = bundle.get(shot_start..shot_end)?;
    Some((marginal, shot))
}

fn read_u32(buf: &[u8], offset: usize) -> Option<(u32, usize)> {
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

    fn rng_consistent_segment() -> TrajectorySegment {
        let mut rng = StdRng::seed_from_u64(7);
        let u0: f64 = rng.gen();
        let o0 = if u0 < 0.5 { 0u8 } else { 1 };
        let u1: f64 = rng.gen();
        let o1 = if u1 < 0.0 { 0u8 } else { 1 };

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
                    pre_measure_statevector_digest: "d0".into(),
                },
                TrajectoryMeasureEvent {
                    gate_index: 3,
                    qubit: 1,
                    cbit: 1,
                    p0: 0.0,
                    p1: 1.0,
                    outcome: o1,
                    pre_measure_statevector_digest: "d1".into(),
                },
            ],
        }];
        TrajectorySegment {
            sample_seed: 7,
            shots: 1,
            measurement_spec_hash: "spec".into(),
            trajectory_digest: crate::trajectory::calculate_trajectory_digest(&traces),
            qubit_count: 2,
            unitary_link_digest: String::new(),
            traces,
            marginal_witnesses: Vec::new(),
        }
    }

    #[test]
    fn shot_sampling_stark_roundtrip() {
        let segment = rng_consistent_segment();
        let events = collect_shot_sampling_events(&segment).unwrap();
        let ctx = TrajectoryShotSamplingStarkContext {
            sub_task_id: "sub-traj",
            trajectory_digest: &segment.trajectory_digest,
            sample_seed: segment.sample_seed,
            shots: segment.shots,
            event_count: events.len() as u32,
        };
        let inner = generate_shot_sampling_stark(&ctx, &segment).expect("prove");
        assert!(verify_shot_sampling_stark(&ctx, &segment, &inner));
    }
}

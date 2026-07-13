//! C2c: mid-circuit trajectory tail bound to a v1/v2 STARK transcript.
//!
//! Appended after optional distribution / Born tails:
//! `_M31_TRAJ_V1_` or `_M31_TRAJ_V2_` + segment payload (+ optional `_M31_TRAJ_STARK_V1_` zk bundle)

pub const TRAJ_V1_MARKER: &[u8] = b"_M31_TRAJ_V1_";
pub const TRAJ_V2_MARKER: &[u8] = b"_M31_TRAJ_V2_";

type ProofTailSplit<'a> = (&'a [u8], Option<(&'a [u8], &'static [u8])>);

/// One observed MEASURE event during a trajectory shot.
#[derive(Debug, Clone, PartialEq)]
pub struct TrajectoryMeasureEvent {
    pub gate_index: u32,
    pub qubit: u32,
    pub cbit: u32,
    pub p0: f64,
    pub p1: f64,
    pub outcome: u8,
    /// SHA3-256 hex of canonical pre-measure statevector JSON (empty in legacy V1 tails).
    pub pre_measure_statevector_digest: String,
}

/// Unique pre-measure statevector witness for zk marginal binding (deduped by digest + qubit).
#[derive(Debug, Clone, PartialEq)]
pub struct TrajectoryMarginalWitness {
    pub qubit: u32,
    pub reference_p0: f64,
    pub reference_p1: f64,
    pub pre_measure_statevector: Vec<(f64, f64)>,
    pub pre_measure_statevector_digest: String,
}

/// One deterministic trajectory shot.
#[derive(Debug, Clone, PartialEq)]
pub struct TrajectoryShotTrace {
    pub shot_index: u64,
    pub shot_seed: u64,
    pub final_outcome: String,
    pub classical_bits: Vec<u8>,
    pub measures: Vec<TrajectoryMeasureEvent>,
}

/// Mid-circuit trajectory binding carried in the proof transcript tail.
#[derive(Debug, Clone, PartialEq)]
pub struct TrajectorySegment {
    pub sample_seed: u64,
    pub shots: u64,
    /// SHA3-256 hex of canonical measurement spec JSON (C2a-4).
    pub measurement_spec_hash: String,
    /// SHA3-256 hex of canonical trajectory JSON.
    pub trajectory_digest: String,
    pub qubit_count: u32,
    /// Digest of the first MEASURE pre-measure statevector (unitary v2 link); empty when absent.
    pub unitary_link_digest: String,
    pub traces: Vec<TrajectoryShotTrace>,
    /// Deduped marginal witnesses for algebraic / zk binding (empty in legacy V1 tails).
    pub marginal_witnesses: Vec<TrajectoryMarginalWitness>,
}

fn read_cstr(proof: &[u8], offset: usize) -> Option<(String, usize)> {
    let tail = proof.get(offset..)?;
    let end_rel = tail.iter().position(|&b| b == 0)?;
    let end = offset + end_rel;
    let value = std::str::from_utf8(&proof[offset..end]).ok()?;
    Some((value.to_string(), end + 1))
}

fn read_u32_le(proof: &[u8], offset: usize) -> Option<(u32, usize)> {
    let bytes = proof.get(offset..offset + 4)?;
    let mut buf = [0u8; 4];
    buf.copy_from_slice(bytes);
    Some((u32::from_le_bytes(buf), offset + 4))
}

fn read_u64_le(proof: &[u8], offset: usize) -> Option<(u64, usize)> {
    let bytes = proof.get(offset..offset + 8)?;
    let mut buf = [0u8; 8];
    buf.copy_from_slice(bytes);
    Some((u64::from_le_bytes(buf), offset + 8))
}

fn read_f64_le(proof: &[u8], offset: usize) -> Option<(f64, usize)> {
    let bytes = proof.get(offset..offset + 8)?;
    let mut buf = [0u8; 8];
    buf.copy_from_slice(bytes);
    Some((f64::from_le_bytes(buf), offset + 8))
}

fn append_cstr(out: &mut Vec<u8>, value: &str) {
    out.extend_from_slice(value.as_bytes());
    out.push(0);
}

fn format_go_float(val: f64) -> String {
    if val == (val as i64) as f64 {
        format!("{:.1}", val)
    } else {
        format!("{val}")
    }
}

/// Canonical JSON for trajectory digest — must match `wqc-core`.
pub fn format_trajectory_json(traces: &[TrajectoryShotTrace]) -> String {
    let mut shots = String::new();
    for shot in traces {
        if !shots.is_empty() {
            shots.push(',');
        }
        let mut measures = String::new();
        for m in &shot.measures {
            if !measures.is_empty() {
                measures.push(',');
            }
            measures.push_str(&format!(
                r#"{{"cbit":{},"gate_index":{},"outcome":{},"p0":{},"p1":{},"qubit":{}}}"#,
                m.cbit,
                m.gate_index,
                m.outcome,
                format_go_float(m.p0),
                format_go_float(m.p1),
                m.qubit,
            ));
        }
        let classical: Vec<String> = shot.classical_bits.iter().map(|b| b.to_string()).collect();
        shots.push_str(&format!(
            r#"{{"classical_bits":[{}],"final_outcome":"{}","measures":[{}],"shot_index":{},"shot_seed":{}}}"#,
            classical.join(","),
            shot.final_outcome,
            measures,
            shot.shot_index,
            shot.shot_seed,
        ));
    }
    format!(r#"{{"trajectory":{{"shots":[{shots}]}}}}"#)
}

/// SHA3-256 hex digest of the canonical trajectory JSON.
pub fn calculate_trajectory_digest(traces: &[TrajectoryShotTrace]) -> String {
    use sha3::{Digest, Sha3_256};
    hex::encode(Sha3_256::digest(format_trajectory_json(traces).as_bytes()))
}

pub fn encode_trajectory_segment(segment: &TrajectorySegment, marker: &[u8]) -> Vec<u8> {
    if marker == TRAJ_V2_MARKER {
        encode_trajectory_segment_v2(segment)
    } else {
        encode_trajectory_segment_v1(segment)
    }
}

fn encode_trajectory_segment_v1(segment: &TrajectorySegment) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(&segment.sample_seed.to_le_bytes());
    out.extend_from_slice(&segment.shots.to_le_bytes());
    append_cstr(&mut out, &segment.measurement_spec_hash);
    append_cstr(&mut out, &segment.trajectory_digest);
    out.extend_from_slice(&(segment.traces.len() as u32).to_le_bytes());
    for shot in &segment.traces {
        out.extend_from_slice(&shot.shot_index.to_le_bytes());
        out.extend_from_slice(&shot.shot_seed.to_le_bytes());
        append_cstr(&mut out, &shot.final_outcome);
        out.extend_from_slice(&(shot.classical_bits.len() as u32).to_le_bytes());
        out.extend_from_slice(&shot.classical_bits);
        out.extend_from_slice(&(shot.measures.len() as u32).to_le_bytes());
        for m in &shot.measures {
            out.extend_from_slice(&m.gate_index.to_le_bytes());
            out.extend_from_slice(&m.qubit.to_le_bytes());
            out.extend_from_slice(&m.cbit.to_le_bytes());
            out.extend_from_slice(&m.p0.to_le_bytes());
            out.extend_from_slice(&m.p1.to_le_bytes());
            out.push(m.outcome);
        }
    }
    out
}

fn encode_trajectory_segment_v2(segment: &TrajectorySegment) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(&segment.sample_seed.to_le_bytes());
    out.extend_from_slice(&segment.shots.to_le_bytes());
    append_cstr(&mut out, &segment.measurement_spec_hash);
    append_cstr(&mut out, &segment.trajectory_digest);
    out.extend_from_slice(&segment.qubit_count.to_le_bytes());
    append_cstr(&mut out, &segment.unitary_link_digest);
    out.extend_from_slice(&(segment.traces.len() as u32).to_le_bytes());
    for shot in &segment.traces {
        out.extend_from_slice(&shot.shot_index.to_le_bytes());
        out.extend_from_slice(&shot.shot_seed.to_le_bytes());
        append_cstr(&mut out, &shot.final_outcome);
        out.extend_from_slice(&(shot.classical_bits.len() as u32).to_le_bytes());
        out.extend_from_slice(&shot.classical_bits);
        out.extend_from_slice(&(shot.measures.len() as u32).to_le_bytes());
        for m in &shot.measures {
            out.extend_from_slice(&m.gate_index.to_le_bytes());
            out.extend_from_slice(&m.qubit.to_le_bytes());
            out.extend_from_slice(&m.cbit.to_le_bytes());
            out.extend_from_slice(&m.p0.to_le_bytes());
            out.extend_from_slice(&m.p1.to_le_bytes());
            out.push(m.outcome);
            append_cstr(&mut out, &m.pre_measure_statevector_digest);
        }
    }
    out.extend_from_slice(&(segment.marginal_witnesses.len() as u32).to_le_bytes());
    for witness in &segment.marginal_witnesses {
        out.extend_from_slice(&witness.qubit.to_le_bytes());
        out.extend_from_slice(&witness.reference_p0.to_le_bytes());
        out.extend_from_slice(&witness.reference_p1.to_le_bytes());
        out.extend_from_slice(&(witness.pre_measure_statevector.len() as u32).to_le_bytes());
        for (re, im) in &witness.pre_measure_statevector {
            out.extend_from_slice(&re.to_le_bytes());
            out.extend_from_slice(&im.to_le_bytes());
        }
        append_cstr(&mut out, &witness.pre_measure_statevector_digest);
    }
    out
}

pub fn decode_trajectory_segment(
    payload: &[u8],
    marker: &[u8],
) -> Option<(TrajectorySegment, usize)> {
    if marker == TRAJ_V2_MARKER {
        decode_trajectory_segment_v2(payload, 0)
    } else {
        decode_trajectory_segment_v1(payload, 0)
    }
}

fn decode_trajectory_segment_v1(
    payload: &[u8],
    offset: usize,
) -> Option<(TrajectorySegment, usize)> {
    let (sample_seed, cursor) = read_u64_le(payload, offset)?;
    let (shots, cursor) = read_u64_le(payload, cursor)?;
    let (measurement_spec_hash, cursor) = read_cstr(payload, cursor)?;
    let (trajectory_digest, cursor) = read_cstr(payload, cursor)?;
    let (shot_count, mut cursor) = read_u32_le(payload, cursor)?;

    let mut traces = Vec::with_capacity(shot_count as usize);
    for _ in 0..shot_count {
        let (shot_index, next) = read_u64_le(payload, cursor)?;
        let (shot_seed, next) = read_u64_le(payload, next)?;
        let (final_outcome, next) = read_cstr(payload, next)?;
        let (classical_len, next) = read_u32_le(payload, next)?;
        let classical_end = next + classical_len as usize;
        let classical_bits = payload.get(next..classical_end)?.to_vec();
        cursor = classical_end;
        let (measure_count, next) = read_u32_le(payload, cursor)?;
        cursor = next;
        let mut measures = Vec::with_capacity(measure_count as usize);
        for _ in 0..measure_count {
            let (gate_index, next) = read_u32_le(payload, cursor)?;
            let (qubit, next) = read_u32_le(payload, next)?;
            let (cbit, next) = read_u32_le(payload, next)?;
            let (p0, next) = read_f64_le(payload, next)?;
            let (p1, next) = read_f64_le(payload, next)?;
            let outcome = *payload.get(next)?;
            cursor = next + 1;
            measures.push(TrajectoryMeasureEvent {
                gate_index,
                qubit,
                cbit,
                p0,
                p1,
                outcome,
                pre_measure_statevector_digest: String::new(),
            });
        }
        traces.push(TrajectoryShotTrace {
            shot_index,
            shot_seed,
            final_outcome,
            classical_bits,
            measures,
        });
    }

    Some((
        TrajectorySegment {
            sample_seed,
            shots,
            measurement_spec_hash,
            trajectory_digest,
            qubit_count: 0,
            unitary_link_digest: String::new(),
            traces,
            marginal_witnesses: Vec::new(),
        },
        cursor,
    ))
}

fn decode_trajectory_segment_v2(
    payload: &[u8],
    offset: usize,
) -> Option<(TrajectorySegment, usize)> {
    let (sample_seed, cursor) = read_u64_le(payload, offset)?;
    let (shots, cursor) = read_u64_le(payload, cursor)?;
    let (measurement_spec_hash, cursor) = read_cstr(payload, cursor)?;
    let (trajectory_digest, cursor) = read_cstr(payload, cursor)?;
    let (qubit_count, cursor) = read_u32_le(payload, cursor)?;
    let (unitary_link_digest, cursor) = read_cstr(payload, cursor)?;
    let (shot_count, mut cursor) = read_u32_le(payload, cursor)?;

    let mut traces = Vec::with_capacity(shot_count as usize);
    for _ in 0..shot_count {
        let (shot_index, next) = read_u64_le(payload, cursor)?;
        let (shot_seed, next) = read_u64_le(payload, next)?;
        let (final_outcome, next) = read_cstr(payload, next)?;
        let (classical_len, next) = read_u32_le(payload, next)?;
        let classical_end = next + classical_len as usize;
        let classical_bits = payload.get(next..classical_end)?.to_vec();
        cursor = classical_end;
        let (measure_count, next) = read_u32_le(payload, cursor)?;
        cursor = next;
        let mut measures = Vec::with_capacity(measure_count as usize);
        for _ in 0..measure_count {
            let (gate_index, next) = read_u32_le(payload, cursor)?;
            let (qubit, next) = read_u32_le(payload, next)?;
            let (cbit, next) = read_u32_le(payload, next)?;
            let (p0, next) = read_f64_le(payload, next)?;
            let (p1, next) = read_f64_le(payload, next)?;
            let outcome = *payload.get(next)?;
            let (pre_measure_statevector_digest, next) = read_cstr(payload, next + 1)?;
            cursor = next;
            measures.push(TrajectoryMeasureEvent {
                gate_index,
                qubit,
                cbit,
                p0,
                p1,
                outcome,
                pre_measure_statevector_digest,
            });
        }
        traces.push(TrajectoryShotTrace {
            shot_index,
            shot_seed,
            final_outcome,
            classical_bits,
            measures,
        });
    }

    let (witness_count, mut cursor) = read_u32_le(payload, cursor)?;
    let mut marginal_witnesses = Vec::with_capacity(witness_count as usize);
    for _ in 0..witness_count {
        let (qubit, next) = read_u32_le(payload, cursor)?;
        let (reference_p0, next) = read_f64_le(payload, next)?;
        let (reference_p1, next) = read_f64_le(payload, next)?;
        let (sv_len, next) = read_u32_le(payload, next)?;
        cursor = next;
        let mut pre_measure_statevector = Vec::with_capacity(sv_len as usize);
        for _ in 0..sv_len {
            let (re, next) = read_f64_le(payload, cursor)?;
            let (im, next) = read_f64_le(payload, next)?;
            cursor = next;
            pre_measure_statevector.push((re, im));
        }
        let (pre_measure_statevector_digest, next) = read_cstr(payload, cursor)?;
        cursor = next;
        marginal_witnesses.push(TrajectoryMarginalWitness {
            qubit,
            reference_p0,
            reference_p1,
            pre_measure_statevector,
            pre_measure_statevector_digest,
        });
    }

    Some((
        TrajectorySegment {
            sample_seed,
            shots,
            measurement_spec_hash,
            trajectory_digest,
            qubit_count,
            unitary_link_digest,
            traces,
            marginal_witnesses,
        },
        cursor,
    ))
}

/// Reads `unitary_link_digest` without running full marginal/zk verification (v2 peek).
pub fn peek_trajectory_unitary_link_digest(proof: &[u8]) -> Option<String> {
    let (_, tail) = split_trajectory_tail(proof)?;
    let (payload, marker) = tail?;
    let (segment, end) = decode_trajectory_segment(payload, marker)?;
    if end != payload.len() || segment.unitary_link_digest.is_empty() {
        return None;
    }
    Some(segment.unitary_link_digest)
}

fn find_trajectory_tail_marker(proof: &[u8]) -> Option<(usize, &'static [u8])> {
    let mut best: Option<(usize, &'static [u8])> = None;
    for marker in [TRAJ_V2_MARKER, TRAJ_V1_MARKER] {
        if let Some(pos) = proof.windows(marker.len()).rposition(|w| w == marker) {
            best = Some(match best {
                Some((bpos, _)) if bpos > pos => best.unwrap(),
                _ => (pos, marker),
            });
        }
    }
    best
}

/// Appends a trajectory tail to a STARK transcript (after optional distribution / Born tails).
pub fn append_trajectory_tail(mut proof: Vec<u8>, segment: &TrajectorySegment) -> Vec<u8> {
    let marker = if segment.marginal_witnesses.is_empty() && segment.unitary_link_digest.is_empty()
    {
        TRAJ_V1_MARKER
    } else {
        TRAJ_V2_MARKER
    };
    let payload = encode_trajectory_segment(segment, marker);
    proof.extend_from_slice(marker);
    proof.extend_from_slice(&(payload.len() as u32).to_le_bytes());
    proof.extend_from_slice(&payload);
    proof
}

/// Splits a proof into the prefix and optional trajectory tail payload.
pub fn split_trajectory_tail(proof: &[u8]) -> Option<ProofTailSplit<'_>> {
    let (pos, marker) = find_trajectory_tail_marker(proof)?;
    let base = &proof[..pos];
    let cursor = pos + marker.len();
    let (len, cursor) = read_u32_le(proof, cursor)?;
    let end = cursor + len as usize;
    let payload = proof.get(cursor..end)?;
    Some((base, Some((payload, marker))))
}

pub fn has_trajectory_tail(proof: &[u8]) -> bool {
    find_trajectory_tail_marker(proof).is_some()
}

/// Strips the rightmost auxiliary tail marker suffix (Born, trajectory, or distribution).
pub fn strip_one_aux_tail(proof: &[u8]) -> &[u8] {
    let mut best: Option<usize> = None;
    const DIST_V2_MARKER: &[u8] = b"_M31_DIST_V2_";
    const DIST_V1_MARKER: &[u8] = b"_M31_DIST_V1_";
    for marker in [
        TRAJ_V2_MARKER,
        TRAJ_V1_MARKER,
        DIST_V2_MARKER,
        DIST_V1_MARKER,
    ] {
        if let Some(pos) = proof.windows(marker.len()).rposition(|w| w == marker) {
            best = Some(best.map_or(pos, |b| b.max(pos)));
        }
    }
    #[cfg(feature = "plonky3-stark")]
    {
        let born = crate::plonky3_stark::BORN_STARK_TAIL_MARKER;
        if let Some(pos) = proof.windows(born.len()).rposition(|w| w == born) {
            best = Some(best.map_or(pos, |b| b.max(pos)));
        }
        let traj_stark = crate::plonky3_stark::TRAJ_STARK_TAIL_MARKER;
        if let Some(pos) = proof
            .windows(traj_stark.len())
            .rposition(|w| w == traj_stark)
        {
            best = Some(best.map_or(pos, |b| b.max(pos)));
        }
    }
    best.map(|pos| &proof[..pos]).unwrap_or(proof)
}

/// Returns the unitary STARK body with all optional tails removed.
pub fn base_proof_without_aux_tails(proof: &[u8]) -> &[u8] {
    let mut base = proof;
    loop {
        let stripped = strip_one_aux_tail(base);
        if stripped.len() == base.len() {
            return base;
        }
        base = stripped;
    }
}

pub fn verify_trajectory_segment(segment: &TrajectorySegment) -> bool {
    if segment.trajectory_digest.is_empty() {
        eprintln!("[STARK Core] Failed: trajectory_digest is empty");
        return false;
    }
    if segment.traces.len() as u64 != segment.shots {
        eprintln!("[STARK Core] Failed: trajectory shot count mismatch");
        return false;
    }
    for window in segment.traces.windows(2) {
        if window[0].shot_index >= window[1].shot_index {
            eprintln!("[STARK Core] Failed: trajectory shot_index not strictly increasing");
            return false;
        }
    }
    for (i, shot) in segment.traces.iter().enumerate() {
        if shot.shot_index != i as u64 {
            eprintln!("[STARK Core] Failed: trajectory shot_index not contiguous");
            return false;
        }
        let expected_seed = segment.sample_seed.wrapping_add(shot.shot_index);
        if shot.shot_seed != expected_seed {
            eprintln!("[STARK Core] Failed: trajectory shot_seed mismatch");
            return false;
        }
    }
    let recomputed = calculate_trajectory_digest(&segment.traces);
    if recomputed != segment.trajectory_digest {
        eprintln!(
            "[STARK Core] Failed: trajectory_digest mismatch (claimed {}, recomputed {})",
            segment.trajectory_digest, recomputed
        );
        return false;
    }
    if !segment.marginal_witnesses.is_empty()
        && !crate::air::trajectory::evaluate_trajectory_marginal_constraints(segment)
    {
        eprintln!("[STARK Core] Failed: trajectory marginal constraints not satisfied");
        return false;
    }
    if !crate::air::shot_sampling::evaluate_trajectory_shot_sampling_constraints(segment) {
        eprintln!("[STARK Core] Failed: trajectory shot sampling constraints not satisfied");
        return false;
    }
    true
}

pub fn decode_and_verify_trajectory_tail(
    payload: &[u8],
    marker: &[u8],
) -> Option<TrajectorySegment> {
    if marker != TRAJ_V1_MARKER && marker != TRAJ_V2_MARKER {
        return None;
    }
    let (segment, end) = decode_trajectory_segment(payload, marker)?;
    if end != payload.len() {
        return None;
    }
    if !verify_trajectory_segment(&segment) {
        return None;
    }
    Some(segment)
}

/// Aggregates per-shot final outcomes into a counts histogram.
pub fn counts_from_trajectory_segment(
    segment: &TrajectorySegment,
) -> std::collections::BTreeMap<String, u64> {
    use std::collections::BTreeMap;
    let mut counts = BTreeMap::new();
    for shot in &segment.traces {
        *counts.entry(shot.final_outcome.clone()).or_insert(0) += 1;
    }
    counts
}

/// Verifies trajectory tail binding: segment metadata + shot outcomes → deterministic counts.
pub fn verify_trajectory_binding(
    proof: &[u8],
    expected_seed: u64,
    expected_shots: u64,
    expected_measurement_spec_hash: Option<&str>,
    reported_counts: &std::collections::BTreeMap<String, u64>,
    reported_shots: u64,
) -> bool {
    let traj_proof = crate::aggregation::trajectory_proof_view(proof);
    let (_, tail) = match split_trajectory_tail(traj_proof) {
        Some(parts) => parts,
        None => {
            eprintln!("[STARK Core] Failed: missing trajectory tail");
            return false;
        }
    };
    let (payload, marker) = match tail {
        Some(parts) => parts,
        None => {
            eprintln!("[STARK Core] Failed: missing trajectory tail");
            return false;
        }
    };
    let segment = match decode_and_verify_trajectory_tail(payload, marker) {
        Some(seg) => seg,
        None => {
            eprintln!("[STARK Core] Failed: invalid trajectory segment");
            return false;
        }
    };
    if segment.sample_seed != expected_seed {
        eprintln!("[STARK Core] Failed: trajectory sample_seed mismatch");
        return false;
    }
    if segment.shots != expected_shots || segment.shots != reported_shots {
        eprintln!("[STARK Core] Failed: trajectory shots mismatch");
        return false;
    }
    if let Some(expected_hash) = expected_measurement_spec_hash {
        if expected_hash.is_empty() {
            eprintln!("[STARK Core] Failed: expected measurement_spec_hash is empty");
            return false;
        }
        if segment.measurement_spec_hash != expected_hash {
            eprintln!("[STARK Core] Failed: trajectory measurement_spec_hash mismatch");
            return false;
        }
    }
    let recomputed = counts_from_trajectory_segment(&segment);
    if &recomputed != reported_counts {
        eprintln!("[STARK Core] Failed: counts do not match trajectory segment");
        return false;
    }

    #[cfg(feature = "plonky3-stark")]
    if crate::plonky3_stark::has_trajectory_stark_tail(traj_proof) {
        if !crate::plonky3_stark::segment_supports_trajectory_zk(&segment) {
            eprintln!("[STARK Core] Failed: trajectory zk tail without zk-capable segment");
            return false;
        }
        let Some(bundle) = crate::plonky3_stark::split_trajectory_stark_tail(traj_proof) else {
            eprintln!("[STARK Core] Failed: malformed trajectory zk tail");
            return false;
        };
        // sub_task_id is validated via prefix binding in full verify path; here we only check bundle shape.
        if bundle.is_empty() {
            eprintln!("[STARK Core] Failed: empty trajectory zk bundle");
            return false;
        }
    }

    true
}

#[cfg(test)]
mod tests {
    use super::*;

    fn demo_segment() -> TrajectorySegment {
        use rand::rngs::StdRng;
        use rand::{Rng, SeedableRng};

        let make_shot = |shot_index: u64, shot_seed: u64, p0_1: f64, p1_1: f64| {
            let mut rng = StdRng::seed_from_u64(shot_seed);
            let u0: f64 = rng.gen();
            let o0 = if u0 < 0.5 { 0u8 } else { 1 };
            let u1: f64 = rng.gen();
            let denom = (p0_1 + p1_1).max(1e-30_f64);
            let o1 = if u1 < p0_1 / denom { 0u8 } else { 1 };
            TrajectoryShotTrace {
                shot_index,
                shot_seed,
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
                        pre_measure_statevector_digest: String::new(),
                    },
                    TrajectoryMeasureEvent {
                        gate_index: 3,
                        qubit: 1,
                        cbit: 1,
                        p0: p0_1,
                        p1: p1_1,
                        outcome: o1,
                        pre_measure_statevector_digest: String::new(),
                    },
                ],
            }
        };

        let traces = vec![
            make_shot(0, 7, 1.0, 0.0),
            make_shot(1, 8, 0.0, 1.0),
        ];
        TrajectorySegment {
            sample_seed: 7,
            shots: 2,
            measurement_spec_hash: "spec-hash".into(),
            trajectory_digest: calculate_trajectory_digest(&traces),
            qubit_count: 0,
            unitary_link_digest: String::new(),
            traces,
            marginal_witnesses: Vec::new(),
        }
    }

    #[test]
    fn trajectory_segment_roundtrip() {
        let segment = demo_segment();
        let proof = append_trajectory_tail(b"stark".to_vec(), &segment);
        let (_, tail) = split_trajectory_tail(&proof).expect("split");
        let (payload, marker) = tail.expect("tail present");
        assert_eq!(marker, TRAJ_V1_MARKER);
        let decoded = decode_and_verify_trajectory_tail(payload, marker).expect("decode");
        assert_eq!(decoded, segment);
    }

    #[test]
    fn trajectory_binding_matches_counts() {
        let segment = demo_segment();
        let proof = append_trajectory_tail(b"stark".to_vec(), &segment);
        let counts = counts_from_trajectory_segment(&segment);
        assert!(verify_trajectory_binding(
            &proof,
            7,
            2,
            Some("spec-hash"),
            &counts,
            2,
        ));
    }

    #[test]
    fn tampered_trajectory_digest_rejected() {
        let mut segment = demo_segment();
        segment.trajectory_digest = "deadbeef".into();
        assert!(!verify_trajectory_segment(&segment));
    }
}

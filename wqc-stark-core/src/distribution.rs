//! C2a-2/4: optional distribution tail bound to a v1/v2 STARK transcript.
//!
//! Appended after the main proof body:
//! `_M31_DIST_V2_` + sample_seed + shots + measurement_spec_hash + probability_digest + probs
//! (`_M31_DIST_V1_` tails without `measurement_spec_hash` remain decodable for devnet replay).

pub const DIST_V1_MARKER: &[u8] = b"_M31_DIST_V1_";
pub const DIST_V2_MARKER: &[u8] = b"_M31_DIST_V2_";

type ProofTailSplit<'a> = (&'a [u8], Option<(&'a [u8], &'static [u8])>);

/// C2b optional terminal statevector binding for Born-rule AIR verification.
#[derive(Debug, Clone, PartialEq)]
pub struct BornBinding {
    pub qubit_count: u32,
    pub classical_bit_count: u32,
    /// Program-order `(qubit, cbit)` pairs.
    pub measures: Vec<(u32, u32)>,
    /// Dense terminal amplitudes in computational basis order.
    pub terminal_statevector: Vec<(f64, f64)>,
    /// SHA3-256 hex of canonical quantized statevector JSON (unitary↔Born link).
    pub terminal_statevector_digest: String,
}

impl BornBinding {
    pub fn from_specs(
        qubit_count: u32,
        classical_bit_count: u32,
        measures: &[(u32, u32)],
        terminal_statevector: Vec<(f64, f64)>,
    ) -> Option<Self> {
        if qubit_count as usize > crate::air::distribution::BORN_AIR_MAX_QUBITS {
            return None;
        }
        let dim = 1usize << qubit_count;
        if terminal_statevector.len() != dim {
            return None;
        }
        let terminal_statevector_digest =
            calculate_terminal_statevector_digest(&terminal_statevector);
        Some(Self {
            qubit_count,
            classical_bit_count,
            measures: measures.to_vec(),
            terminal_statevector,
            terminal_statevector_digest,
        })
    }

    pub fn with_digest(mut self, digest: String) -> Self {
        self.terminal_statevector_digest = digest;
        self
    }
}

/// Born-rule binding carried in the proof transcript tail.
#[derive(Debug, Clone, PartialEq)]
pub struct DistributionSegment {
    pub sample_seed: u64,
    pub shots: u64,
    /// SHA3-256 hex of canonical measurement spec JSON (C2a-4); empty on legacy V1 tails.
    pub measurement_spec_hash: String,
    pub probability_digest: String,
    /// Sorted lexicographically by outcome key (Qiskit bitstring order).
    pub probabilities: Vec<(String, f64)>,
    /// C2b: optional terminal statevector + measures for Born AIR verification.
    pub born_binding: Option<BornBinding>,
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

/// Canonical JSON for SHA3-256 hashing — must match `wqc-core` / orchestrator.
pub fn format_go_probability_json(probabilities: &[(String, f64)]) -> String {
    let mut pairs = String::new();
    for (key, value) in probabilities {
        if !pairs.is_empty() {
            pairs.push(',');
        }
        pairs.push_str(&format!(r#""{key}":{}"#, format_go_float(*value)));
    }
    format!(r#"{{"probabilities":{{{pairs}}}}}"#)
}

/// SHA3-256 hex digest of the canonical probability JSON.
pub fn calculate_probability_digest(probabilities: &[(String, f64)]) -> String {
    use sha3::{Digest, Sha3_256};
    hex::encode(Sha3_256::digest(
        format_go_probability_json(probabilities).as_bytes(),
    ))
}

/// Fixed-point scale for terminal statevector digest (matches AIR `f64_to_m31`).
pub const TERMINAL_STATEVECTOR_DIGEST_SCALE: f64 = 10_000.0;

fn quantize_for_digest(val: f64) -> f64 {
    (val * TERMINAL_STATEVECTOR_DIGEST_SCALE).round() / TERMINAL_STATEVECTOR_DIGEST_SCALE
}

/// Quantizes amplitudes to the digest/AIR fixed-point grid (C2b/C2c binding).
pub fn canonicalize_terminal_statevector(statevector: &[(f64, f64)]) -> Vec<(f64, f64)> {
    statevector
        .iter()
        .map(|(re, im)| (quantize_for_digest(*re), quantize_for_digest(*im)))
        .collect()
}

/// Canonical JSON for terminal statevector digest — must match `wqc-core`.
pub fn format_terminal_statevector_json(statevector: &[(f64, f64)]) -> String {
    let mut amps = String::new();
    for (re, im) in statevector {
        if !amps.is_empty() {
            amps.push(',');
        }
        amps.push_str(&format!(
            r#"{{"im":{},"re":{}}}"#,
            format_go_float(quantize_for_digest(*im)),
            format_go_float(quantize_for_digest(*re)),
        ));
    }
    format!(r#"{{"statevector":{{"amplitudes":[{amps}]}}}}"#)
}

/// SHA3-256 hex digest of the canonical quantized terminal statevector JSON.
pub fn calculate_terminal_statevector_digest(statevector: &[(f64, f64)]) -> String {
    use sha3::{Digest, Sha3_256};
    hex::encode(Sha3_256::digest(
        format_terminal_statevector_json(statevector).as_bytes(),
    ))
}

fn format_go_float(val: f64) -> String {
    if val == (val as i64) as f64 {
        format!("{:.1}", val)
    } else {
        format!("{val}")
    }
}

/// Encodes a distribution segment (without the outer tail wrapper).
pub fn encode_distribution_segment(segment: &DistributionSegment) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(&segment.sample_seed.to_le_bytes());
    out.extend_from_slice(&segment.shots.to_le_bytes());
    append_cstr(&mut out, &segment.measurement_spec_hash);
    append_cstr(&mut out, &segment.probability_digest);
    out.extend_from_slice(&(segment.probabilities.len() as u32).to_le_bytes());
    for (key, prob) in &segment.probabilities {
        append_cstr(&mut out, key);
        out.extend_from_slice(&prob.to_le_bytes());
    }
    if let Some(binding) = &segment.born_binding {
        out.extend_from_slice(&binding.qubit_count.to_le_bytes());
        out.extend_from_slice(&binding.classical_bit_count.to_le_bytes());
        out.extend_from_slice(&(binding.measures.len() as u32).to_le_bytes());
        for (qubit, cbit) in &binding.measures {
            out.extend_from_slice(&qubit.to_le_bytes());
            out.extend_from_slice(&cbit.to_le_bytes());
        }
        out.extend_from_slice(&(binding.terminal_statevector.len() as u32).to_le_bytes());
        for (re, im) in &binding.terminal_statevector {
            out.extend_from_slice(&re.to_le_bytes());
            out.extend_from_slice(&im.to_le_bytes());
        }
        append_cstr(&mut out, &binding.terminal_statevector_digest);
    }
    out
}

fn decode_born_binding(payload: &[u8], offset: usize) -> Option<(Option<BornBinding>, usize)> {
    if offset >= payload.len() {
        return Some((None, offset));
    }
    let (qubit_count, cursor) = read_u32_le(payload, offset)?;
    let (classical_bit_count, cursor) = read_u32_le(payload, cursor)?;
    let (measure_count, mut cursor) = read_u32_le(payload, cursor)?;
    let mut measures = Vec::with_capacity(measure_count as usize);
    for _ in 0..measure_count {
        let (qubit, next) = read_u32_le(payload, cursor)?;
        let (cbit, next) = read_u32_le(payload, next)?;
        measures.push((qubit, cbit));
        cursor = next;
    }
    let (sv_len, mut cursor) = read_u32_le(payload, cursor)?;
    let mut terminal_statevector = Vec::with_capacity(sv_len as usize);
    for _ in 0..sv_len {
        let (re, next) = read_f64_le(payload, cursor)?;
        let (im, next) = read_f64_le(payload, next)?;
        terminal_statevector.push((re, im));
        cursor = next;
    }
    let (terminal_statevector_digest, cursor) = if cursor < payload.len() {
        read_cstr(payload, cursor)?
    } else {
        (String::new(), cursor)
    };
    let binding = BornBinding::from_specs(
        qubit_count,
        classical_bit_count,
        &measures,
        terminal_statevector,
    )?
    .with_digest(terminal_statevector_digest);
    Some((Some(binding), cursor))
}

/// Decodes a V2 distribution segment payload (includes `measurement_spec_hash`).
pub fn decode_distribution_segment(
    proof: &[u8],
    offset: usize,
) -> Option<(DistributionSegment, usize)> {
    let (sample_seed, cursor) = read_u64_le(proof, offset)?;
    let (shots, cursor) = read_u64_le(proof, cursor)?;
    let (measurement_spec_hash, cursor) = read_cstr(proof, cursor)?;
    let (probability_digest, cursor) = read_cstr(proof, cursor)?;
    let (prob_count, mut cursor) = read_u32_le(proof, cursor)?;

    let mut probabilities = Vec::with_capacity(prob_count as usize);
    for _ in 0..prob_count {
        let (key, next) = read_cstr(proof, cursor)?;
        let (prob, next) = read_f64_le(proof, next)?;
        probabilities.push((key, prob));
        cursor = next;
    }

    let (segment, cursor) = (
        DistributionSegment {
            sample_seed,
            shots,
            measurement_spec_hash,
            probability_digest,
            probabilities,
            born_binding: None,
        },
        cursor,
    );
    finalize_v2_segment(segment, proof, cursor)
}

fn finalize_v2_segment(
    mut segment: DistributionSegment,
    payload: &[u8],
    cursor: usize,
) -> Option<(DistributionSegment, usize)> {
    let (born_binding, end) = decode_born_binding(payload, cursor)?;
    segment.born_binding = born_binding;
    Some((segment, end))
}

/// Decodes a legacy V1 distribution segment payload (no `measurement_spec_hash`).
pub fn decode_distribution_segment_v1(
    proof: &[u8],
    offset: usize,
) -> Option<(DistributionSegment, usize)> {
    let (sample_seed, cursor) = read_u64_le(proof, offset)?;
    let (shots, cursor) = read_u64_le(proof, cursor)?;
    let (probability_digest, cursor) = read_cstr(proof, cursor)?;
    let (prob_count, mut cursor) = read_u32_le(proof, cursor)?;

    let mut probabilities = Vec::with_capacity(prob_count as usize);
    for _ in 0..prob_count {
        let (key, next) = read_cstr(proof, cursor)?;
        let (prob, next) = read_f64_le(proof, next)?;
        probabilities.push((key, prob));
        cursor = next;
    }

    Some((
        DistributionSegment {
            sample_seed,
            shots,
            measurement_spec_hash: String::new(),
            probability_digest,
            probabilities,
            born_binding: None,
        },
        cursor,
    ))
}

fn find_distribution_tail_marker(proof: &[u8]) -> Option<(usize, &'static [u8])> {
    let v2 = proof
        .windows(DIST_V2_MARKER.len())
        .rposition(|w| w == DIST_V2_MARKER)
        .map(|pos| (pos, DIST_V2_MARKER));
    let v1 = proof
        .windows(DIST_V1_MARKER.len())
        .rposition(|w| w == DIST_V1_MARKER)
        .map(|pos| (pos, DIST_V1_MARKER));
    match (v2, v1) {
        (Some(a), Some(b)) => Some(if a.0 >= b.0 { a } else { b }),
        (Some(a), None) => Some(a),
        (None, Some(b)) => Some(b),
        (None, None) => None,
    }
}

/// Appends a distribution tail to a v1/v2 STARK transcript.
pub fn append_distribution_tail(mut proof: Vec<u8>, segment: &DistributionSegment) -> Vec<u8> {
    let payload = encode_distribution_segment(segment);
    proof.extend_from_slice(DIST_V2_MARKER);
    proof.extend_from_slice(&(payload.len() as u32).to_le_bytes());
    proof.extend_from_slice(&payload);
    proof
}

/// Splits a proof into the base STARK body and optional distribution tail.
/// A Born zk STARK transcript may follow the distribution payload.
pub fn split_distribution_tail(proof: &[u8]) -> Option<ProofTailSplit<'_>> {
    let (pos, marker) = find_distribution_tail_marker(proof)?;
    let base = &proof[..pos];
    let cursor = pos + marker.len();
    let (len, cursor) = read_u32_le(proof, cursor)?;
    let end = cursor + len as usize;
    let payload = proof.get(cursor..end)?;
    Some((base, Some((payload, marker))))
}

/// Strips an optional Born STARK suffix (returns proof up to and including distribution payload end).
pub fn proof_without_born_stark_tail(proof: &[u8]) -> &[u8] {
    #[cfg(feature = "plonky3-stark")]
    {
        if let Some(pos) = proof
            .windows(crate::plonky3_stark::BORN_STARK_TAIL_MARKER.len())
            .rposition(|w| w == crate::plonky3_stark::BORN_STARK_TAIL_MARKER)
        {
            return &proof[..pos];
        }
    }
    proof
}

/// Returns the base proof when no distribution tail is present.
pub fn base_proof_without_distribution_tail(proof: &[u8]) -> &[u8] {
    crate::trajectory::base_proof_without_aux_tails(proof)
}

/// Verifies sorted keys, non-empty digest, and digest recomputation from embedded probs.
pub fn verify_distribution_segment(segment: &DistributionSegment) -> bool {
    if segment.probability_digest.is_empty() {
        eprintln!("[STARK Core] Failed: distribution probability_digest is empty");
        return false;
    }

    for window in segment.probabilities.windows(2) {
        if window[0].0 >= window[1].0 {
            eprintln!("[STARK Core] Failed: distribution outcome keys not strictly sorted");
            return false;
        }
    }

    let recomputed = calculate_probability_digest(&segment.probabilities);
    if recomputed != segment.probability_digest {
        eprintln!(
            "[STARK Core] Failed: distribution probability_digest mismatch (claimed {}, recomputed {})",
            segment.probability_digest, recomputed
        );
        return false;
    }

    true
}

/// Decodes and verifies a distribution tail payload (post-marker bytes).
pub fn decode_and_verify_distribution_tail(
    payload: &[u8],
    marker: &[u8],
) -> Option<DistributionSegment> {
    let (segment, end) = if marker == DIST_V2_MARKER {
        decode_distribution_segment(payload, 0)?
    } else {
        decode_distribution_segment_v1(payload, 0)?
    };
    if end != payload.len() {
        return None;
    }
    if !verify_distribution_segment(&segment) {
        return None;
    }
    if crate::air::distribution::evaluate_born_constraint_sum(&segment) != 0 {
        eprintln!("[STARK Core] Failed: Born AIR constraint violation");
        return None;
    }
    Some(segment)
}

/// Deterministic shot sampling — matches `wqc-core` `sample_counts_from_probabilities`.
pub fn sample_counts_from_probabilities(
    probabilities: &[(String, f64)],
    shots: u64,
    seed: u64,
) -> std::collections::BTreeMap<String, u64> {
    use rand::rngs::StdRng;
    use rand::{Rng, SeedableRng};
    use std::collections::BTreeMap;

    let mut counts: BTreeMap<String, u64> = BTreeMap::new();
    if shots == 0 || probabilities.is_empty() {
        return counts;
    }

    let total: f64 = probabilities.iter().map(|(_, p)| p).sum();
    let mut cumulative = Vec::with_capacity(probabilities.len());
    let mut acc = 0.0;
    for (label, prob) in probabilities {
        acc += prob / total;
        cumulative.push((label.clone(), acc));
    }

    let mut rng = StdRng::seed_from_u64(seed);
    for _ in 0..shots {
        let r: f64 = rng.gen();
        let label = cumulative
            .iter()
            .find(|(_, c)| r <= *c)
            .map(|(label, _)| label.clone())
            .unwrap_or_else(|| cumulative.last().unwrap().0.clone());
        *counts.entry(label).or_insert(0) += 1;
    }
    counts
}

/// Verifies proof tail binding: segment metadata + Born probs → deterministic counts.
pub fn verify_distribution_binding(
    proof: &[u8],
    expected_seed: u64,
    expected_shots: u64,
    expected_measurement_spec_hash: Option<&str>,
    reported_counts: &std::collections::BTreeMap<String, u64>,
    reported_shots: u64,
) -> bool {
    let Some((_, Some((payload, marker)))) = split_distribution_tail(proof) else {
        eprintln!("[STARK Core] Failed: missing distribution tail");
        return false;
    };
    let segment = match decode_and_verify_distribution_tail(payload, marker) {
        Some(seg) => seg,
        None => {
            eprintln!("[STARK Core] Failed: invalid distribution segment");
            return false;
        }
    };
    if segment.sample_seed != expected_seed {
        eprintln!("[STARK Core] Failed: distribution sample_seed mismatch");
        return false;
    }
    if segment.shots != expected_shots || segment.shots != reported_shots {
        eprintln!("[STARK Core] Failed: distribution shots mismatch");
        return false;
    }
    if let Some(expected_hash) = expected_measurement_spec_hash {
        if expected_hash.is_empty() {
            eprintln!("[STARK Core] Failed: expected measurement_spec_hash is empty");
            return false;
        }
        if segment.measurement_spec_hash != expected_hash {
            eprintln!("[STARK Core] Failed: distribution measurement_spec_hash mismatch");
            return false;
        }
    }
    let recomputed = sample_counts_from_probabilities(
        &segment.probabilities,
        segment.shots,
        segment.sample_seed,
    );
    if &recomputed != reported_counts {
        eprintln!("[STARK Core] Failed: counts do not match Born probabilities and seed");
        return false;
    }
    if crate::air::distribution::evaluate_born_constraint_sum(&segment) != 0 {
        eprintln!("[STARK Core] Failed: Born AIR constraint violation");
        return false;
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bell_segment() -> DistributionSegment {
        DistributionSegment {
            sample_seed: 42,
            shots: 1024,
            measurement_spec_hash: "abc123".into(),
            probability_digest: calculate_probability_digest(&[
                ("00".into(), 0.5),
                ("11".into(), 0.5),
            ]),
            probabilities: vec![("00".into(), 0.5), ("11".into(), 0.5)],
            born_binding: None,
        }
    }

    #[test]
    fn probability_digest_matches_golden_bell() {
        assert_eq!(
            calculate_probability_digest(&[("00".into(), 0.5), ("11".into(), 0.5)]),
            "ef8f4691ad99dc93489c72d6a5863df7974ce1d0c1ad58525c133c15d43190fc"
        );
    }

    #[test]
    fn segment_roundtrip_and_tail_split() {
        let segment = bell_segment();
        let base = b"fake-stark-body";
        let proof = append_distribution_tail(base.to_vec(), &segment);
        let (decoded_base, tail) = split_distribution_tail(&proof).expect("split");
        assert_eq!(decoded_base, base);
        let (payload, marker) = tail.expect("tail");
        assert_eq!(marker, DIST_V2_MARKER);
        let decoded = decode_and_verify_distribution_tail(payload, marker).expect("decode");
        assert_eq!(decoded, segment);
    }

    #[test]
    fn unsorted_keys_rejected() {
        let mut segment = bell_segment();
        segment.probabilities = vec![("11".into(), 0.5), ("00".into(), 0.5)];
        assert!(!verify_distribution_segment(&segment));
    }

    #[test]
    fn sample_counts_match_core_golden_h_seed99() {
        let probs = vec![("0".into(), 0.5), ("1".into(), 0.5)];
        let counts = sample_counts_from_probabilities(&probs, 256, 99);
        assert_eq!(counts.get("0").copied(), Some(118));
        assert_eq!(counts.get("1").copied(), Some(138));
    }

    #[test]
    fn verify_distribution_binding_roundtrip() {
        let segment = bell_segment();
        let counts = sample_counts_from_probabilities(
            &segment.probabilities,
            segment.shots,
            segment.sample_seed,
        );
        let proof = append_distribution_tail(b"stark".to_vec(), &segment);
        assert!(verify_distribution_binding(
            &proof,
            segment.sample_seed,
            segment.shots,
            Some(&segment.measurement_spec_hash),
            &counts,
            segment.shots,
        ));
    }

    #[test]
    fn v1_tail_still_decodes_without_measurement_spec_hash() {
        let mut payload = Vec::new();
        payload.extend_from_slice(&42u64.to_le_bytes());
        payload.extend_from_slice(&128u64.to_le_bytes());
        append_cstr(
            &mut payload,
            "b3de34846864135b2fc5dc4cfc94c950b8e4c95b98015ba3e09fa46ada453e20",
        );
        payload.extend_from_slice(&1u32.to_le_bytes());
        append_cstr(&mut payload, "0");
        payload.extend_from_slice(&1.0f64.to_le_bytes());

        let mut proof = b"stark".to_vec();
        proof.extend_from_slice(DIST_V1_MARKER);
        proof.extend_from_slice(&(payload.len() as u32).to_le_bytes());
        proof.extend_from_slice(&payload);

        let seg = decode_and_verify_distribution_tail(&payload, DIST_V1_MARKER).expect("v1 decode");
        assert!(seg.measurement_spec_hash.is_empty());
    }

    #[test]
    fn born_binding_roundtrip_in_v2_tail() {
        use crate::air::distribution::{evaluate_born_constraint_sum, BornMeasureSpec};
        use crate::distribution::BornBinding;

        let inv_sqrt2 = 1.0f64 / 2.0f64.sqrt();
        let sv = vec![(inv_sqrt2, 0.0), (0.0, 0.0), (0.0, 0.0), (inv_sqrt2, 0.0)];
        let measures = vec![
            BornMeasureSpec { qubit: 0, cbit: 0 },
            BornMeasureSpec { qubit: 1, cbit: 1 },
        ];
        let probs =
            crate::air::distribution::born_probabilities_from_statevector(&sv, 2, &measures, 2)
                .expect("born");
        let prob_vec: Vec<(String, f64)> = probs.into_iter().collect();
        let binding = BornBinding::from_specs(2, 2, &[(0, 0), (1, 1)], sv).expect("bind");
        let segment = DistributionSegment {
            sample_seed: 42,
            shots: 128,
            measurement_spec_hash: "spec".into(),
            probability_digest: calculate_probability_digest(&prob_vec),
            probabilities: prob_vec,
            born_binding: Some(binding),
        };
        assert_eq!(evaluate_born_constraint_sum(&segment), 0);
        let proof = append_distribution_tail(b"stark".to_vec(), &segment);
        let (_, Some((payload, marker))) = split_distribution_tail(&proof).expect("split") else {
            panic!("tail missing");
        };
        let decoded = decode_and_verify_distribution_tail(payload, marker).expect("decode");
        assert_eq!(decoded, segment);
    }

    #[test]
    fn tampered_digest_rejected() {
        let mut segment = bell_segment();
        segment.probability_digest = "deadbeef".into();
        assert!(!verify_distribution_segment(&segment));
    }
}

//! C2a-2: optional distribution tail bound to a v1/v2 STARK transcript.
//!
//! Appended after the main proof body:
//! `_M31_DIST_V1_` + sample_seed + shots + probability_digest + outcome probabilities.

pub const DIST_V1_MARKER: &[u8] = b"_M31_DIST_V1_";

/// Born-rule binding carried in the proof transcript tail.
#[derive(Debug, Clone, PartialEq)]
pub struct DistributionSegment {
    pub sample_seed: u64,
    pub shots: u64,
    pub probability_digest: String,
    /// Sorted lexicographically by outcome key (Qiskit bitstring order).
    pub probabilities: Vec<(String, f64)>,
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
    append_cstr(&mut out, &segment.probability_digest);
    out.extend_from_slice(&(segment.probabilities.len() as u32).to_le_bytes());
    for (key, prob) in &segment.probabilities {
        append_cstr(&mut out, key);
        out.extend_from_slice(&prob.to_le_bytes());
    }
    out
}

/// Decodes a distribution segment payload (after `DIST_V1_MARKER`).
pub fn decode_distribution_segment(proof: &[u8], offset: usize) -> Option<(DistributionSegment, usize)> {
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
            probability_digest,
            probabilities,
        },
        cursor,
    ))
}

/// Appends a distribution tail to a v1/v2 STARK transcript.
pub fn append_distribution_tail(mut proof: Vec<u8>, segment: &DistributionSegment) -> Vec<u8> {
    let payload = encode_distribution_segment(segment);
    proof.extend_from_slice(DIST_V1_MARKER);
    proof.extend_from_slice(&(payload.len() as u32).to_le_bytes());
    proof.extend_from_slice(&payload);
    proof
}

/// Splits a proof into the base STARK body and optional distribution tail.
pub fn split_distribution_tail(proof: &[u8]) -> Option<(&[u8], Option<&[u8]>)> {
    let pos = proof
        .windows(DIST_V1_MARKER.len())
        .rposition(|w| w == DIST_V1_MARKER)?;
    let base = &proof[..pos];
    let cursor = pos + DIST_V1_MARKER.len();
    let (len, cursor) = read_u32_le(proof, cursor)?;
    let end = cursor + len as usize;
    let payload = proof.get(cursor..end)?;
    if end != proof.len() {
        return None;
    }
    Some((base, Some(payload)))
}

/// Returns the base proof when no distribution tail is present.
pub fn base_proof_without_distribution_tail(proof: &[u8]) -> &[u8] {
    split_distribution_tail(proof)
        .map(|(base, _)| base)
        .unwrap_or(proof)
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
pub fn decode_and_verify_distribution_tail(payload: &[u8]) -> Option<DistributionSegment> {
    let (segment, end) = decode_distribution_segment(payload, 0)?;
    if end != payload.len() {
        return None;
    }
    if !verify_distribution_segment(&segment) {
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
    use rand::{Rng, SeedableRng};
    use rand::rngs::StdRng;
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
    reported_counts: &std::collections::BTreeMap<String, u64>,
    reported_shots: u64,
) -> bool {
    let Some((_, Some(payload))) = split_distribution_tail(proof) else {
        eprintln!("[STARK Core] Failed: missing distribution tail");
        return false;
    };
    let segment = match decode_and_verify_distribution_tail(payload) {
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
    let recomputed = sample_counts_from_probabilities(&segment.probabilities, segment.shots, segment.sample_seed);
    if &recomputed != reported_counts {
        eprintln!("[STARK Core] Failed: counts do not match Born probabilities and seed");
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
            probability_digest: calculate_probability_digest(&[
                ("00".into(), 0.5),
                ("11".into(), 0.5),
            ]),
            probabilities: vec![("00".into(), 0.5), ("11".into(), 0.5)],
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
        let payload = tail.expect("tail");
        let decoded = decode_and_verify_distribution_tail(payload).expect("decode");
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
        let counts = sample_counts_from_probabilities(&segment.probabilities, segment.shots, segment.sample_seed);
        let proof = append_distribution_tail(b"stark".to_vec(), &segment);
        assert!(verify_distribution_binding(
            &proof,
            segment.sample_seed,
            segment.shots,
            &counts,
            segment.shots,
        ));
    }

    #[test]
    fn tampered_digest_rejected() {
        let mut segment = bell_segment();
        segment.probability_digest = "deadbeef".into();
        assert!(!verify_distribution_segment(&segment));
    }
}

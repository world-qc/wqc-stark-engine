//! Optional overlap tail: MPS ket/bra sites → ⟨φ|ψ⟩ bound to `output_result_hash`.
//!
//! Appended after the unitary proof body:
//! `_M31_OVERLAP_V1_` + u32_le(payload_len) + OverlapSegment bytes.

use crate::air::overlap::{evaluate_overlap_constraint_sum, overlap_constraint_failure};

pub const OVERLAP_V1_MARKER: &[u8] = b"_M31_OVERLAP_V1_";

/// Max bond dimension per site in an overlap witness (time-split ScalarTimeSplitBond).
pub const OVERLAP_MAX_BOND: usize = 16;
/// Max ket_right × bra_right environment width (matches core OVERLAP_ENV_LIMIT).
pub const OVERLAP_ENV_LIMIT: usize = 256;
/// Max sites in an overlap witness (Phase 1 MPS width stand-in).
pub const OVERLAP_MAX_QUBITS: usize = 2048;

type ProofTailSplit<'a> = (&'a [u8], Option<(&'a [u8], &'static [u8])>);

/// One MPS site tensor `[left × 2 × right]` with complex entries.
#[derive(Debug, Clone, PartialEq)]
pub struct OverlapSiteTensor {
    pub left_dim: u32,
    pub right_dim: u32,
    /// Flat row-major `[left][phys][right]` complex pairs.
    pub values: Vec<(f64, f64)>,
}

/// Overlap witness carried in the proof transcript tail.
#[derive(Debug, Clone, PartialEq)]
pub struct OverlapSegment {
    pub qubit_count: u32,
    pub amplitude_re: f64,
    pub amplitude_im: f64,
    /// SHA3-256 hex of canonical `{"real":…,"imag":…}` (matches `output_result_hash`).
    pub amplitude_digest: String,
    pub ket_sites: Vec<OverlapSiteTensor>,
    pub bra_sites: Vec<OverlapSiteTensor>,
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

/// Canonical JSON for SHA3-256 — must match wqc-core / orchestrator ComplexResult.
pub fn format_go_amplitude_json(re: f64, im: f64) -> String {
    format!(
        r#"{{"real":{},"imag":{}}}"#,
        format_go_float(re),
        format_go_float(im),
    )
}

/// SHA3-256 hex digest of the canonical amplitude JSON.
pub fn calculate_amplitude_digest(re: f64, im: f64) -> String {
    use sha3::{Digest, Sha3_256};
    hex::encode(Sha3_256::digest(
        format_go_amplitude_json(re, im).as_bytes(),
    ))
}

fn encode_site(out: &mut Vec<u8>, site: &OverlapSiteTensor) {
    out.extend_from_slice(&site.left_dim.to_le_bytes());
    out.extend_from_slice(&site.right_dim.to_le_bytes());
    out.extend_from_slice(&(site.values.len() as u32).to_le_bytes());
    for &(re, im) in &site.values {
        out.extend_from_slice(&re.to_le_bytes());
        out.extend_from_slice(&im.to_le_bytes());
    }
}

fn decode_site(payload: &[u8], offset: usize) -> Option<(OverlapSiteTensor, usize)> {
    let (left_dim, cursor) = read_u32_le(payload, offset)?;
    let (right_dim, cursor) = read_u32_le(payload, cursor)?;
    let (value_count, mut cursor) = read_u32_le(payload, cursor)?;
    let left = left_dim as usize;
    let right = right_dim as usize;
    if left == 0 || right == 0 || left > OVERLAP_MAX_BOND || right > OVERLAP_MAX_BOND {
        return None;
    }
    let expected = left.checked_mul(2)?.checked_mul(right)?;
    if value_count as usize != expected {
        return None;
    }
    // Each complex pair is 16 bytes (re f64 + im f64).
    let need = (value_count as usize).checked_mul(16)?;
    if payload.len().saturating_sub(cursor) < need {
        return None;
    }
    let mut values = Vec::with_capacity(value_count as usize);
    for _ in 0..value_count {
        let (re, next) = read_f64_le(payload, cursor)?;
        let (im, next) = read_f64_le(payload, next)?;
        values.push((re, im));
        cursor = next;
    }
    Some((
        OverlapSiteTensor {
            left_dim,
            right_dim,
            values,
        },
        cursor,
    ))
}

/// Encodes an overlap segment payload (no marker / length prefix).
pub fn encode_overlap_segment(segment: &OverlapSegment) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(&segment.qubit_count.to_le_bytes());
    out.extend_from_slice(&segment.amplitude_re.to_le_bytes());
    out.extend_from_slice(&segment.amplitude_im.to_le_bytes());
    append_cstr(&mut out, &segment.amplitude_digest);
    out.extend_from_slice(&(segment.ket_sites.len() as u32).to_le_bytes());
    for site in &segment.ket_sites {
        encode_site(&mut out, site);
    }
    out.extend_from_slice(&(segment.bra_sites.len() as u32).to_le_bytes());
    for site in &segment.bra_sites {
        encode_site(&mut out, site);
    }
    out
}

/// Decodes an overlap segment payload.
pub fn decode_overlap_segment(proof: &[u8], offset: usize) -> Option<(OverlapSegment, usize)> {
    let (qubit_count, cursor) = read_u32_le(proof, offset)?;
    if qubit_count == 0 || qubit_count as usize > OVERLAP_MAX_QUBITS {
        return None;
    }
    let (amplitude_re, cursor) = read_f64_le(proof, cursor)?;
    let (amplitude_im, cursor) = read_f64_le(proof, cursor)?;
    let (amplitude_digest, cursor) = read_cstr(proof, cursor)?;
    let (ket_count, mut cursor) = read_u32_le(proof, cursor)?;
    if ket_count != qubit_count {
        return None;
    }
    let mut ket_sites = Vec::with_capacity(ket_count as usize);
    for _ in 0..ket_count {
        let (site, next) = decode_site(proof, cursor)?;
        ket_sites.push(site);
        cursor = next;
    }
    let (bra_count, mut cursor) = read_u32_le(proof, cursor)?;
    if bra_count != qubit_count {
        return None;
    }
    let mut bra_sites = Vec::with_capacity(bra_count as usize);
    for _ in 0..bra_count {
        let (site, next) = decode_site(proof, cursor)?;
        bra_sites.push(site);
        cursor = next;
    }
    Some((
        OverlapSegment {
            qubit_count,
            amplitude_re,
            amplitude_im,
            amplitude_digest,
            ket_sites,
            bra_sites,
        },
        cursor,
    ))
}

fn find_overlap_tail_marker(proof: &[u8]) -> Option<usize> {
    proof
        .windows(OVERLAP_V1_MARKER.len())
        .rposition(|w| w == OVERLAP_V1_MARKER)
}

/// Appends an overlap tail to a STARK transcript.
pub fn append_overlap_tail(mut proof: Vec<u8>, segment: &OverlapSegment) -> Vec<u8> {
    let payload = encode_overlap_segment(segment);
    proof.extend_from_slice(OVERLAP_V1_MARKER);
    proof.extend_from_slice(&(payload.len() as u32).to_le_bytes());
    proof.extend_from_slice(&payload);
    proof
}

/// Splits a proof into the base body and optional overlap tail.
pub fn split_overlap_tail(proof: &[u8]) -> Option<ProofTailSplit<'_>> {
    let pos = find_overlap_tail_marker(proof)?;
    let base = &proof[..pos];
    let cursor = pos + OVERLAP_V1_MARKER.len();
    let (len, cursor) = read_u32_le(proof, cursor)?;
    let end = cursor + len as usize;
    let payload = proof.get(cursor..end)?;
    Some((base, Some((payload, OVERLAP_V1_MARKER))))
}

pub fn has_overlap_tail(proof: &[u8]) -> bool {
    find_overlap_tail_marker(proof).is_some()
}

/// Structural + AIR failure reason without printing.
pub fn overlap_segment_error(segment: &OverlapSegment) -> Option<String> {
    if segment.amplitude_digest.is_empty() {
        return Some("overlap amplitude_digest is empty".into());
    }
    let recomputed = calculate_amplitude_digest(segment.amplitude_re, segment.amplitude_im);
    if recomputed != segment.amplitude_digest {
        return Some(format!(
            "overlap amplitude_digest mismatch (claimed {}, recomputed {})",
            segment.amplitude_digest, recomputed
        ));
    }
    if let Some((_, message)) = overlap_constraint_failure(segment) {
        return Some(format!("overlap AIR constraint violation: {message}"));
    }
    None
}

pub fn verify_overlap_segment(segment: &OverlapSegment) -> bool {
    match overlap_segment_error(segment) {
        None => true,
        Some(reason) => {
            eprintln!("[STARK Core] Failed: {reason}");
            false
        }
    }
}

/// Decodes and verifies an overlap tail payload (post-marker bytes).
pub fn try_decode_and_verify_overlap_tail(
    payload: &[u8],
    marker: &[u8],
) -> Result<OverlapSegment, String> {
    if marker != OVERLAP_V1_MARKER {
        let reason = "unknown overlap marker".to_string();
        eprintln!("[STARK Core] Failed: {reason}");
        return Err(reason);
    }
    let Some((segment, end)) = decode_overlap_segment(payload, 0) else {
        let reason = "malformed overlap segment".to_string();
        eprintln!("[STARK Core] Failed: {reason}");
        return Err(reason);
    };
    if end != payload.len() {
        let reason = "overlap segment length mismatch".to_string();
        eprintln!("[STARK Core] Failed: {reason}");
        return Err(reason);
    }
    if let Some(reason) = overlap_segment_error(&segment) {
        eprintln!("[STARK Core] Failed: {reason}");
        return Err(reason);
    }
    if evaluate_overlap_constraint_sum(&segment) != 0 {
        let reason = "overlap AIR constraint violation".to_string();
        eprintln!("[STARK Core] Failed: {reason}");
        return Err(reason);
    }
    Ok(segment)
}

pub fn decode_and_verify_overlap_tail(payload: &[u8], marker: &[u8]) -> Option<OverlapSegment> {
    try_decode_and_verify_overlap_tail(payload, marker).ok()
}

/// Verifies overlap tail presence and binding to the expected `output_result_hash`.
pub fn verify_overlap_binding(proof: &[u8], expected_output_hash: &str) -> bool {
    if expected_output_hash.is_empty() {
        eprintln!("[STARK Core] Failed: overlap binding requires output_result_hash");
        return false;
    }
    let Some((_, Some((payload, marker)))) = split_overlap_tail(proof) else {
        eprintln!("[STARK Core] Failed: missing overlap tail");
        return false;
    };
    let segment = match decode_and_verify_overlap_tail(payload, marker) {
        Some(seg) => seg,
        None => {
            eprintln!("[STARK Core] Failed: invalid overlap segment");
            return false;
        }
    };
    if segment.amplitude_digest != expected_output_hash {
        eprintln!("[STARK Core] Failed: overlap amplitude_digest != output_result_hash");
        return false;
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bond1_identity_segment() -> OverlapSegment {
        let site = OverlapSiteTensor {
            left_dim: 1,
            right_dim: 1,
            values: vec![(1.0, 0.0), (0.0, 0.0)],
        };
        OverlapSegment {
            qubit_count: 1,
            amplitude_re: 1.0,
            amplitude_im: 0.0,
            amplitude_digest: calculate_amplitude_digest(1.0, 0.0),
            ket_sites: vec![site.clone()],
            bra_sites: vec![site],
        }
    }

    fn bond1_two_site_product() -> OverlapSegment {
        let site = OverlapSiteTensor {
            left_dim: 1,
            right_dim: 1,
            values: vec![(1.0, 0.0), (0.0, 0.0)],
        };
        OverlapSegment {
            qubit_count: 2,
            amplitude_re: 1.0,
            amplitude_im: 0.0,
            amplitude_digest: calculate_amplitude_digest(1.0, 0.0),
            ket_sites: vec![site.clone(), site.clone()],
            bra_sites: vec![site.clone(), site],
        }
    }

    #[test]
    fn segment_roundtrip_and_tail_split() {
        let segment = bond1_identity_segment();
        let base = b"fake-stark-body";
        let proof = append_overlap_tail(base.to_vec(), &segment);
        let (decoded_base, tail) = split_overlap_tail(&proof).expect("split");
        assert_eq!(decoded_base, base);
        let (payload, marker) = tail.expect("tail");
        assert_eq!(marker, OVERLAP_V1_MARKER);
        let decoded = decode_and_verify_overlap_tail(payload, marker).expect("decode");
        assert_eq!(decoded, segment);
    }

    #[test]
    fn bond1_one_and_two_sites_verify() {
        assert!(verify_overlap_segment(&bond1_identity_segment()));
        assert!(verify_overlap_segment(&bond1_two_site_product()));
    }

    #[test]
    fn verify_overlap_binding_roundtrip() {
        let segment = bond1_identity_segment();
        let proof = append_overlap_tail(b"stark".to_vec(), &segment);
        assert!(verify_overlap_binding(&proof, &segment.amplitude_digest));
    }

    #[test]
    fn tampered_amplitude_rejected() {
        let mut segment = bond1_identity_segment();
        segment.amplitude_re = 0.5;
        segment.amplitude_digest = calculate_amplitude_digest(0.5, 0.0);
        assert!(!verify_overlap_segment(&segment));
    }

    #[test]
    fn digest_mismatch_rejected() {
        let mut segment = bond1_identity_segment();
        segment.amplitude_digest = "deadbeef".into();
        assert!(!verify_overlap_segment(&segment));
    }

    #[test]
    fn decode_rejects_huge_value_count_without_allocating() {
        // left=1, right=1, but value_count = u32::MAX → would ask for ~64 GiB if trusted.
        let mut payload = Vec::new();
        payload.extend_from_slice(&1u32.to_le_bytes()); // qubit_count
        payload.extend_from_slice(&1.0f64.to_le_bytes());
        payload.extend_from_slice(&0.0f64.to_le_bytes());
        payload.extend_from_slice(b"dead\0");
        payload.extend_from_slice(&1u32.to_le_bytes()); // ket_count
        payload.extend_from_slice(&1u32.to_le_bytes()); // left
        payload.extend_from_slice(&1u32.to_le_bytes()); // right
        payload.extend_from_slice(&u32::MAX.to_le_bytes()); // value_count
        assert!(decode_overlap_segment(&payload, 0).is_none());
    }

    #[test]
    fn decode_rejects_huge_ket_count_without_allocating() {
        let mut payload = Vec::new();
        payload.extend_from_slice(&1u32.to_le_bytes()); // qubit_count
        payload.extend_from_slice(&1.0f64.to_le_bytes());
        payload.extend_from_slice(&0.0f64.to_le_bytes());
        payload.extend_from_slice(b"dead\0");
        payload.extend_from_slice(&u32::MAX.to_le_bytes()); // ket_count ≠ qubit_count
        assert!(decode_overlap_segment(&payload, 0).is_none());
    }
}

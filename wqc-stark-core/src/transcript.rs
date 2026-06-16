//! Proof transcript encoding/decoding (v1: embedded execution trace + AIR digest).

use p3_field::PrimeField32;

use crate::air::{boundary_from_matrix, evaluate_air_sum, trace_to_air_matrix};
use crate::trace_spec::TRACE_WIDTH;

/// V1 marker separating `sub_task_id` from bound metadata.
pub const V1_MARKER: &[u8] = b"_M31_QUANTUM_AIR_V1_";

/// Future Plonky3 uni-STARK proofs will use this marker (Phase 3).
pub const V2_MARKER: &[u8] = b"_M31_PLONKY3_STARK_V2_";

/// Legacy devnet marker (pre-Phase 1; no embedded trace).
pub const LEGACY_MARKER: &[u8] = b"_M31_QUANTUM_AIR_STARK_";

pub struct StarkContext<'a> {
    pub circuit_id: &'a str,
    pub sub_task_id: &'a str,
    pub node_id: &'a str,
    pub slice_id: &'a str,
    pub output_hash: &'a str,
}

fn append_public_input_binding(proof: &mut Vec<u8>, context: &StarkContext<'_>) {
    for field in [
        context.circuit_id,
        context.node_id,
        context.slice_id,
        context.output_hash,
    ] {
        proof.extend_from_slice(field.as_bytes());
        proof.push(0);
    }
}

fn read_cstr_field(proof: &[u8], offset: usize) -> Option<(&str, usize)> {
    let tail = proof.get(offset..)?;
    let end_rel = tail.iter().position(|&b| b == 0)?;
    let end = offset + end_rel;
    let value = std::str::from_utf8(&proof[offset..end]).ok()?;
    Some((value, end + 1))
}

pub(crate) fn verify_public_input_binding(
    proof: &[u8],
    offset: usize,
    context: &StarkContext<'_>,
) -> Option<usize> {
    let mut cursor = offset;
    for expected in [
        context.circuit_id,
        context.node_id,
        context.slice_id,
        context.output_hash,
    ] {
        let (parsed, next) = read_cstr_field(proof, cursor)?;
        if parsed != expected {
            eprintln!(
                "[STARK Core] Failed: public input binding mismatch (expected '{}', got '{}')",
                expected, parsed
            );
            return None;
        }
        cursor = next;
    }
    Some(cursor)
}

fn read_u32_le(proof: &[u8], offset: usize) -> Option<(u32, usize)> {
    let bytes = proof.get(offset..offset + 4)?;
    let mut buf = [0u8; 4];
    buf.copy_from_slice(bytes);
    Some((u32::from_le_bytes(buf), offset + 4))
}

fn trace_f64_bytes(trace: &[f64]) -> Vec<u8> {
    let mut out = Vec::with_capacity(trace.len() * 8);
    for value in trace {
        out.extend_from_slice(&value.to_le_bytes());
    }
    out
}

fn parse_trace_f64_bytes(bytes: &[u8]) -> Option<Vec<f64>> {
    if !bytes.len().is_multiple_of(8) {
        return None;
    }
    let mut trace = Vec::with_capacity(bytes.len() / 8);
    for chunk in bytes.chunks_exact(8) {
        let mut buf = [0u8; 8];
        buf.copy_from_slice(chunk);
        trace.push(f64::from_le_bytes(buf));
    }
    Some(trace)
}

/// Encodes a v1 proof transcript with embedded execution trace.
pub fn encode_proof_v1(
    context: &StarkContext<'_>,
    execution_trace: &[f64],
    air_sum: u32,
    boundary: [u32; 4],
) -> Vec<u8> {
    let mut proof_bytes = Vec::new();
    proof_bytes.extend_from_slice(context.sub_task_id.as_bytes());
    proof_bytes.extend_from_slice(V1_MARKER);
    append_public_input_binding(&mut proof_bytes, context);

    let trace_len = (execution_trace.len() / TRACE_WIDTH) as u32;
    proof_bytes.extend_from_slice(&trace_len.to_le_bytes());
    proof_bytes.extend_from_slice(&trace_f64_bytes(execution_trace));
    proof_bytes.extend_from_slice(&air_sum.to_le_bytes());
    for amp in boundary {
        proof_bytes.extend_from_slice(&amp.to_le_bytes());
    }
    proof_bytes
}

/// Locates a known marker after the `sub_task_id` prefix.
pub fn find_marker(proof: &[u8], sub_task_id: &str) -> Option<(usize, &'static [u8])> {
    let prefix_len = sub_task_id.len();
    let tail = proof.get(prefix_len..)?;
    for marker in [V1_MARKER, V2_MARKER, LEGACY_MARKER] {
        if tail.starts_with(marker) {
            return Some((prefix_len, marker));
        }
    }
    None
}

/// Decodes a v1 proof payload after public-input binding.
pub(crate) fn decode_proof_v1_payload(proof: &[u8], offset: usize) -> Option<(Vec<f64>, u32, [u32; 4], usize)> {
    let (trace_row_count, offset) = read_u32_le(proof, offset)?;
    let trace_float_count = trace_row_count as usize * TRACE_WIDTH;
    let trace_byte_len = trace_float_count * 8;
    let trace_bytes = proof.get(offset..offset + trace_byte_len)?;
    let trace = parse_trace_f64_bytes(trace_bytes)?;
    let offset = offset + trace_byte_len;

    let (air_sum, mut offset) = read_u32_le(proof, offset)?;
    let mut boundary = [0u32; 4];
    for item in &mut boundary {
        (*item, offset) = read_u32_le(proof, offset)?;
    }
    Some((trace, air_sum, boundary, offset))
}

/// Owned v1 decode for tests and internal verification.
pub fn decode_proof_v1_owned(
    proof: &[u8],
    context: &StarkContext<'_>,
) -> Option<(Vec<f64>, u32, [u32; 4])> {
    let (marker_index, marker) = find_marker(proof, context.sub_task_id)?;
    if marker != V1_MARKER {
        return None;
    }
    let binding_start = marker_index + V1_MARKER.len();
    let payload_start = verify_public_input_binding(proof, binding_start, context)?;
    let (trace, air_sum, boundary, end) = decode_proof_v1_payload(proof, payload_start)?;
    if end != proof.len() {
        return None;
    }
    Some((trace, air_sum, boundary))
}

/// Recomputes AIR sum and boundary from an execution trace; used by prover and verifier.
pub fn air_digest_from_trace(execution_trace: &[f64]) -> Option<(u32, [u32; 4])> {
    let matrix = trace_to_air_matrix(execution_trace)?;
    let sum = evaluate_air_sum(&matrix);
    let boundary = boundary_from_matrix(&matrix)?;
    Some((sum.as_canonical_u32(), boundary))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_context() -> StarkContext<'static> {
        StarkContext {
            circuit_id: "circuit-a",
            sub_task_id: "task-1",
            node_id: "node-1",
            slice_id: "0",
            output_hash: "hash-abc",
        }
    }

    #[test]
    fn v1_roundtrip_preserves_trace_and_digest() {
        let context = sample_context();
        let trace = vec![
            4.0, 0.0, 0.0, 1.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0,
            0.0, 0.0, 0.0, 1.0, 0.0, 0.70710678, 0.0, 0.70710678, 0.0, 0.0,
        ];
        let (air_sum, boundary) = air_digest_from_trace(&trace).expect("digest");

        let proof = encode_proof_v1(&context, &trace, air_sum, boundary);
        let (decoded_trace, decoded_sum, decoded_boundary) =
            decode_proof_v1_owned(&proof, &context).expect("decode");

        assert_eq!(decoded_trace, trace);
        assert_eq!(decoded_sum, air_sum);
        assert_eq!(decoded_boundary, boundary);
    }

    #[test]
    fn decode_fails_on_mismatched_public_inputs() {
        let context = sample_context();
        let trace = vec![
            4.0, 0.0, 0.0, 1.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0,
            0.0, 0.0, 0.0, 1.0, 0.0, 0.70710678, 0.0, 0.70710678, 0.0, 0.0,
        ];
        let (air_sum, boundary) = air_digest_from_trace(&trace).expect("digest");

        let proof = encode_proof_v1(&context, &trace, air_sum, boundary);

        // Changing the slice_id should cause decoding to fail due to a public input binding mismatch.
        let bad_context = StarkContext {
            circuit_id: context.circuit_id,
            sub_task_id: context.sub_task_id,
            node_id: context.node_id,
            slice_id: "1", // mismatch
            output_hash: context.output_hash,
        };

        let decoded = decode_proof_v1_owned(&proof, &bad_context);
        assert!(decoded.is_none(), "decode should fail on mismatched public inputs");
    }

    #[test]
    fn decode_fails_on_truncated_payload() {
        let context = sample_context();
        let trace = vec![
            4.0, 0.0, 0.0, 1.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0,
            0.0, 0.0, 0.0, 1.0, 0.0, 0.70710678, 0.0, 0.70710678, 0.0, 0.0,
        ];
        let (air_sum, boundary) = air_digest_from_trace(&trace).expect("digest");

        let mut proof = encode_proof_v1(&context, &trace, air_sum, boundary);
        // Truncate the trace bytes to break the proof.
        proof.truncate(proof.len().saturating_sub(8));

        let decoded = decode_proof_v1_owned(&proof, &context);
        assert!(decoded.is_none(), "decode should fail on truncated payload");
    }
}

//! v2 proof transcript helpers (Plonky3 payload).

use crate::transcript::{StarkContext, V2_MARKER, verify_public_input_binding};

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
    if !context.terminal_statevector_digest.is_empty() {
        proof.extend_from_slice(context.terminal_statevector_digest.as_bytes());
        proof.push(0);
    }
}

fn read_u32_le(proof: &[u8], offset: usize) -> Option<(u32, usize)> {
    let bytes = proof.get(offset..offset + 4)?;
    let mut buf = [0u8; 4];
    buf.copy_from_slice(bytes);
    Some((u32::from_le_bytes(buf), offset + 4))
}

/// Encodes a v2 transcript: public-input binding + postcard Plonky3 proof bytes.
pub fn encode_proof_v2(context: &StarkContext<'_>, plonky3_bytes: &[u8]) -> Vec<u8> {
    let mut proof_bytes = Vec::new();
    proof_bytes.extend_from_slice(context.sub_task_id.as_bytes());
    proof_bytes.extend_from_slice(V2_MARKER);
    append_public_input_binding(&mut proof_bytes, context);
    proof_bytes.extend_from_slice(&(plonky3_bytes.len() as u32).to_le_bytes());
    proof_bytes.extend_from_slice(plonky3_bytes);
    proof_bytes
}

/// Decodes the Plonky3 payload from a v2 transcript after public-input binding.
pub fn decode_proof_v2_payload(proof: &[u8], offset: usize) -> Option<(Vec<u8>, usize)> {
    let (len, offset) = read_u32_le(proof, offset)?;
    let end = offset + len as usize;
    let payload = proof.get(offset..end)?.to_vec();
    Some((payload, end))
}

/// Owned decode of a v2 proof body (allows trailing distribution tail).
pub fn decode_proof_v2_plonky3_bytes(proof: &[u8], context: &StarkContext<'_>) -> Option<Vec<u8>> {
    if !proof.starts_with(context.sub_task_id.as_bytes()) {
        return None;
    }
    let prefix_len = context.sub_task_id.len();
    if !proof[prefix_len..].starts_with(V2_MARKER) {
        return None;
    }
    let binding_start = prefix_len + V2_MARKER.len();
    let payload_start = verify_public_input_binding(proof, binding_start, context)?;
    let (payload, _end) = decode_proof_v2_payload(proof, payload_start)?;
    Some(payload)
}

/// Owned decode of a v2 proof (entire transcript must be only v2 body).
pub fn decode_proof_v2_owned(proof: &[u8], context: &StarkContext<'_>) -> Option<Vec<u8>> {
    let base = crate::distribution::base_proof_without_distribution_tail(proof);
    let payload = decode_proof_v2_plonky3_bytes(base, context)?;
    if base.len() != proof.len() {
        return None;
    }
    Some(payload)
}

//! V5 recursive aggregation transcript (R3-M1).

use crate::aggregation::CHILD_HASH_LEN;

use super::air::REC_KIND_AGG;
use super::context::RecursiveAggregationContext;
use super::STARK_DIGEST_LEN;

pub const V5_REC_AGG_INNER_MARKER: &[u8] = b"_WQC_REC_AGG_V5_";
pub const V5_REC_TAIL_MARKER: &[u8] = b"_WQC_REC_TAIL_V5_";

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

fn read_fixed<const N: usize>(proof: &[u8], offset: usize) -> Option<([u8; N], usize)> {
    let bytes = proof.get(offset..offset + N)?;
    let mut out = [0u8; N];
    out.copy_from_slice(bytes);
    Some((out, offset + N))
}

fn locate_inner_marker(proof: &[u8]) -> Option<usize> {
    let pos = proof
        .windows(V5_REC_AGG_INNER_MARKER.len())
        .position(|w| w == V5_REC_AGG_INNER_MARKER)?;
    let prefix = &proof[..pos];
    if prefix.is_empty() || prefix.last() != Some(&0) {
        return None;
    }
    Some(pos)
}

pub fn encode_rec_agg_proof(
    context: &RecursiveAggregationContext<'_>,
    plonky3_bytes: &[u8],
) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(context.parent_task_id.as_bytes());
    out.push(0);
    out.extend_from_slice(V5_REC_AGG_INNER_MARKER);
    out.extend_from_slice(context.compose_label.as_bytes());
    out.push(0);
    out.extend_from_slice(context.manifest_root_hash.as_bytes());
    out.push(0);
    out.extend_from_slice(&context.left_child_hash);
    out.extend_from_slice(&context.right_child_hash);
    out.extend_from_slice(&context.left_stark_digest);
    out.extend_from_slice(&context.right_stark_digest);
    out.push(context.left_kind);
    out.push(context.right_kind);
    out.extend_from_slice(&(plonky3_bytes.len() as u32).to_le_bytes());
    out.extend_from_slice(plonky3_bytes);
    out
}

pub fn decode_rec_agg_proof_owned(
    proof: &[u8],
    expected: &RecursiveAggregationContext<'_>,
) -> Option<Vec<u8>> {
    if !proof.starts_with(expected.parent_task_id.as_bytes()) {
        return None;
    }
    let marker_pos = locate_inner_marker(proof)?;
    let parent_end = marker_pos.saturating_sub(1);
    let parent_task_id = std::str::from_utf8(&proof[..parent_end]).ok()?;
    if parent_task_id != expected.parent_task_id {
        return None;
    }

    let cursor = marker_pos + V5_REC_AGG_INNER_MARKER.len();
    let (compose_label, cursor) = read_cstr(proof, cursor)?;
    let (manifest_root_hash, cursor) = read_cstr(proof, cursor)?;
    let (left_hash, cursor) = read_fixed::<{ CHILD_HASH_LEN }>(proof, cursor)?;
    let (right_hash, cursor) = read_fixed::<{ CHILD_HASH_LEN }>(proof, cursor)?;
    let (left_stark, cursor) = read_fixed::<{ STARK_DIGEST_LEN }>(proof, cursor)?;
    let (right_stark, cursor) = read_fixed::<{ STARK_DIGEST_LEN }>(proof, cursor)?;
    let left_kind = *proof.get(cursor)?;
    let right_kind = *proof.get(cursor + 1)?;
    let cursor = cursor + 2;

    if compose_label != expected.compose_label
        || manifest_root_hash != expected.manifest_root_hash
        || left_hash != expected.left_child_hash
        || right_hash != expected.right_child_hash
        || left_stark != expected.left_stark_digest
        || right_stark != expected.right_stark_digest
        || left_kind != expected.left_kind
        || right_kind != expected.right_kind
    {
        return None;
    }
    if left_kind > REC_KIND_AGG || right_kind > REC_KIND_AGG {
        return None;
    }

    let (len, cursor) = read_u32_le(proof, cursor)?;
    let end = cursor + len as usize;
    let payload = proof.get(cursor..end)?.to_vec();
    if end != proof.len() {
        return None;
    }
    Some(payload)
}

pub fn append_rec_tail(mut body: Vec<u8>, rec_proof: &[u8]) -> Vec<u8> {
    body.extend_from_slice(V5_REC_TAIL_MARKER);
    body.extend_from_slice(&(rec_proof.len() as u32).to_le_bytes());
    body.extend_from_slice(rec_proof);
    body
}

pub fn split_rec_tail(proof: &[u8]) -> Option<(&[u8], &[u8])> {
    let pos = proof
        .windows(V5_REC_TAIL_MARKER.len())
        .rposition(|w| w == V5_REC_TAIL_MARKER)?;
    let body = &proof[..pos];
    let cursor = pos + V5_REC_TAIL_MARKER.len();
    let (len, cursor) = read_u32_le(proof, cursor)?;
    let end = cursor + len as usize;
    let rec = proof.get(cursor..end)?;
    if end != proof.len() {
        return None;
    }
    Some((body, rec))
}

pub fn has_rec_tail(proof: &[u8]) -> bool {
    proof
        .windows(V5_REC_TAIL_MARKER.len())
        .any(|w| w == V5_REC_TAIL_MARKER)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rec_tail_roundtrip() {
        let body = b"v3-bytes";
        let rec = b"rec-proof";
        let combined = append_rec_tail(body.to_vec(), rec);
        let (left, right) = split_rec_tail(&combined).expect("split");
        assert_eq!(left, body);
        assert_eq!(right, rec);
        assert!(has_rec_tail(&combined));
    }
}

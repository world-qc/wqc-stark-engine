//! v4 aggregation STARK transcript (R2).

use crate::aggregation::CHILD_HASH_LEN;

use super::aggregation::AggregationContext;

pub const V4_AGG_INNER_MARKER: &[u8] = b"_WQC_AGG_STARK_V4_";
pub const V4_AGG_TAIL_MARKER: &[u8] = b"_WQC_AGG_TAIL_V4_";

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
        .windows(V4_AGG_INNER_MARKER.len())
        .position(|w| w == V4_AGG_INNER_MARKER)?;
    let prefix = &proof[..pos];
    if prefix.is_empty() || prefix.last() != Some(&0) {
        return None;
    }
    Some(pos)
}

/// Encodes an aggregation STARK payload bound to compose metadata and child digests.
pub fn encode_agg_proof(context: &AggregationContext<'_>, plonky3_bytes: &[u8]) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(context.parent_task_id.as_bytes());
    out.push(0);
    out.extend_from_slice(V4_AGG_INNER_MARKER);
    out.extend_from_slice(context.compose_label.as_bytes());
    out.push(0);
    out.extend_from_slice(context.manifest_root_hash.as_bytes());
    out.push(0);
    out.extend_from_slice(&context.left_child_hash);
    out.extend_from_slice(&context.right_child_hash);
    out.extend_from_slice(&(plonky3_bytes.len() as u32).to_le_bytes());
    out.extend_from_slice(plonky3_bytes);
    out
}

/// Decodes the Plonky3 payload from a v4 aggregation transcript.
pub fn decode_agg_proof_owned(proof: &[u8], expected: &AggregationContext<'_>) -> Option<Vec<u8>> {
    if !proof.starts_with(expected.parent_task_id.as_bytes()) {
        return None;
    }
    let marker_pos = locate_inner_marker(proof)?;
    let parent_end = marker_pos.saturating_sub(1);
    let parent_task_id = std::str::from_utf8(&proof[..parent_end]).ok()?;
    if parent_task_id != expected.parent_task_id {
        return None;
    }

    let cursor = marker_pos + V4_AGG_INNER_MARKER.len();
    let (compose_label, cursor) = read_cstr(proof, cursor)?;
    let (manifest_root_hash, cursor) = read_cstr(proof, cursor)?;
    let (left_hash, cursor) = read_fixed::<{ CHILD_HASH_LEN }>(proof, cursor)?;
    let (right_hash, cursor) = read_fixed::<{ CHILD_HASH_LEN }>(proof, cursor)?;

    if compose_label != expected.compose_label {
        return None;
    }
    if manifest_root_hash != expected.manifest_root_hash {
        return None;
    }
    if left_hash != expected.left_child_hash || right_hash != expected.right_child_hash {
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

/// Appends an aggregation STARK tail to a v3 compose transcript.
pub fn append_agg_tail(mut v3_compose: Vec<u8>, agg_proof: &[u8]) -> Vec<u8> {
    v3_compose.extend_from_slice(V4_AGG_TAIL_MARKER);
    v3_compose.extend_from_slice(&(agg_proof.len() as u32).to_le_bytes());
    v3_compose.extend_from_slice(agg_proof);
    v3_compose
}

/// Splits a v3 compose transcript and optional v4 aggregation tail.
pub fn split_agg_tail(proof: &[u8]) -> Option<(&[u8], &[u8])> {
    let pos = proof
        .windows(V4_AGG_TAIL_MARKER.len())
        .rposition(|w| w == V4_AGG_TAIL_MARKER)?;
    let v3 = &proof[..pos];
    let cursor = pos + V4_AGG_TAIL_MARKER.len();
    let (len, cursor) = read_u32_le(proof, cursor)?;
    let end = cursor + len as usize;
    let agg = proof.get(cursor..end)?;
    if end != proof.len() {
        return None;
    }
    Some((v3, agg))
}

pub fn has_agg_tail(proof: &[u8]) -> bool {
    proof
        .windows(V4_AGG_TAIL_MARKER.len())
        .any(|w| w == V4_AGG_TAIL_MARKER)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn agg_tail_roundtrip() {
        let v3 = b"v3-bytes";
        let agg = b"agg-proof";
        let combined = append_agg_tail(v3.to_vec(), agg);
        let (left, right) = split_agg_tail(&combined).expect("split");
        assert_eq!(left, v3);
        assert_eq!(right, agg);
        assert!(has_agg_tail(&combined));
    }
}

//! C2b Born-rule Plonky3 STARK tail transcript.

use super::distribution_stark::BornStarkContext;

pub const BORN_STARK_INNER_MARKER: &[u8] = b"_M31_BORN_STARK_V1_";
pub const BORN_STARK_TAIL_MARKER: &[u8] = b"_M31_BORN_TAIL_V1_";

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

/// Encodes a Born STARK inner payload bound to `probability_digest`.
pub fn encode_born_stark(context: &BornStarkContext<'_>, plonky3_bytes: &[u8]) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(context.sub_task_id.as_bytes());
    out.push(0);
    out.extend_from_slice(BORN_STARK_INNER_MARKER);
    out.extend_from_slice(context.probability_digest.as_bytes());
    out.push(0);
    out.extend_from_slice(&(plonky3_bytes.len() as u32).to_le_bytes());
    out.extend_from_slice(plonky3_bytes);
    out
}

/// Decodes the Plonky3 payload from a Born STARK inner transcript.
pub fn decode_born_stark_owned(
    proof: &[u8],
    expected: &BornStarkContext<'_>,
) -> Option<Vec<u8>> {
    if !proof.starts_with(expected.sub_task_id.as_bytes()) {
        return None;
    }
    let marker_pos = proof
        .windows(BORN_STARK_INNER_MARKER.len())
        .position(|w| w == BORN_STARK_INNER_MARKER)?;
    let sub_end = marker_pos.saturating_sub(1);
    let sub_task_id = std::str::from_utf8(&proof[..sub_end]).ok()?;
    if sub_task_id != expected.sub_task_id {
        return None;
    }

    let cursor = marker_pos + BORN_STARK_INNER_MARKER.len();
    let (probability_digest, cursor) = read_cstr(proof, cursor)?;
    if probability_digest != expected.probability_digest {
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

/// Appends a length-prefixed Born STARK tail after the distribution segment.
pub fn append_born_stark_tail(mut proof: Vec<u8>, born_proof: &[u8]) -> Vec<u8> {
    proof.extend_from_slice(BORN_STARK_TAIL_MARKER);
    proof.extend_from_slice(&(born_proof.len() as u32).to_le_bytes());
    proof.extend_from_slice(born_proof);
    proof
}

/// Splits the Born STARK inner transcript from a full proof tail wrapper.
pub fn split_born_stark_tail(proof: &[u8]) -> Option<&[u8]> {
    let pos = proof
        .windows(BORN_STARK_TAIL_MARKER.len())
        .rposition(|w| w == BORN_STARK_TAIL_MARKER)?;
    let cursor = pos + BORN_STARK_TAIL_MARKER.len();
    let (len, cursor) = read_u32_le(proof, cursor)?;
    let end = cursor + len as usize;
    proof.get(cursor..end)
}

pub fn has_born_stark_tail(proof: &[u8]) -> bool {
    proof
        .windows(BORN_STARK_TAIL_MARKER.len())
        .any(|w| w == BORN_STARK_TAIL_MARKER)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn born_stark_transcript_roundtrip() {
        let ctx = BornStarkContext {
            sub_task_id: "sub-1",
            probability_digest: "abc123digest",
        };
        let payload = b"plonky3-bytes";
        let encoded = encode_born_stark(&ctx, payload);
        let decoded = decode_born_stark_owned(&encoded, &ctx).expect("decode");
        assert_eq!(decoded, payload);
    }

    #[test]
    fn born_stark_tail_wrapper_roundtrip() {
        let ctx = BornStarkContext {
            sub_task_id: "sub-1",
            probability_digest: "abc123digest",
        };
        let inner = encode_born_stark(&ctx, b"plonky3");
        let wrapped = append_born_stark_tail(b"base-proof".to_vec(), &inner);
        assert!(has_born_stark_tail(&wrapped));
        let extracted = split_born_stark_tail(&wrapped).expect("split");
        assert_eq!(extracted, inner.as_slice());
    }
}

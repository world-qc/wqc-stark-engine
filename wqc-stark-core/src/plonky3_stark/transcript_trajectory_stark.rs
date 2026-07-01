//! C2c trajectory marginal Plonky3 STARK tail transcript.

pub const TRAJ_MARG_STARK_INNER_MARKER: &[u8] = b"_M31_TRAJ_MARG_STARK_INNER_V1_";
pub const TRAJ_STARK_TAIL_MARKER: &[u8] = b"_M31_TRAJ_STARK_V1_";

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

/// Public binding for one trajectory marginal STARK inner transcript.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TrajectoryMarginalStarkContext<'a> {
    pub sub_task_id: &'a str,
    pub trajectory_digest: &'a str,
    pub witness_digest: &'a str,
    pub unitary_link_digest: &'a str,
}

/// Encodes one marginal zk proof bound to trajectory + witness digests.
pub fn encode_trajectory_marginal_stark(
    context: &TrajectoryMarginalStarkContext<'_>,
    plonky3_bytes: &[u8],
) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(context.sub_task_id.as_bytes());
    out.push(0);
    out.extend_from_slice(TRAJ_MARG_STARK_INNER_MARKER);
    out.extend_from_slice(context.trajectory_digest.as_bytes());
    out.push(0);
    out.extend_from_slice(context.witness_digest.as_bytes());
    out.push(0);
    out.extend_from_slice(context.unitary_link_digest.as_bytes());
    out.push(0);
    out.extend_from_slice(&(plonky3_bytes.len() as u32).to_le_bytes());
    out.extend_from_slice(plonky3_bytes);
    out
}

pub fn decode_trajectory_marginal_stark_owned(
    proof: &[u8],
    expected: &TrajectoryMarginalStarkContext<'_>,
) -> Option<Vec<u8>> {
    if !proof.starts_with(expected.sub_task_id.as_bytes()) {
        return None;
    }
    let marker_pos = proof
        .windows(TRAJ_MARG_STARK_INNER_MARKER.len())
        .position(|w| w == TRAJ_MARG_STARK_INNER_MARKER)?;
    let sub_end = marker_pos.saturating_sub(1);
    let sub_task_id = std::str::from_utf8(&proof[..sub_end]).ok()?;
    if sub_task_id != expected.sub_task_id {
        return None;
    }

    let cursor = marker_pos + TRAJ_MARG_STARK_INNER_MARKER.len();
    let (trajectory_digest, cursor) = read_cstr(proof, cursor)?;
    if trajectory_digest != expected.trajectory_digest {
        return None;
    }
    let (witness_digest, cursor) = read_cstr(proof, cursor)?;
    if witness_digest != expected.witness_digest {
        return None;
    }
    let (unitary_link_digest, cursor) = read_cstr(proof, cursor)?;
    if unitary_link_digest != expected.unitary_link_digest {
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

/// Appends a bundle of marginal STARK inner transcripts.
pub fn append_trajectory_stark_tail(mut proof: Vec<u8>, bundle: &[u8]) -> Vec<u8> {
    proof.extend_from_slice(TRAJ_STARK_TAIL_MARKER);
    proof.extend_from_slice(&(bundle.len() as u32).to_le_bytes());
    proof.extend_from_slice(bundle);
    proof
}

pub fn split_trajectory_stark_tail(proof: &[u8]) -> Option<&[u8]> {
    let pos = proof
        .windows(TRAJ_STARK_TAIL_MARKER.len())
        .rposition(|w| w == TRAJ_STARK_TAIL_MARKER)?;
    let cursor = pos + TRAJ_STARK_TAIL_MARKER.len();
    let (len, cursor) = read_u32_le(proof, cursor)?;
    let end = cursor + len as usize;
    proof.get(cursor..end)
}

pub fn has_trajectory_stark_tail(proof: &[u8]) -> bool {
    proof
        .windows(TRAJ_STARK_TAIL_MARKER.len())
        .any(|w| w == TRAJ_STARK_TAIL_MARKER)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn trajectory_marginal_stark_transcript_roundtrip() {
        let ctx = TrajectoryMarginalStarkContext {
            sub_task_id: "sub-traj",
            trajectory_digest: "trajdigest",
            witness_digest: "witnessdigest",
            unitary_link_digest: "unitarylink",
        };
        let encoded = encode_trajectory_marginal_stark(&ctx, b"plonky3-bytes");
        let decoded = decode_trajectory_marginal_stark_owned(&encoded, &ctx).expect("decode");
        assert_eq!(decoded, b"plonky3-bytes");
    }

    #[test]
    fn trajectory_stark_tail_wrapper_roundtrip() {
        let ctx = TrajectoryMarginalStarkContext {
            sub_task_id: "sub-traj",
            trajectory_digest: "trajdigest",
            witness_digest: "witnessdigest",
            unitary_link_digest: "",
        };
        let inner = encode_trajectory_marginal_stark(&ctx, b"plonky3");
        let wrapped = append_trajectory_stark_tail(b"base-proof".to_vec(), &inner);
        assert!(has_trajectory_stark_tail(&wrapped));
        let extracted = split_trajectory_stark_tail(&wrapped).expect("split");
        assert_eq!(extracted, inner.as_slice());
    }
}

//! Extract SHA3 digests of verified child STARK payloads for R3-M1 binding.

use sha3::{Digest, Sha3_256};

use crate::aggregation::{
    is_born_leaf_proof, is_compose_v3, is_trajectory_leaf_proof, parse_leaf_binding,
    parsed_to_stark_context, CHILD_HASH_LEN,
};
use crate::aggregation::{parse_born_leaf_prefix, parse_trajectory_leaf_prefix};
use crate::distribution::base_proof_without_distribution_tail;
use crate::plonky3_stark::shot_sampling_stark::split_shot_sampling_from_bundle;
use crate::plonky3_stark::transcript_born::BORN_STARK_INNER_MARKER;
use crate::plonky3_stark::transcript_trajectory_stark::{
    TRAJ_MARG_STARK_INNER_MARKER, TRAJ_SHOT_STARK_INNER_MARKER,
};
use crate::plonky3_stark::transcript_v2::decode_proof_v2_plonky3_bytes;
use crate::plonky3_stark::transcript_v4::{split_agg_tail, V4_AGG_INNER_MARKER};
use crate::plonky3_stark::{split_born_stark_tail, split_trajectory_stark_tail};
use crate::trajectory::base_proof_without_aux_tails;

use super::air::{REC_KIND_AGG, REC_KIND_LEAF};
use super::transcript_v5::{split_rec_tail, V5_REC_AGG_INNER_MARKER};

pub const STARK_DIGEST_LEN: usize = CHILD_HASH_LEN;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ChildStarkBinding {
    pub stark_digest: [u8; STARK_DIGEST_LEN],
    pub kind: u8,
}

fn sha3_32(bytes: &[u8]) -> [u8; STARK_DIGEST_LEN] {
    let mut out = [0u8; STARK_DIGEST_LEN];
    out.copy_from_slice(&Sha3_256::digest(bytes));
    out
}

fn read_cstr(buf: &[u8], offset: usize) -> Option<usize> {
    let end_rel = buf.get(offset..)?.iter().position(|&b| b == 0)?;
    Some(offset + end_rel + 1)
}

fn plonky3_payload_from_rec_or_agg_inner(inner: &[u8], is_v5: bool) -> Option<&[u8]> {
    let marker = if is_v5 {
        V5_REC_AGG_INNER_MARKER
    } else {
        V4_AGG_INNER_MARKER
    };
    let pos = inner.windows(marker.len()).position(|w| w == marker)?;
    let mut cursor = pos + marker.len();
    cursor = read_cstr(inner, cursor)?; // compose_label
    cursor = read_cstr(inner, cursor)?; // manifest
    cursor += 64; // two child hashes
    if is_v5 {
        cursor += 64 + 2; // stark digests + kinds
    }
    if cursor + 4 > inner.len() {
        return None;
    }
    let len = u32::from_le_bytes(inner[cursor..cursor + 4].try_into().ok()?) as usize;
    cursor += 4;
    inner.get(cursor..cursor + len)
}

fn leaf_plonky3_payload(child: &[u8]) -> Option<Vec<u8>> {
    let base = base_proof_without_aux_tails(base_proof_without_distribution_tail(child));
    let parsed = parse_leaf_binding(base)?;
    let ctx = parsed_to_stark_context(&parsed);
    decode_proof_v2_plonky3_bytes(base, &ctx)
}

fn read_u32_le(buf: &[u8], offset: usize) -> Option<(u32, usize)> {
    let bytes = buf.get(offset..offset + 4)?;
    let mut raw = [0u8; 4];
    raw.copy_from_slice(bytes);
    Some((u32::from_le_bytes(raw), offset + 4))
}

fn plonky3_after_inner_marker(inner: &[u8], marker: &[u8], skip_cstrs: usize) -> Option<Vec<u8>> {
    let marker_pos = inner.windows(marker.len()).position(|w| w == marker)?;
    let mut cursor = marker_pos + marker.len();
    for _ in 0..skip_cstrs {
        cursor = read_cstr(inner, cursor)?;
    }
    let (len, cursor) = read_u32_le(inner, cursor)?;
    let end = cursor + len as usize;
    inner.get(cursor..end).map(|s| s.to_vec())
}

fn born_plonky3_digest_payload(child: &[u8]) -> Result<Vec<u8>, String> {
    let (_, tail_body) =
        parse_born_leaf_prefix(child).ok_or_else(|| "malformed Born leaf".to_string())?;
    let born_inner =
        split_born_stark_tail(tail_body).ok_or_else(|| "missing Born tail".to_string())?;
    plonky3_after_inner_marker(born_inner, BORN_STARK_INNER_MARKER, 2)
        .ok_or_else(|| "cannot extract Born plonky3 payload".to_string())
}

fn traj_plonky3_digest_payload(child: &[u8]) -> Result<Vec<u8>, String> {
    let (_, tail_body) = parse_trajectory_leaf_prefix(child)
        .ok_or_else(|| "malformed trajectory leaf".to_string())?;
    let bundle = split_trajectory_stark_tail(tail_body)
        .ok_or_else(|| "missing trajectory zk tail".to_string())?;
    let (marginal_bundle, shot_inner) = split_shot_sampling_from_bundle(bundle)
        .ok_or_else(|| "malformed trajectory bundle".to_string())?;
    let (witness_count, mut cursor) =
        read_u32_le(marginal_bundle, 0).ok_or_else(|| "truncated marginal header".to_string())?;
    let mut concat = Vec::new();
    for _ in 0..witness_count {
        let (inner_len, next) = read_u32_le(marginal_bundle, cursor)
            .ok_or_else(|| "truncated marginal inner".to_string())?;
        cursor = next;
        let end = cursor + inner_len as usize;
        let inner = marginal_bundle
            .get(cursor..end)
            .ok_or_else(|| "truncated marginal proof".to_string())?;
        let plonky3 = plonky3_after_inner_marker(inner, TRAJ_MARG_STARK_INNER_MARKER, 3)
            .ok_or_else(|| "cannot extract marginal plonky3".to_string())?;
        concat.extend_from_slice(&plonky3);
        cursor = end;
    }
    let marker_pos = shot_inner
        .windows(TRAJ_SHOT_STARK_INNER_MARKER.len())
        .position(|w| w == TRAJ_SHOT_STARK_INNER_MARKER)
        .ok_or_else(|| "missing shot marker".to_string())?;
    let mut sc = marker_pos + TRAJ_SHOT_STARK_INNER_MARKER.len();
    sc = read_cstr(shot_inner, sc).ok_or_else(|| "truncated shot digest".to_string())?;
    if shot_inner.len() < sc + 20 {
        return Err("truncated shot tail".into());
    }
    sc += 20;
    let (len, sc) = read_u32_le(shot_inner, sc).ok_or_else(|| "truncated shot len".to_string())?;
    let end = sc + len as usize;
    let shot_plonky3 = shot_inner
        .get(sc..end)
        .ok_or_else(|| "truncated shot plonky3".to_string())?;
    concat.extend_from_slice(shot_plonky3);
    Ok(concat)
}

/// Digests the Plonky3 STARK payload that was (or will be) verified for this child.
pub fn child_stark_binding(child: &[u8]) -> ChildStarkBinding {
    if let Some((_, rec)) = split_rec_tail(child) {
        if let Some(payload) = plonky3_payload_from_rec_or_agg_inner(rec, true) {
            return ChildStarkBinding {
                stark_digest: sha3_32(payload),
                kind: REC_KIND_AGG,
            };
        }
    }
    if let Some((_, agg)) = split_agg_tail(child) {
        if let Some(payload) = plonky3_payload_from_rec_or_agg_inner(agg, false) {
            return ChildStarkBinding {
                stark_digest: sha3_32(payload),
                kind: REC_KIND_AGG,
            };
        }
    }
    if is_born_leaf_proof(child) {
        if let Ok(plonky3) = born_plonky3_digest_payload(child) {
            return ChildStarkBinding {
                stark_digest: sha3_32(&plonky3),
                kind: REC_KIND_LEAF,
            };
        }
    }
    if is_trajectory_leaf_proof(child) {
        if let Ok(plonky3) = traj_plonky3_digest_payload(child) {
            return ChildStarkBinding {
                stark_digest: sha3_32(&plonky3),
                kind: REC_KIND_LEAF,
            };
        }
    }
    if is_compose_v3(child) {
        // Nested compose nodes carry agg/rec tails; bind whole verified blob.
        return ChildStarkBinding {
            stark_digest: sha3_32(child),
            kind: REC_KIND_AGG,
        };
    }
    if let Some(payload) = leaf_plonky3_payload(child) {
        return ChildStarkBinding {
            stark_digest: sha3_32(&payload),
            kind: REC_KIND_LEAF,
        };
    }
    ChildStarkBinding {
        stark_digest: sha3_32(child),
        kind: REC_KIND_LEAF,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn binding_is_deterministic() {
        let a = child_stark_binding(b"not-a-real-proof");
        let b = child_stark_binding(b"not-a-real-proof");
        assert_eq!(a, b);
        assert_eq!(a.kind, REC_KIND_LEAF);
    }
}

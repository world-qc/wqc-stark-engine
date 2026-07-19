//! Extract SHA3 digests of verified child STARK payloads for R3-M1 binding.

use sha3::{Digest, Sha3_256};

use crate::aggregation::{
    is_born_leaf_proof, is_compose_v3, is_trajectory_leaf_proof, parse_leaf_binding,
    parsed_to_stark_context, CHILD_HASH_LEN,
};
use crate::distribution::base_proof_without_distribution_tail;
use crate::plonky3_stark::transcript_v2::decode_proof_v2_plonky3_bytes;
use crate::plonky3_stark::transcript_v4::{split_agg_tail, V4_AGG_INNER_MARKER};
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
    if is_compose_v3(child) || is_trajectory_leaf_proof(child) || is_born_leaf_proof(child) {
        // Nested compose / distribution leaf wrappers: bind whole verified blob.
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

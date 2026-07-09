//! v3 proof-tree compose transcript (pairs of child proofs).
//!
//! This is a **structural** aggregation format: compose verifies both children,
//! binds their SHA3-256 digests, and embeds the child bytes. A future phase will
//! replace the container with a true recursive Plonky3 aggregation proof.

use sha3::{Digest, Sha3_256};

pub const V3_COMPOSE_MARKER: &[u8] = b"_WQC_COMPOSE_V3_";
pub const CHILD_HASH_LEN: usize = 32;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ComposeHeader {
    pub parent_task_id: String,
    pub compose_label: String,
    pub manifest_root_hash: String,
    pub left_child_hash: [u8; CHILD_HASH_LEN],
    pub right_child_hash: [u8; CHILD_HASH_LEN],
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

fn read_fixed<const N: usize>(proof: &[u8], offset: usize) -> Option<([u8; N], usize)> {
    let bytes = proof.get(offset..offset + N)?;
    let mut out = [0u8; N];
    out.copy_from_slice(bytes);
    Some((out, offset + N))
}

pub fn child_digest(child: &[u8]) -> [u8; CHILD_HASH_LEN] {
    let mut hasher = Sha3_256::new();
    hasher.update(child);
    hasher.finalize().into()
}

/// Encodes a v3 compose transcript embedding two verified child proofs.
pub fn encode_compose_v3(
    parent_task_id: &str,
    compose_label: &str,
    manifest_root_hash: &str,
    left_child: &[u8],
    right_child: &[u8],
) -> Vec<u8> {
    let left_hash = child_digest(left_child);
    let right_hash = child_digest(right_child);

    let mut out = Vec::new();
    out.extend_from_slice(parent_task_id.as_bytes());
    out.push(0);
    out.extend_from_slice(V3_COMPOSE_MARKER);
    out.extend_from_slice(compose_label.as_bytes());
    out.push(0);
    out.extend_from_slice(manifest_root_hash.as_bytes());
    out.push(0);
    out.extend_from_slice(&left_hash);
    out.extend_from_slice(&right_hash);
    out.extend_from_slice(&(left_child.len() as u32).to_le_bytes());
    out.extend_from_slice(left_child);
    out.extend_from_slice(&(right_child.len() as u32).to_le_bytes());
    out.extend_from_slice(right_child);
    out
}

/// Returns true when `proof` contains a v3 compose marker.
pub fn is_compose_v3(proof: &[u8]) -> bool {
    proof
        .windows(V3_COMPOSE_MARKER.len())
        .any(|w| w == V3_COMPOSE_MARKER)
}

/// Locates the v3 compose marker and returns the parent_task_id prefix length.
pub fn locate_compose_marker(proof: &[u8]) -> Option<usize> {
    let pos = proof
        .windows(V3_COMPOSE_MARKER.len())
        .position(|w| w == V3_COMPOSE_MARKER)?;
    let prefix = &proof[..pos];
    if prefix.is_empty() || prefix.last() != Some(&0) {
        return None;
    }
    Some(pos)
}

pub fn decode_compose_v3(proof: &[u8]) -> Option<(ComposeHeader, Vec<u8>, Vec<u8>)> {
    let (header, left, right) = decode_compose_v3_slices(proof)?;
    Some((header, left.to_vec(), right.to_vec()))
}

/// Decodes a v3 compose transcript returning child byte slices into `proof`.
pub fn decode_compose_v3_slices(proof: &[u8]) -> Option<(ComposeHeader, &[u8], &[u8])> {
    let marker_pos = locate_compose_marker(proof)?;
    let parent_end = marker_pos.saturating_sub(1);
    let parent_task_id = std::str::from_utf8(&proof[..parent_end]).ok()?.to_string();

    let cursor = marker_pos + V3_COMPOSE_MARKER.len();
    let (compose_label, cursor) = read_cstr(proof, cursor)?;
    let (manifest_root_hash, cursor) = read_cstr(proof, cursor)?;
    let (left_child_hash, cursor) = read_fixed::<CHILD_HASH_LEN>(proof, cursor)?;
    let (right_child_hash, cursor) = read_fixed::<CHILD_HASH_LEN>(proof, cursor)?;
    let (left_len, cursor) = read_u32_le(proof, cursor)?;
    let left_end = cursor + left_len as usize;
    let left_child = proof.get(cursor..left_end)?;
    let cursor = left_end;
    let (right_len, cursor) = read_u32_le(proof, cursor)?;
    let right_end = cursor + right_len as usize;
    let right_child = proof.get(cursor..right_end)?;
    if right_end != proof.len() {
        return None;
    }

    Some((
        ComposeHeader {
            parent_task_id,
            compose_label,
            manifest_root_hash,
            left_child_hash,
            right_child_hash,
        },
        left_child,
        right_child,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn compose_roundtrip_and_hashes() {
        let left = b"leaf-left-bytes";
        let right = b"leaf-right-bytes";
        let proof = encode_compose_v3("parent-1", "L1:0", "", left, right);
        assert!(is_compose_v3(&proof));

        let (header, decoded_left, decoded_right) = decode_compose_v3(&proof).expect("decode");
        assert_eq!(header.parent_task_id, "parent-1");
        assert_eq!(header.compose_label, "L1:0");
        assert_eq!(decoded_left, left);
        assert_eq!(decoded_right, right);
        assert_eq!(header.left_child_hash, child_digest(left));
        assert_eq!(header.right_child_hash, child_digest(right));
    }

    #[test]
    fn tampered_child_hash_rejected_on_decode_check() {
        let left = b"left";
        let right = b"right";
        let mut proof = encode_compose_v3("parent-1", "root", "manifest-hash", left, right);
        let (header, _, _) = decode_compose_v3(&proof).unwrap();
        assert_eq!(header.manifest_root_hash, "manifest-hash");

        // Flip a byte in embedded left child without updating hash.
        let marker_pos = locate_compose_marker(&proof).unwrap();
        let (_, cursor) = read_cstr(&proof, marker_pos + V3_COMPOSE_MARKER.len()).unwrap();
        let (_, cursor) = read_cstr(&proof, cursor).unwrap();
        let (_, cursor) = read_fixed::<CHILD_HASH_LEN>(&proof, cursor).unwrap();
        let (_, cursor) = read_fixed::<CHILD_HASH_LEN>(&proof, cursor).unwrap();
        let (_, cursor) = read_u32_le(&proof, cursor).unwrap();
        proof[cursor] ^= 0xFF;

        let (header2, decoded_left, _) = decode_compose_v3(&proof).unwrap();
        assert_ne!(child_digest(&decoded_left), header2.left_child_hash);
        assert_eq!(header.left_child_hash, header2.left_child_hash);
    }
}

//! R3-M3d: variable-depth ValMmcs / flattened-ChallengeMmcs Merkle path digests.
//!
//! Production PCS Merkle is Poseidon2; this module records digest-only openings.
//! In-circuit path checks live in M4c Poseidon (or Keccak) group STARKs.
//! Fixed-depth Keccak fold AIR for AggregationAir LDE remains in
//! [`super::keccak_merkle_air`].

use p3_mersenne_31::Mersenne31;

use super::keccak256_air::Keccak256StarkProof;
use super::merkle_keccak::{compress_digests, hash_val_leaf};

/// Max Merkle depth for FRI Mmcs paths (Born n≤16 LDE needs ≤17; cap at 20).
pub const FRI_MMCS_MAX_DEPTH: usize = 20;

/// Digest-only Merkle path for a single ValMmcs (or flattened Challenge) matrix.
///
/// Nested `fold_stark` / Keccak sponge STARKs are empty; digests bind the opening
/// and M4c groups prove the path in-circuit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FriMmcsPathProof {
    pub depth: u32,
    pub leaf_width: u32,
    pub leaf_digest: [u8; 32],
    pub layer_digests: Vec<[u8; 32]>,
    pub fold_stark: Vec<u8>,
    pub leaf_keccak: Keccak256StarkProof,
    pub compress_starks: Vec<Keccak256StarkProof>,
}

/// Prove a binary Merkle path for an arbitrary-width M31 leaf row.
pub fn generate_fri_mmcs_path_proof(
    row: &[Mersenne31],
    siblings: &[[u8; 32]],
    index: usize,
    expected_root: &[u8; 32],
) -> Result<FriMmcsPathProof, String> {
    generate_fri_mmcs_path_proof_inner(row, siblings, index, expected_root)
}

/// Alias kept for callers that previously dropped nested Keccak STARKs.
/// Digest-only paths already omit nested STARK bytes.
pub fn generate_fri_mmcs_path_proof_drop_nested(
    row: &[Mersenne31],
    siblings: &[[u8; 32]],
    index: usize,
    expected_root: &[u8; 32],
) -> Result<FriMmcsPathProof, String> {
    generate_fri_mmcs_path_proof_inner(row, siblings, index, expected_root)
}

fn generate_fri_mmcs_path_proof_inner(
    row: &[Mersenne31],
    siblings: &[[u8; 32]],
    index: usize,
    expected_root: &[u8; 32],
) -> Result<FriMmcsPathProof, String> {
    let depth = siblings.len();
    if depth == 0 || depth > FRI_MMCS_MAX_DEPTH {
        return Err(format!("unsupported Merkle depth {depth}"));
    }
    let leaf_digest = hash_val_leaf(row);
    let leaf_keccak = Keccak256StarkProof {
        msg_len: (row.len() * 4) as u32,
        digest: leaf_digest,
        stark: vec![],
    };

    let mut digest = leaf_digest;
    let mut idx = index;
    let mut layer_digests = Vec::with_capacity(depth);
    let mut compress_starks = Vec::with_capacity(depth);
    for sib in siblings {
        let (left, right) = if idx.is_multiple_of(2) {
            (digest, *sib)
        } else {
            (*sib, digest)
        };
        digest = compress_digests(left, right);
        layer_digests.push(digest);
        compress_starks.push(Keccak256StarkProof {
            msg_len: 64,
            digest,
            stark: vec![],
        });
        idx /= 2;
    }
    if &digest != expected_root {
        return Err("folded root mismatch".into());
    }

    Ok(FriMmcsPathProof {
        depth: depth as u32,
        leaf_width: row.len() as u32,
        leaf_digest,
        layer_digests,
        fold_stark: Vec::new(),
        leaf_keccak,
        compress_starks,
    })
}

pub fn verify_fri_mmcs_path_proof(
    row: &[Mersenne31],
    siblings: &[[u8; 32]],
    index: usize,
    expected_root: &[u8; 32],
    proof: &FriMmcsPathProof,
) -> bool {
    let depth = proof.depth as usize;
    if siblings.len() != depth
        || proof.layer_digests.len() != depth
        || proof.compress_starks.len() != depth
        || row.len() as u32 != proof.leaf_width
        || depth == 0
        || depth > FRI_MMCS_MAX_DEPTH
    {
        eprintln!("[FriMmcsPath] Failed: shape");
        return false;
    }
    let leaf = hash_val_leaf(row);
    if leaf != proof.leaf_digest || leaf != proof.leaf_keccak.digest {
        eprintln!("[FriMmcsPath] Failed: leaf digest");
        return false;
    }
    let mut digest = leaf;
    let mut idx = index;
    for (i, sib) in siblings.iter().enumerate() {
        let (left, right) = if idx.is_multiple_of(2) {
            (digest, *sib)
        } else {
            (*sib, digest)
        };
        let next = compress_digests(left, right);
        if next != proof.layer_digests[i] || next != proof.compress_starks[i].digest {
            eprintln!("[FriMmcsPath] Failed: compress layer {i}");
            return false;
        }
        digest = next;
        idx /= 2;
    }
    if &digest != expected_root {
        eprintln!("[FriMmcsPath] Failed: root");
        return false;
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_field::PrimeCharacteristicRing;

    fn sib(seed: u32) -> [u8; 32] {
        crate::plonky3_stark::config_poseidon::pack_digest([Mersenne31::from_u32(seed); 8])
    }

    #[test]
    fn fri_mmcs_path_quot_width3_depth1() {
        let row = [
            Mersenne31::from_u32(1),
            Mersenne31::from_u32(2),
            Mersenne31::from_u32(3),
        ];
        let leaf = hash_val_leaf(&row);
        let sibling = sib(9);
        let root = compress_digests(leaf, sibling);
        let proof = generate_fri_mmcs_path_proof(&row, &[sibling], 0, &root).expect("prove");
        assert!(verify_fri_mmcs_path_proof(
            &row,
            &[sibling],
            0,
            &root,
            &proof
        ));
    }

    #[test]
    fn fri_mmcs_path_chal_width6() {
        let row: Vec<_> = (0..6)
            .map(|i| Mersenne31::from_u32(i as u32 + 10))
            .collect();
        let leaf = hash_val_leaf(&row);
        let sibling = sib(3);
        let root = compress_digests(sibling, leaf); // index=1
        let proof = generate_fri_mmcs_path_proof(&row, &[sibling], 1, &root).expect("prove");
        assert!(verify_fri_mmcs_path_proof(
            &row,
            &[sibling],
            1,
            &root,
            &proof
        ));
    }

    #[test]
    fn fri_mmcs_path_drop_nested_keeps_digests() {
        let row = [
            Mersenne31::from_u32(1),
            Mersenne31::from_u32(2),
            Mersenne31::from_u32(3),
        ];
        let leaf = hash_val_leaf(&row);
        let sibling = sib(9);
        let root = compress_digests(leaf, sibling);
        let proof =
            generate_fri_mmcs_path_proof_drop_nested(&row, &[sibling], 0, &root).expect("prove");
        assert!(proof.fold_stark.is_empty());
        assert!(proof.leaf_keccak.stark.is_empty());
        assert!(proof.compress_starks.iter().all(|c| c.stark.is_empty()));
        assert_eq!(proof.leaf_digest, leaf);
        assert_eq!(proof.layer_digests[0], root);
        assert!(verify_fri_mmcs_path_proof(
            &row,
            &[sibling],
            0,
            &root,
            &proof
        ));
    }
}

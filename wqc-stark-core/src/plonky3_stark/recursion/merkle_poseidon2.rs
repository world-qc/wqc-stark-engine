//! Poseidon2 Merkle helpers (E5b spike — not ValMmcs wire format yet).
//!
//! Native leaf hashing and binary compression using width-16 M31 Poseidon2.

use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_mersenne_31::{default_mersenne31_poseidon2_16, Mersenne31};
use p3_symmetric::Permutation;

use super::poseidon2_spike::{poseidon2_compress32, POSEIDON2_WIDTH};

/// Leaf digest of an M31 row via Poseidon2 sponge (field-native absorb).
pub fn hash_val_leaf_poseidon(row: &[Mersenne31]) -> [u8; 32] {
    let mut state = [Mersenne31::ZERO; POSEIDON2_WIDTH];
    for (i, v) in row.iter().enumerate().take(POSEIDON2_WIDTH) {
        state[i] = *v;
    }
    default_mersenne31_poseidon2_16().permute_mut(&mut state);
    state_to_digest(&state)
}

/// Binary compress: Poseidon2 over `(left || right)` packed into rate slots.
pub fn compress_digests_poseidon(left: [u8; 32], right: [u8; 32]) -> [u8; 32] {
    poseidon2_compress32(left, right)
}

fn state_to_digest(state: &[Mersenne31; POSEIDON2_WIDTH]) -> [u8; 32] {
    let mut out = [0u8; 32];
    for (i, limb) in state.iter().take(8).enumerate() {
        out[i * 4..(i + 1) * 4].copy_from_slice(&limb.as_canonical_u32().to_le_bytes());
    }
    out
}

/// Recomputes the Merkle root for a binary path using Poseidon2 compression.
pub fn merkle_root_from_path_poseidon(
    leaf_digest: [u8; 32],
    siblings: &[[u8; 32]],
    mut index: usize,
) -> [u8; 32] {
    let mut digest = leaf_digest;
    for sibling in siblings {
        let pos = index % 2;
        digest = if pos == 0 {
            compress_digests_poseidon(digest, *sibling)
        } else {
            compress_digests_poseidon(*sibling, digest)
        };
        index /= 2;
    }
    digest
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_field::PrimeField32;

    #[test]
    fn poseidon_leaf_hash_deterministic() {
        let row = vec![
            Mersenne31::from_u32(1),
            Mersenne31::from_u32(2),
            Mersenne31::from_u32(3),
        ];
        let a = hash_val_leaf_poseidon(&row);
        let b = hash_val_leaf_poseidon(&row);
        assert_eq!(a, b);
        assert_ne!(a, [0u8; 32]);
    }

    #[test]
    fn poseidon_merkle_path_roundtrip() {
        let row = vec![Mersenne31::from_u32(9); 3];
        let leaf = hash_val_leaf_poseidon(&row);
        let sibling = [7u8; 32];
        let root = compress_digests_poseidon(leaf, sibling);
        let got = merkle_root_from_path_poseidon(leaf, &[sibling], 0);
        assert_eq!(got, root);
    }
}

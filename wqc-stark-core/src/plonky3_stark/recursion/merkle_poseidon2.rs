//! Poseidon2 Merkle helpers (E5b spike — not ValMmcs wire format yet).
//!
//! Native leaf hashing and binary compression using width-16 M31 Poseidon2.

use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_mersenne_31::{default_mersenne31_poseidon2_16, Mersenne31};
use p3_symmetric::Permutation;

use super::keccak_f_native::KECCAK_RATE;
use super::poseidon2_spike::{poseidon2_compress32, POSEIDON2_WIDTH};

/// Number of width-16 perm segments to absorb a ValMmcs leaf row (M4b-eligible widths).
pub fn poseidon_leaf_perm_count(leaf_width: usize) -> usize {
    leaf_width.div_ceil(POSEIDON2_WIDTH)
}

/// True when the Poseidon2 group prototype can prove this homogeneous width.
pub fn poseidon_m4b_width_eligible(leaf_width: usize) -> bool {
    let msg_len = leaf_width.saturating_mul(4);
    (12..=2 * KECCAK_RATE).contains(&msg_len) && msg_len.is_multiple_of(4)
}

/// One leaf perm input: row chunk `perm_k * WIDTH .. (perm_k+1) * WIDTH`.
pub fn leaf_perm_state(row: &[Mersenne31], perm_k: usize) -> [Mersenne31; POSEIDON2_WIDTH] {
    let mut state = [Mersenne31::ZERO; POSEIDON2_WIDTH];
    let base = perm_k * POSEIDON2_WIDTH;
    for i in 0..POSEIDON2_WIDTH {
        if base + i < row.len() {
            state[i] = row[base + i];
        }
    }
    state
}

/// Leaf digest of an M31 row via chained Poseidon2 perms (field-native absorb).
pub fn hash_val_leaf_poseidon(row: &[Mersenne31]) -> [u8; 32] {
    let perm = default_mersenne31_poseidon2_16();
    let n = poseidon_leaf_perm_count(row.len());
    let mut state = leaf_perm_state(row, 0);
    perm.permute_mut(&mut state);
    for k in 1..n {
        state = leaf_perm_state(row, k);
        perm.permute_mut(&mut state);
    }
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
    fn poseidon_wide_leaf_hash_w48() {
        let row: Vec<_> = (0..48)
            .map(|i| Mersenne31::from_u32(i as u32 + 7))
            .collect();
        assert_eq!(poseidon_leaf_perm_count(row.len()), 3);
        let a = hash_val_leaf_poseidon(&row);
        let b = hash_val_leaf_poseidon(&row);
        assert_eq!(a, b);
        assert_ne!(a, hash_val_leaf_poseidon(&row[..16]));
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

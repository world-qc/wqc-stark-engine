//! Poseidon2 Merkle helpers matching production [`crate::plonky3_stark::config::ValMmcs`].
//!
//! Leaf sponge + binary compress are identical to `config_poseidon` packed Poseidon Mmcs.

use p3_field::PrimeCharacteristicRing;
use p3_mersenne_31::Mersenne31;

use super::keccak_f_native::KECCAK_RATE;
use super::poseidon2_spike::POSEIDON2_WIDTH;
use crate::plonky3_stark::config_poseidon::{
    compress_digests_poseidon_mmcs, poseidon_sponge_leaf_perm_inputs,
};

pub use crate::plonky3_stark::config_poseidon::{
    compress_digests_poseidon_mmcs as compress_digests_poseidon,
    hash_val_leaf_poseidon_mmcs as hash_val_leaf_poseidon, poseidon_compress_perm_input,
    poseidon_leaf_perm_count,
};

/// True when the Poseidon2 group prototype can prove this homogeneous width.
pub fn poseidon_m4b_width_eligible(leaf_width: usize) -> bool {
    let msg_len = leaf_width.saturating_mul(4);
    (12..=2 * KECCAK_RATE).contains(&msg_len) && msg_len.is_multiple_of(4)
}

/// One leaf sponge perm input (RATE=8 overwrite); `perm_k` indexes sponge rounds.
pub fn leaf_perm_state(row: &[Mersenne31], perm_k: usize) -> [Mersenne31; POSEIDON2_WIDTH] {
    let inputs = poseidon_sponge_leaf_perm_inputs(row);
    inputs
        .get(perm_k)
        .copied()
        .unwrap_or([Mersenne31::ZERO; POSEIDON2_WIDTH])
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
            compress_digests_poseidon_mmcs(digest, *sibling)
        } else {
            compress_digests_poseidon_mmcs(*sibling, digest)
        };
        index /= 2;
    }
    digest
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::plonky3_stark::config_poseidon::{pack_digest, poseidon_val_mmcs};
    use p3_commit::Mmcs;
    use p3_field::PrimeCharacteristicRing;
    use p3_matrix::dense::RowMajorMatrix;

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
        assert_eq!(poseidon_leaf_perm_count(row.len()), 6);
        let a = hash_val_leaf_poseidon(&row);
        let b = hash_val_leaf_poseidon(&row);
        assert_eq!(a, b);
        assert_ne!(a, hash_val_leaf_poseidon(&row[..8]));
    }

    #[test]
    fn poseidon_leaf_matches_val_mmcs() {
        let mmcs = poseidon_val_mmcs();
        let row: Vec<_> = (0..3).map(|i| Mersenne31::from_u32(i + 9)).collect();
        let mat = RowMajorMatrix::new(row.clone(), 3);
        let (commit, _) = mmcs.commit(vec![mat]);
        assert_eq!(
            hash_val_leaf_poseidon(&row),
            *commit.roots().first().expect("root")
        );
    }

    #[test]
    fn poseidon_merkle_path_roundtrip() {
        let row = vec![Mersenne31::from_u32(9); 3];
        let leaf = hash_val_leaf_poseidon(&row);
        let sibling = pack_digest([Mersenne31::from_u32(7); 8]);
        let root = compress_digests_poseidon(leaf, sibling);
        let got = merkle_root_from_path_poseidon(leaf, &[sibling], 0);
        assert_eq!(got, root);
    }
}

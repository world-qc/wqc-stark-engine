//! Poseidon2 Merkle helpers matching production [`crate::plonky3_stark::config::ValMmcs`].
//!
//! Leaf sponge + binary compress are identical to `config_poseidon` packed Poseidon Mmcs.

use super::keccak_f_native::KECCAK_RATE;

pub use crate::plonky3_stark::config_poseidon::{
    compress_digests_poseidon_mmcs as compress_digests_poseidon,
    hash_val_leaf_poseidon_mmcs as hash_val_leaf_poseidon, poseidon_compress_perm_input,
};

/// True when the Poseidon2 group prototype can prove this homogeneous width.
pub fn poseidon_m4b_width_eligible(leaf_width: usize) -> bool {
    let msg_len = leaf_width.saturating_mul(4);
    (12..=2 * KECCAK_RATE).contains(&msg_len) && msg_len.is_multiple_of(4)
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
    use crate::plonky3_stark::config_poseidon::{
        pack_digest, poseidon_leaf_perm_count, poseidon_val_mmcs,
    };
    use p3_commit::Mmcs;
    use p3_field::PrimeCharacteristicRing;
    use p3_matrix::dense::RowMajorMatrix;
    use p3_mersenne_31::Mersenne31;

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

#[cfg(test)]
mod wrap_golden {
    use super::*;
    use crate::plonky3_stark::config_poseidon::pack_digest;
    use p3_field::{PrimeCharacteristicRing, PrimeField32};
    use p3_mersenne_31::{default_mersenne31_poseidon2_16, Mersenne31};
    use p3_symmetric::Permutation;

    #[test]
    fn poseidon2_default_permute_and_mmcs_golden() {
        let golden_path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../fixtures/e5b/wrap_poseidon2_mmcs_golden.json"
        );
        let raw = std::fs::read_to_string(golden_path).expect("wrap_poseidon2_mmcs_golden.json");
        let v: serde_json::Value = serde_json::from_str(&raw).expect("golden json");

        let mut state = [
            Mersenne31::from_u32(1),
            Mersenne31::from_u32(2),
            Mersenne31::from_u32(3),
            Mersenne31::from_u32(4),
            Mersenne31::from_u32(5),
            Mersenne31::from_u32(6),
            Mersenne31::from_u32(7),
            Mersenne31::from_u32(8),
            Mersenne31::from_u32(9),
            Mersenne31::from_u32(10),
            Mersenne31::from_u32(11),
            Mersenne31::from_u32(12),
            Mersenne31::from_u32(13),
            Mersenne31::from_u32(14),
            Mersenne31::from_u32(15),
            Mersenne31::from_u32(16),
        ];
        default_mersenne31_poseidon2_16().permute_mut(&mut state);
        let want_perm = v["permute_out"]
            .as_array()
            .expect("permute_out")
            .iter()
            .map(|x| x.as_u64().unwrap() as u32)
            .collect::<Vec<_>>();
        for (i, x) in state.iter().enumerate() {
            assert_eq!(x.as_canonical_u32(), want_perm[i], "perm limb {i}");
        }

        let row = vec![
            Mersenne31::from_u32(1),
            Mersenne31::from_u32(2),
            Mersenne31::from_u32(3),
        ];
        let leaf = hash_val_leaf_poseidon(&row);
        let sibling = pack_digest([Mersenne31::from_u32(7); 8]);
        let root = compress_digests_poseidon(leaf, sibling);
        assert_eq!(root, merkle_root_from_path_poseidon(leaf, &[sibling], 0));

        let want_leaf: Vec<u8> = v["leaf_digest"]
            .as_array()
            .unwrap()
            .iter()
            .map(|x| x.as_u64().unwrap() as u8)
            .collect();
        let want_root: Vec<u8> = v["path_root"]
            .as_array()
            .unwrap()
            .iter()
            .map(|x| x.as_u64().unwrap() as u8)
            .collect();
        assert_eq!(leaf.as_slice(), want_leaf.as_slice());
        assert_eq!(root.as_slice(), want_root.as_slice());
    }
}

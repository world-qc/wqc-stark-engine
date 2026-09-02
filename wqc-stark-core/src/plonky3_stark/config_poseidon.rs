//! Poseidon2 field-native ValMmcs scaffolding (E5b migration Phase 3).
//!
//! Parallel to [`super::config`] Keccak/`SerializingHasher` wire. Digests are
//! **8 × M31** (not `[u8; 32]`), matching Plonky3 BabyBear Poseidon trees.
//! Production `WqcStarkConfig` stays Keccak until RecAgg / leaf PCS digest
//! encoding is migrated.

use p3_commit::{ExtensionMmcs, Mmcs};
use p3_field::Field;
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_mersenne_31::{default_mersenne31_poseidon2_16, Mersenne31, Poseidon2Mersenne31};
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};

use super::config::{Challenge, Val};

/// Poseidon2 width-16 permutation (same as group-fold spike).
pub type Poseidon2Perm16 = Poseidon2Mersenne31<16>;
/// Leaf / row hasher: sponge WIDTH=16, RATE=8, OUT=8 field limbs.
pub type PoseidonFieldHash = PaddingFreeSponge<Poseidon2Perm16, 16, 8, 8>;
/// Binary compress: truncated perm over 2×8 limbs.
pub type PoseidonCompress = TruncatedPermutation<Poseidon2Perm16, 2, 8, 16>;
/// Field-native Merkle Mmcs (digest = 8 × M31).
pub type PoseidonValMmcs = MerkleTreeMmcs<
    <Val as Field>::Packing,
    <Val as Field>::Packing,
    PoseidonFieldHash,
    PoseidonCompress,
    2,
    8,
>;
pub type PoseidonChallengeMmcs = ExtensionMmcs<Val, Challenge, PoseidonValMmcs>;

/// Field limbs per Poseidon Merkle digest (vs Keccak's 32 bytes).
pub const POSEIDON_DIGEST_LIMBS: usize = 8;

/// Builds a Poseidon2 ValMmcs with Plonky3 default M31 RC tables (`cap_height = 0`).
pub fn poseidon_val_mmcs() -> PoseidonValMmcs {
    let perm = default_mersenne31_poseidon2_16();
    let hash = PoseidonFieldHash::new(perm.clone());
    let compress = PoseidonCompress::new(perm);
    PoseidonValMmcs::new(hash, compress, 0)
}

/// Builds ChallengeMmcs wrapping [`poseidon_val_mmcs`].
pub fn poseidon_challenge_mmcs() -> PoseidonChallengeMmcs {
    PoseidonChallengeMmcs::new(poseidon_val_mmcs())
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_commit::{BatchOpeningRef, Mmcs};
    use p3_field::PrimeCharacteristicRing;
    use p3_matrix::Dimensions;

    #[test]
    fn poseidon_val_mmcs_commit_open_roundtrip() {
        let mmcs = poseidon_val_mmcs();
        // 8 rows × width 3 — power-of-two height for a small tree.
        let mut values = Vec::with_capacity(8 * 3);
        for r in 0u32..8 {
            values.push(Mersenne31::from_u32(r * 3 + 1));
            values.push(Mersenne31::from_u32(r * 3 + 2));
            values.push(Mersenne31::from_u32(r * 3 + 3));
        }
        let mat = RowMajorMatrix::new(values, 3);
        let (commit, prover_data) = mmcs.commit(vec![mat]);
        let index = 5usize;
        let batch = mmcs.open_batch(index, &prover_data);
        assert_eq!(batch.opened_values.len(), 1);
        assert_eq!(batch.opened_values[0].len(), 3);
        let dims = [Dimensions {
            width: 3,
            height: 8,
        }];
        mmcs.verify_batch(
            &commit,
            &dims,
            index,
            BatchOpeningRef::new(&batch.opened_values, &batch.opening_proof),
        )
        .expect("poseidon ValMmcs verify");
    }

    #[test]
    fn poseidon_digest_is_eight_limbs() {
        assert_eq!(POSEIDON_DIGEST_LIMBS, 8);
        let mmcs = poseidon_val_mmcs();
        let mat = RowMajorMatrix::new(vec![Mersenne31::ONE; 4], 1);
        let (commit, _) = mmcs.commit(vec![mat]);
        // MerkleCap with cap_height=0 → single root digest of 8 limbs.
        assert_eq!(commit.num_roots(), 1);
        let root = commit.roots()[0];
        assert_eq!(root.len(), POSEIDON_DIGEST_LIMBS);
    }
}

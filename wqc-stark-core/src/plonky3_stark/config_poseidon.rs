//! Poseidon2 field-native ValMmcs for production [`super::config::WqcStarkConfig`].
//!
//! Digests are **packed** `8 × M31 → [u8; 32]` so RecAgg / leaf PCS wire and
//! `SerializingChallenger32` stay byte-digest shaped, while leaf/compress match
//! Plonky3 `PaddingFreeSponge` + `TruncatedPermutation` (same as BabyBear Poseidon trees).

use p3_commit::ExtensionMmcs;
use p3_field::extension::BinomialExtensionField;
use p3_field::{Field, PrimeCharacteristicRing, PrimeField32};
use p3_merkle_tree::MerkleTreeMmcs;
use p3_mersenne_31::{default_mersenne31_poseidon2_16, Mersenne31, Poseidon2Mersenne31};
#[cfg(test)]
use p3_symmetric::Permutation;
use p3_symmetric::{
    CryptographicHasher, PaddingFreeSponge, PseudoCompressionFunction, TruncatedPermutation,
};

type Val = Mersenne31;
type Challenge = BinomialExtensionField<Val, 3>;

/// Poseidon2 width-16 permutation (Plonky3 default M31 RC tables).
pub type Poseidon2Perm16 = Poseidon2Mersenne31<16>;

/// Field limbs per Poseidon Merkle digest (packed into 32 bytes on the wire).
pub const POSEIDON_DIGEST_LIMBS: usize = 8;
/// Sponge rate (= digest limb count).
pub const POSEIDON_RATE: usize = 8;

/// Leaf / row hasher: sponge WIDTH=16, RATE=8, OUT=8 field limbs.
pub type PoseidonFieldHash =
    PaddingFreeSponge<Poseidon2Perm16, 16, { POSEIDON_RATE }, { POSEIDON_DIGEST_LIMBS }>;
/// Binary compress: truncated perm over 2×8 limbs.
pub type PoseidonCompress = TruncatedPermutation<Poseidon2Perm16, 2, { POSEIDON_DIGEST_LIMBS }, 16>;

/// Pack 8×M31 into a 32-byte wire digest (little-endian canonical u32 each).
pub fn pack_digest(limbs: [Mersenne31; POSEIDON_DIGEST_LIMBS]) -> [u8; 32] {
    let mut out = [0u8; 32];
    for (i, limb) in limbs.iter().enumerate() {
        out[i * 4..(i + 1) * 4].copy_from_slice(&limb.as_canonical_u32().to_le_bytes());
    }
    out
}

/// Unpack a 32-byte wire digest into 8×M31.
pub fn unpack_digest(bytes: [u8; 32]) -> [Mersenne31; POSEIDON_DIGEST_LIMBS] {
    let mut limbs = [Mersenne31::ZERO; POSEIDON_DIGEST_LIMBS];
    for (i, limb) in limbs.iter_mut().enumerate() {
        let mut b = [0u8; 4];
        b.copy_from_slice(&bytes[i * 4..(i + 1) * 4]);
        *limb = Mersenne31::new(u32::from_le_bytes(b));
    }
    limbs
}

/// Field hasher that emits packed `[u8; 32]` digests for MerkleTreeMmcs.
#[derive(Clone)]
pub struct PoseidonPackedFieldHash {
    inner: PoseidonFieldHash,
}

impl PoseidonPackedFieldHash {
    pub fn new(perm: Poseidon2Perm16) -> Self {
        Self {
            inner: PoseidonFieldHash::new(perm),
        }
    }
}

impl CryptographicHasher<Val, [u8; 32]> for PoseidonPackedFieldHash {
    fn hash_iter<I>(&self, input: I) -> [u8; 32]
    where
        I: IntoIterator<Item = Val>,
    {
        pack_digest(self.inner.hash_iter(input))
    }
}

/// Binary compress over packed digests (unpack → TruncatedPermutation → pack).
#[derive(Clone)]
pub struct PoseidonPackedCompress {
    inner: PoseidonCompress,
}

impl PoseidonPackedCompress {
    pub fn new(perm: Poseidon2Perm16) -> Self {
        Self {
            inner: PoseidonCompress::new(perm),
        }
    }
}

impl PseudoCompressionFunction<[u8; 32], 2> for PoseidonPackedCompress {
    fn compress(&self, input: [[u8; 32]; 2]) -> [u8; 32] {
        let left = unpack_digest(input[0]);
        let right = unpack_digest(input[1]);
        pack_digest(self.inner.compress([left, right]))
    }
}

/// Production ValMmcs: Poseidon2 sponge/compress with packed `[u8; 32]` digests.
pub type PoseidonValMmcs =
    MerkleTreeMmcs<Val, u8, PoseidonPackedFieldHash, PoseidonPackedCompress, 2, 32>;
pub type PoseidonChallengeMmcs = ExtensionMmcs<Val, Challenge, PoseidonValMmcs>;

/// Field-native (unpacked) ValMmcs — used by isolated smoke tests / migration docs.
#[allow(dead_code)]
pub type PoseidonFieldValMmcs = MerkleTreeMmcs<
    <Val as Field>::Packing,
    <Val as Field>::Packing,
    PoseidonFieldHash,
    PoseidonCompress,
    2,
    8,
>;

/// Builds production Poseidon ValMmcs (`cap_height = 0`).
pub fn poseidon_val_mmcs() -> PoseidonValMmcs {
    let perm = default_mersenne31_poseidon2_16();
    let hash = PoseidonPackedFieldHash::new(perm.clone());
    let compress = PoseidonPackedCompress::new(perm);
    PoseidonValMmcs::new(hash, compress, 0)
}

/// Builds ChallengeMmcs wrapping [`poseidon_val_mmcs`].
pub fn poseidon_challenge_mmcs() -> PoseidonChallengeMmcs {
    PoseidonChallengeMmcs::new(poseidon_val_mmcs())
}

/// Leaf digest matching production ValMmcs.
pub fn hash_val_leaf_poseidon_mmcs(row: &[Mersenne31]) -> [u8; 32] {
    PoseidonPackedFieldHash::new(default_mersenne31_poseidon2_16()).hash_iter(row.iter().copied())
}

/// Binary compress matching production ValMmcs.
pub fn compress_digests_poseidon_mmcs(left: [u8; 32], right: [u8; 32]) -> [u8; 32] {
    PoseidonPackedCompress::new(default_mersenne31_poseidon2_16()).compress([left, right])
}

/// Pre-permutation sponge states for a leaf row (RATE=8 overwrite absorb).
///
/// Each returned state is the width-16 input to one Poseidon2 perm in the sponge.
/// Host-only helper for tests (group AIR is compress-only; leaf hash uses
/// [`hash_val_leaf_poseidon_mmcs`]).
#[cfg(test)]
pub fn poseidon_sponge_leaf_perm_inputs(row: &[Mersenne31]) -> Vec<[Mersenne31; 16]> {
    let perm = default_mersenne31_poseidon2_16();
    let mut state = [Mersenne31::ZERO; 16];
    let mut inputs = Vec::new();
    let mut input = row.iter().copied();
    'outer: loop {
        for i in 0..POSEIDON_RATE {
            if let Some(x) = input.next() {
                state[i] = x;
            } else {
                if i != 0 {
                    inputs.push(state);
                }
                break 'outer;
            }
        }
        inputs.push(state);
        perm.permute_mut(&mut state);
    }
    inputs
}

/// Number of Poseidon2 perms in the leaf sponge for this row width.
#[cfg(test)]
pub fn poseidon_leaf_perm_count(leaf_width: usize) -> usize {
    if leaf_width == 0 {
        0
    } else {
        leaf_width.div_ceil(POSEIDON_RATE)
    }
}

/// Compress perm input state: `left ‖ right` (8+8 limbs).
pub fn poseidon_compress_perm_input(left: [u8; 32], right: [u8; 32]) -> [Mersenne31; 16] {
    let l = unpack_digest(left);
    let r = unpack_digest(right);
    let mut state = [Mersenne31::ZERO; 16];
    state[..8].copy_from_slice(&l);
    state[8..].copy_from_slice(&r);
    state
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_commit::{BatchOpeningRef, Mmcs};
    use p3_matrix::dense::RowMajorMatrix;
    use p3_matrix::Dimensions;

    #[test]
    fn pack_unpack_roundtrip() {
        let limbs = [
            Mersenne31::from_u32(1),
            Mersenne31::from_u32(2),
            Mersenne31::from_u32(3),
            Mersenne31::from_u32(4),
            Mersenne31::from_u32(5),
            Mersenne31::from_u32(6),
            Mersenne31::from_u32(7),
            Mersenne31::from_u32(8),
        ];
        assert_eq!(unpack_digest(pack_digest(limbs)), limbs);
    }

    #[test]
    fn poseidon_val_mmcs_commit_open_roundtrip() {
        let mmcs = poseidon_val_mmcs();
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
    fn packed_leaf_matches_mmcs_open() {
        let mmcs = poseidon_val_mmcs();
        let row: Vec<_> = (0..3).map(|i| Mersenne31::from_u32(i + 1)).collect();
        // Single-row matrix → leaf digest is the commitment root.
        let mat = RowMajorMatrix::new(row.clone(), 3);
        let (commit, data) = mmcs.commit(vec![mat]);
        let batch = mmcs.open_batch(0, &data);
        let leaf = hash_val_leaf_poseidon_mmcs(&row);
        assert_eq!(leaf, *commit.roots().first().expect("root"));
        assert!(batch.opening_proof.is_empty());
    }

    #[test]
    fn sponge_witness_replays_p3_hash() {
        let perm = default_mersenne31_poseidon2_16();
        for width in [3usize, 8, 9, 12, 21, 48] {
            let row: Vec<_> = (0..width)
                .map(|i| Mersenne31::from_u32(i as u32 * 5 + 7))
                .collect();
            let expected = hash_val_leaf_poseidon_mmcs(&row);
            let inputs = poseidon_sponge_leaf_perm_inputs(&row);
            assert_eq!(inputs.len(), poseidon_leaf_perm_count(width));
            let mut state = [Mersenne31::ZERO; 16];
            for inp in &inputs {
                state = *inp;
                perm.permute_mut(&mut state);
            }
            let digest = pack_digest(state[..8].try_into().unwrap());
            assert_eq!(digest, expected, "width {width}");
        }
    }

    #[test]
    fn sponge_perm_count_matches_helper() {
        assert_eq!(poseidon_leaf_perm_count(3), 1);
        assert_eq!(poseidon_leaf_perm_count(8), 1);
        assert_eq!(poseidon_leaf_perm_count(9), 2);
        assert_eq!(poseidon_leaf_perm_count(48), 6);
        assert_eq!(
            poseidon_sponge_leaf_perm_inputs(&[Mersenne31::ONE; 3]).len(),
            1
        );
        assert_eq!(
            poseidon_sponge_leaf_perm_inputs(&[Mersenne31::ONE; 48]).len(),
            6
        );
    }
}

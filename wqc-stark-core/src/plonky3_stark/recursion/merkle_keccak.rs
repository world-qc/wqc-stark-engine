//! ValMmcs-compatible Keccak-256 Merkle path helpers (AggregationAir LDE tests / Keccak groups).
//!
//! Production [`crate::plonky3_stark::config::ValMmcs`] uses Poseidon2; these Keccak helpers
//! remain for Keccak group-fold AIRs and legacy path STARKs.

#[cfg(test)]
use p3_field::PrimeField32;
use p3_keccak::Keccak256Hash;
use p3_mersenne_31::Mersenne31;
use p3_symmetric::{
    CompressionFunctionFromHasher, CryptographicHasher, PseudoCompressionFunction,
    SerializingHasher,
};

use crate::plonky3_stark::aggregation_air::AGG_WIDTH;

/// Typical sibling count for AggregationAir LDE height 8, binary tree, cap_height 0.
pub const AGG_LDE_MERKLE_DEPTH: usize = 3;

type KeccakFieldHash = SerializingHasher<Keccak256Hash>;
type KeccakCompress = CompressionFunctionFromHasher<Keccak256Hash, 2, 32>;

fn field_hash() -> KeccakFieldHash {
    KeccakFieldHash::new(Keccak256Hash {})
}

fn compress_fn() -> KeccakCompress {
    KeccakCompress::new(Keccak256Hash {})
}

/// Leaf digest of a single AggregationAir-width LDE row (Keccak ValMmcs leaf hash).
pub fn hash_lde_leaf(row: &[Mersenne31]) -> [u8; 32] {
    debug_assert_eq!(row.len(), AGG_WIDTH);
    hash_val_leaf_keccak(row)
}

/// Keccak leaf digest of an arbitrary-width M31 row (legacy / Keccak group AIRs).
pub fn hash_val_leaf_keccak(row: &[Mersenne31]) -> [u8; 32] {
    field_hash().hash_iter(row.iter().copied())
}

/// Production PCS leaf digest (Poseidon2 packed ValMmcs).
pub fn hash_val_leaf(row: &[Mersenne31]) -> [u8; 32] {
    crate::plonky3_stark::config_poseidon::hash_val_leaf_poseidon_mmcs(row)
}

/// Binary Keccak-256 compress: `H(left || right)`.
pub fn compress_digests_keccak(left: [u8; 32], right: [u8; 32]) -> [u8; 32] {
    compress_fn().compress([left, right])
}

/// Production PCS binary compress (Poseidon2 packed).
pub fn compress_digests(left: [u8; 32], right: [u8; 32]) -> [u8; 32] {
    crate::plonky3_stark::config_poseidon::compress_digests_poseidon_mmcs(left, right)
}

/// Recomputes the Merkle root for a binary path (N=2, no injection, cap_height=0).
///
/// Uses production Poseidon ValMmcs compress.
pub fn merkle_root_from_path(
    leaf_digest: [u8; 32],
    siblings: &[[u8; 32]],
    mut index: usize,
) -> [u8; 32] {
    let mut digest = leaf_digest;
    for sibling in siblings {
        let pos = index % 2;
        digest = if pos == 0 {
            compress_digests(digest, *sibling)
        } else {
            compress_digests(*sibling, digest)
        };
        index /= 2;
    }
    digest
}

/// Keccak Merkle root replay (Keccak group / legacy tests).
pub fn merkle_root_from_path_keccak(
    leaf_digest: [u8; 32],
    siblings: &[[u8; 32]],
    mut index: usize,
) -> [u8; 32] {
    let mut digest = leaf_digest;
    for sibling in siblings {
        let pos = index % 2;
        digest = if pos == 0 {
            compress_digests_keccak(digest, *sibling)
        } else {
            compress_digests_keccak(*sibling, digest)
        };
        index /= 2;
    }
    digest
}

/// Verifies an AggregationAir-sized PCS Merkle opening against a commitment root.
pub fn verify_agg_merkle_path(
    lde_row: &[Mersenne31],
    siblings: &[[u8; 32]],
    index: usize,
    expected_root: &[u8; 32],
) -> bool {
    if lde_row.len() != AGG_WIDTH {
        return false;
    }
    if siblings.len() > AGG_LDE_MERKLE_DEPTH + 2 {
        return false;
    }
    let leaf = hash_val_leaf(lde_row);
    let root = merkle_root_from_path(leaf, siblings, index);
    &root == expected_root
}

#[cfg(test)]
fn m31_row_to_leaf_bytes(row: &[Mersenne31]) -> Vec<u8> {
    use p3_field::PrimeField32;
    let mut out = Vec::with_capacity(row.len() * 4);
    for v in row {
        out.extend_from_slice(&v.as_canonical_u32().to_le_bytes());
    }
    out
}

#[cfg(test)]
fn keccak256_bytes(input: &[u8]) -> [u8; 32] {
    Keccak256Hash {}.hash_iter(input.iter().copied())
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_commit::{BatchOpeningRef, Mmcs, Pcs};
    use p3_field::PrimeCharacteristicRing;
    use p3_matrix::{Dimensions, Matrix};
    use p3_uni_stark::StarkGenericConfig;

    use crate::aggregation::CHILD_HASH_LEN;
    use crate::air::pad_air_matrix_for_uni_stark;
    use crate::plonky3_stark::aggregation::build_agg_matrix;
    use crate::plonky3_stark::config::devnet_circle_config;

    #[test]
    fn leaf_hash_keccak_matches_native_bytes() {
        let row: Vec<_> = (0..AGG_WIDTH)
            .map(|i| Mersenne31::from_u32(i as u32))
            .collect();
        let a = hash_val_leaf_keccak(&row);
        let b = keccak256_bytes(&m31_row_to_leaf_bytes(&row));
        assert_eq!(a, b);
    }

    #[test]
    fn path_matches_val_mmcs_open_batch() {
        let matrix = pad_air_matrix_for_uni_stark(build_agg_matrix(
            [1u8; CHILD_HASH_LEN],
            [2u8; CHILD_HASH_LEN],
        ));
        let config = devnet_circle_config();
        let pcs = config.pcs();
        let domain = <crate::plonky3_stark::config::Pcs as Pcs<
            crate::plonky3_stark::config::Challenge,
            crate::plonky3_stark::config::Challenger,
        >>::natural_domain_for_degree(pcs, matrix.height());
        let (comm, prover_data) = <crate::plonky3_stark::config::Pcs as Pcs<
            crate::plonky3_stark::config::Challenge,
            crate::plonky3_stark::config::Challenger,
        >>::commit(pcs, vec![(domain, matrix)]);
        let index = 0usize;
        let batch = pcs.mmcs.open_batch(index, &prover_data);
        let dims: Vec<Dimensions> = pcs
            .mmcs
            .get_matrices(&prover_data)
            .iter()
            .map(|m| Dimensions {
                width: m.width(),
                height: m.height(),
            })
            .collect();
        pcs.mmcs
            .verify_batch(
                &comm,
                &dims,
                index,
                BatchOpeningRef::new(&batch.opened_values, &batch.opening_proof),
            )
            .expect("mmcs verify");

        let row = &batch.opened_values[0];
        let siblings = &batch.opening_proof;
        let root = *comm.roots().first().expect("root");
        assert!(verify_agg_merkle_path(row, siblings, index, &root));
        assert_eq!(siblings.len(), AGG_LDE_MERKLE_DEPTH);
    }
}

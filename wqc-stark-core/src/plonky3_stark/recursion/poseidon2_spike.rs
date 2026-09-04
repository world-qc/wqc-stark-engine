//! Poseidon2 width-16 constant shared by M4b group AIR (`poseidon2_perm_air`,
//! `poseidon2_group_m4b`). Originally an E5b spike; production compress-only
//! Poseidon Mmcs groups live in those modules.
//!
//! Wire encode → decode for Poseidon `MmcsGroupFoldProof` is covered by
//! `transcript_v6::tests::m4c_group_fold_poseidon_codec_roundtrip` (prove → encode
//! → decode). Prove/verify path roundtrips live in `poseidon2_group_m4b` tests.

/// Poseidon2 width for M31 Merkle compression / group AIR.
pub const POSEIDON2_WIDTH: usize = 16;

#[cfg(test)]
mod tests {
    use p3_field::{PrimeCharacteristicRing, PrimeField32};
    use p3_mersenne_31::{default_mersenne31_poseidon2_16, Mersenne31};
    use p3_symmetric::Permutation;

    use super::super::keccak_f_native::KECCAK_ROUNDS;
    use super::POSEIDON2_WIDTH;

    const KECCAK_AIR_COLS_PER_ROUND: usize = super::super::keccak256_air::SPONGE_WIDTH;
    const POSEIDON2_ROUNDS_WIDTH16: usize = 23;

    fn poseidon2_compress32(left: [u8; 32], right: [u8; 32]) -> [u8; 32] {
        let perm = default_mersenne31_poseidon2_16();
        let mut state = [Mersenne31::ZERO; POSEIDON2_WIDTH];
        for (i, chunk) in left[..16]
            .chunks(4)
            .chain(right[..16].chunks(4))
            .enumerate()
            .take(8)
        {
            let mut b = [0u8; 4];
            b.copy_from_slice(chunk);
            state[i] = Mersenne31::new(u32::from_le_bytes(b));
        }
        perm.permute_mut(&mut state);
        let mut out = [0u8; 32];
        for (i, limb) in state.iter().take(8).enumerate() {
            out[i * 4..(i + 1) * 4].copy_from_slice(&limb.as_canonical_u32().to_le_bytes());
        }
        out
    }

    fn estimated_perm_air_cells_keccak_vs_poseidon2(num_perms: usize) -> (usize, usize) {
        let keccak_cells = num_perms * KECCAK_ROUNDS * KECCAK_AIR_COLS_PER_ROUND;
        let poseidon_cells = num_perms * POSEIDON2_ROUNDS_WIDTH16 * POSEIDON2_WIDTH;
        (keccak_cells, poseidon_cells)
    }

    #[test]
    fn poseidon2_compress32_deterministic() {
        let a = [1u8; 32];
        let b = [2u8; 32];
        let d1 = poseidon2_compress32(a, b);
        let d2 = poseidon2_compress32(a, b);
        assert_eq!(d1, d2);
        assert_ne!(d1, [0u8; 32]);
    }

    #[test]
    fn poseidon2_air_cell_estimate_favorable_vs_keccak() {
        let (keccak, poseidon) = estimated_perm_air_cells_keccak_vs_poseidon2(21);
        assert!(
            poseidon < keccak,
            "poseidon cells {poseidon} should be < keccak {keccak}"
        );
    }
}

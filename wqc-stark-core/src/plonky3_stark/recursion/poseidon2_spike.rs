//! E5b Poseidon2 spike — recursion-friendly hash to replace Keccak-in-STARK in M4b Mmcs groups.
//!
//! **Problem:** leaf PCS `mmcs_groups` (~97% of nested STARK bytes) prove Keccak-256 sponges
//! inside uni-STARKs (`keccak256_air.rs` / `fri_mmcs_group_m4b.rs`). Each group STARK carries
//! a wide bit-level Keccak-f[1600] trace.
//!
//! **Target:** Poseidon2 sponge over Mersenne31 (`p3_mersenne_31::Poseidon2Mersenne31`) with a
//! compact AIR, then wire-compatible `PoseidonGroupFoldProof` parallel to `KeccakGroupFoldProof`.
//!
//! **Status:** native perm + AIR cell accounting only; no production AIR yet.

#![allow(dead_code)] // spike exports used by tests and future M4b integration

use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_mersenne_31::{default_mersenne31_poseidon2_16, Mersenne31, Poseidon2Mersenne31};
use p3_symmetric::Permutation;

use super::keccak_f_native::KECCAK_ROUNDS;

/// Poseidon2 width for M31 Merkle compression spike.
pub const POSEIDON2_WIDTH: usize = 16;

/// Estimated Keccak-f round columns in the in-circuit sponge AIR (see `keccak_f_air`).
pub const KECCAK_AIR_COLS_PER_ROUND: usize = super::keccak256_air::SPONGE_WIDTH;

/// Poseidon2 width-16 M31: 4 external + 22 internal + 4 external rounds (default RC tables).
pub const POSEIDON2_ROUNDS_WIDTH16: usize = 30;

/// Native 32-byte digest via Poseidon2 sponge (spike — not consensus wire format).
pub fn poseidon2_compress32(left: [u8; 32], right: [u8; 32]) -> [u8; 32] {
    let perm = default_mersenne31_poseidon2_16();
    let mut state = [Mersenne31::ZERO; POSEIDON2_WIDTH];
    for (i, chunk) in left.chunks(4).chain(right.chunks(4)).enumerate().take(8) {
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

/// Rough AIR cell budget: one Keccak perm vs one Poseidon2 perm (order-of-magnitude spike metric).
pub fn estimated_perm_air_cells_keccak_vs_poseidon2(num_perms: usize) -> (usize, usize) {
    let keccak_cells = num_perms * KECCAK_ROUNDS * KECCAK_AIR_COLS_PER_ROUND;
    let poseidon_cells = num_perms * POSEIDON2_ROUNDS_WIDTH16 * POSEIDON2_WIDTH;
    (keccak_cells, poseidon_cells)
}

#[allow(dead_code)]
type Poseidon2M31_16 = Poseidon2Mersenne31<POSEIDON2_WIDTH>;

#[cfg(test)]
mod tests {
    use super::*;

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
        // Typical ValMmcs path depth ~20 → ~21 Keccak perms per Merkle path statement.
        let (keccak, poseidon) = estimated_perm_air_cells_keccak_vs_poseidon2(21);
        assert!(
            poseidon < keccak,
            "spike expects Poseidon2 AIR << Keccak AIR (poseidon={poseidon}, keccak={keccak})"
        );
        // Sanity: Keccak bit AIR is orders of magnitude wider than field Poseidon2.
        assert!(keccak > poseidon * 10);
    }
}

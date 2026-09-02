//! FRI ValMmcs / ChallengeMmcs Merkle migration — Keccak wire → Poseidon2 native.
//!
//! ## Status
//!
//! Production [`crate::plonky3_stark::config::WqcStarkConfig`] uses packed Poseidon2
//! ValMmcs (`config_poseidon`: `PaddingFreeSponge` + `TruncatedPermutation`, digests
//! packed as `[u8; 32]`). M4c group STARKs default to Poseidon and verify against PCS
//! openings directly (no spike re-hash). Fiat–Shamir challenger hash remains Keccak.

use super::mmcs_group_fold::{mmcs_group_hash_kind, MmcsGroupHashKind};

/// Which Merkle / group-hash mode the M4c prove path uses.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MmcsMerkleMode {
    /// Keccak Mmcs groups (env override `WQC_PCS_MMCS_HASH=keccak`).
    Keccak,
    /// Poseidon2 group STARKs + Poseidon2 PCS Merkle (production).
    PoseidonNative,
}

/// Active Mmcs Merkle mode from env (Poseidon native by default).
pub fn mmcs_merkle_mode() -> MmcsMerkleMode {
    match mmcs_group_hash_kind() {
        MmcsGroupHashKind::Keccak => MmcsMerkleMode::Keccak,
        MmcsGroupHashKind::Poseidon => MmcsMerkleMode::PoseidonNative,
    }
}

/// True when PCS Merkle and group fold both use Poseidon2.
pub fn poseidon_native_mmcs_active() -> bool {
    matches!(mmcs_merkle_mode(), MmcsMerkleMode::PoseidonNative)
}

/// Legacy name — spike mode retired; aliases native Poseidon.
pub fn poseidon_group_spike_active() -> bool {
    false
}

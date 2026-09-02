//! FRI ValMmcs / ChallengeMmcs Merkle migration — Keccak wire → Poseidon2 group fold.
//!
//! ## Phases
//!
//! 1. **Spike (current default with `poseidon-mmcs`)** — Plonky3 PCS Merkle stays Keccak
//!    (`config::ValMmcs`). M4c group STARKs may use Poseidon2 perm AIR
//!    (`WQC_PCS_MMCS_HASH=poseidon`). Group verify uses
//!    [`super::mmcs_group_fold::poseidon_spike_statements`] (Poseidon leaf hash + compress,
//!    Keccak siblings as opaque 32 B). Host bind still replays Keccak roots from the
//!    uni-STARK proof commitments.
//! 2. **Dual-bind** — Poseidon group + Keccak digest replay both required at verify
//!    (today's behaviour once `poseidon-mmcs` e2e passes).
//! 3. **Native Merkle (scaffolded)** — field-native Poseidon2 `ValMmcs` /
//!    `ChallengeMmcs` in [`crate::plonky3_stark::config_poseidon`] (8×M31 digests,
//!    `PaddingFreeSponge` + `TruncatedPermutation`). Isolated commit/open smoke exists;
//!    production `WqcStarkConfig` still Keccak until RecAgg / leaf PCS wire digests migrate.
//!    Then spike conversion is removed and group statements match PCS openings.

use super::mmcs_group_fold::{mmcs_group_hash_kind, MmcsGroupHashKind};

/// Which Merkle / group-hash mode the M4c prove path uses.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MmcsMerkleMode {
    /// Default production: Keccak Mmcs groups + Keccak PCS Merkle tree.
    Keccak,
    /// Poseidon2 group STARKs; PCS Merkle still Keccak (spike statements at verify).
    PoseidonGroupSpike,
    /// Field-native Poseidon2 PCS Merkle (Phase 3). Not selected by env yet —
    /// see [`crate::plonky3_stark::config_poseidon`].
    PoseidonNative,
}

/// Active Mmcs Merkle mode from features + env (spike / Keccak only today).
pub fn mmcs_merkle_mode() -> MmcsMerkleMode {
    match mmcs_group_hash_kind() {
        MmcsGroupHashKind::Keccak => MmcsMerkleMode::Keccak,
        MmcsGroupHashKind::Poseidon => MmcsMerkleMode::PoseidonGroupSpike,
    }
}

/// True when group prove uses Poseidon2 but PCS commitments remain Keccak.
pub fn poseidon_group_spike_active() -> bool {
    matches!(mmcs_merkle_mode(), MmcsMerkleMode::PoseidonGroupSpike)
}

/// True when a future env/feature selects native Poseidon PCS Merkle.
///
/// Currently always `false` — production config remains Keccak. Use
/// [`crate::plonky3_stark::config_poseidon`] for isolated experiments.
pub fn poseidon_native_mmcs_active() -> bool {
    false
}

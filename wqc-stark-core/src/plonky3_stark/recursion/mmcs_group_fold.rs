//! M4b/M4c Mmcs group fold — Keccak vs Poseidon2 dispatch + wire tags.

use super::fri_mmcs_group_m4b::KeccakGroupFoldProof;
use super::poseidon2_group_m4b::PoseidonGroupFoldProof;

/// Per-group hash tag in [`LEAF_MMCS_FOLD_V4`] wire encoding.
pub const MMCS_GROUP_HASH_KECCAK: u8 = 0;
pub const MMCS_GROUP_HASH_POSEIDON: u8 = 1;

/// Which in-circuit hash backs grouped Mmcs path STARKs.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[repr(u8)]
pub enum MmcsGroupHashKind {
    Keccak = MMCS_GROUP_HASH_KECCAK,
    /// Default: production ValMmcs is Poseidon2 packed.
    #[default]
    Poseidon = MMCS_GROUP_HASH_POSEIDON,
}

impl MmcsGroupHashKind {
    pub fn from_u8(v: u8) -> Option<Self> {
        match v {
            MMCS_GROUP_HASH_KECCAK => Some(Self::Keccak),
            MMCS_GROUP_HASH_POSEIDON => Some(Self::Poseidon),
            _ => None,
        }
    }
}

/// Homogeneous Mmcs group STARK (Keccak sponge or Poseidon2 perm segments).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MmcsGroupFoldProof {
    Keccak(KeccakGroupFoldProof),
    Poseidon(PoseidonGroupFoldProof),
}

impl MmcsGroupFoldProof {
    pub fn hash_kind(&self) -> MmcsGroupHashKind {
        match self {
            Self::Keccak(_) => MmcsGroupHashKind::Keccak,
            Self::Poseidon(_) => MmcsGroupHashKind::Poseidon,
        }
    }

    pub fn path_count(&self) -> u32 {
        match self {
            Self::Keccak(g) => g.path_count,
            Self::Poseidon(g) => g.path_count,
        }
    }

    pub fn depth(&self) -> u32 {
        match self {
            Self::Keccak(g) => g.depth,
            Self::Poseidon(g) => g.depth,
        }
    }

    pub fn leaf_width(&self) -> u32 {
        match self {
            Self::Keccak(g) => g.leaf_width,
            Self::Poseidon(g) => g.leaf_width,
        }
    }

    pub fn group_stark_len(&self) -> usize {
        match self {
            Self::Keccak(g) => g.group_stark.len(),
            Self::Poseidon(g) => g.group_stark.len(),
        }
    }

    pub fn keccak(&self) -> Option<&KeccakGroupFoldProof> {
        match self {
            Self::Keccak(g) => Some(g),
            Self::Poseidon(_) => None,
        }
    }

    pub fn poseidon(&self) -> Option<&PoseidonGroupFoldProof> {
        match self {
            Self::Poseidon(g) => Some(g),
            Self::Keccak(_) => None,
        }
    }
}

/// Env override for M4c group prove (`WQC_PCS_MMCS_HASH=keccak` forces Keccak groups).
pub const PCS_MMCS_HASH_ENV: &str = "WQC_PCS_MMCS_HASH";

/// Active Mmcs group hash. Defaults to Poseidon (matches production ValMmcs).
pub fn mmcs_group_hash_kind() -> MmcsGroupHashKind {
    if std::env::var(PCS_MMCS_HASH_ENV)
        .map(|v| v.eq_ignore_ascii_case("keccak"))
        .unwrap_or(false)
    {
        return MmcsGroupHashKind::Keccak;
    }
    MmcsGroupHashKind::Poseidon
}

/// True when the Poseidon2 group can prove this homogeneous width.
pub fn poseidon_group_width_supported(leaf_width: usize) -> bool {
    super::merkle_poseidon2::poseidon_m4b_width_eligible(leaf_width)
}

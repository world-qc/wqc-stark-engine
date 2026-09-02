//! M4b/M4c Mmcs group fold — Keccak vs Poseidon2 dispatch + wire tags.

use super::fri_mmcs_group_m4b::{KeccakGroupFoldProof, MmcsPathStatement};
use super::merkle_poseidon2::{hash_val_leaf_poseidon, merkle_root_from_path_poseidon};
use super::poseidon2_group_m4b::PoseidonGroupFoldProof;
use super::poseidon2_spike::POSEIDON2_WIDTH;

/// Per-group hash tag in [`LEAF_MMCS_FOLD_V4`] wire encoding.
pub const MMCS_GROUP_HASH_KECCAK: u8 = 0;
pub const MMCS_GROUP_HASH_POSEIDON: u8 = 1;

/// Which in-circuit hash backs grouped Mmcs path STARKs.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[repr(u8)]
pub enum MmcsGroupHashKind {
    #[default]
    Keccak = MMCS_GROUP_HASH_KECCAK,
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

/// Env / feature dispatch for M4c group prove (`WQC_PCS_MMCS_HASH=poseidon`).
pub const PCS_MMCS_HASH_ENV: &str = "WQC_PCS_MMCS_HASH";

pub fn mmcs_group_hash_kind() -> MmcsGroupHashKind {
    #[cfg(feature = "poseidon-mmcs")]
    {
        if std::env::var(PCS_MMCS_HASH_ENV)
            .map(|v| v.eq_ignore_ascii_case("poseidon"))
            .unwrap_or(false)
        {
            return MmcsGroupHashKind::Poseidon;
        }
    }
    MmcsGroupHashKind::Keccak
}

/// True when the Poseidon2 group prototype can prove this homogeneous width.
pub fn poseidon_group_width_supported(leaf_width: usize) -> bool {
    super::merkle_poseidon2::poseidon_m4b_width_eligible(leaf_width)
}

/// Spike-only: same opening shape, Poseidon-native digests (siblings kept as opaque 32 B).
pub fn mmcs_path_stmt_poseidon_spike(stmt: &MmcsPathStatement) -> Result<MmcsPathStatement, String> {
    if !poseidon_group_width_supported(stmt.row.len()) {
        return Err(format!(
            "poseidon group leaf_width {} > {POSEIDON2_WIDTH}",
            stmt.row.len()
        ));
    }
    let leaf = hash_val_leaf_poseidon(&stmt.row);
    let root = merkle_root_from_path_poseidon(leaf, &stmt.siblings, stmt.index);
    Ok(MmcsPathStatement {
        row: stmt.row.clone(),
        siblings: stmt.siblings.clone(),
        index: stmt.index,
        root,
    })
}

/// Convert a homogeneous chunk for Poseidon group prove (benchmark / `poseidon-mmcs` mode).
pub fn poseidon_spike_statements(stmts: &[MmcsPathStatement]) -> Result<Vec<MmcsPathStatement>, String> {
    stmts.iter().map(mmcs_path_stmt_poseidon_spike).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_field::PrimeCharacteristicRing;
    use p3_mersenne_31::Mersenne31;

    #[test]
    fn poseidon_spike_stmt_differs_root_from_keccak_tree() {
        let row = vec![
            Mersenne31::from_u32(1),
            Mersenne31::from_u32(2),
            Mersenne31::from_u32(3),
        ];
        let keccak_root = [9u8; 32];
        let stmt = MmcsPathStatement {
            row,
            siblings: vec![[7u8; 32]],
            index: 0,
            root: keccak_root,
        };
        let p = mmcs_path_stmt_poseidon_spike(&stmt).expect("convert");
        assert_ne!(p.root, keccak_root);
        assert_eq!(p.row, stmt.row);
    }
}

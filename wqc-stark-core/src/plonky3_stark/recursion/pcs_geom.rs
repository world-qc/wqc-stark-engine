//! Shared PCS / FRI geometry for AggregationAir and leaf STARKs (R3-M3e).

use p3_uni_stark::{Proof, StarkGenericConfig};

use crate::plonky3_stark::config::{devnet_circle_config, WqcStarkConfig};
use crate::plonky3_stark::shot_sampling_air::SHOT_SAMPLING_AIR_WIDTH;
use crate::trace_spec::AIR_WIDTH;

use super::fri_mmcs_path::FRI_MMCS_MAX_DEPTH;

pub use crate::plonky3_stark::distribution_air::{
    born_distribution_width, born_num_outcomes_from_width, born_recursion_outcomes_ok,
    validate_born_recursion_outcomes, validate_born_recursion_width, BORN_RECURSION_MAX_OUTCOMES,
    BORN_RECURSION_MAX_TRACE_WIDTH,
};

/// Max rows in a multi-chunk quotient [`FriChalBatchPathProof`] (chunks + optional concat).
pub const MAX_QUOT_BATCH_LEAF_ROWS: usize = 64;
/// Limited by 2-block Keccak sponge (`≤ 2·136` bytes ⇒ 68 M31). Born K≤21.
pub const LEAF_DEEP_RO_MAX_WIDTH: usize = BORN_RECURSION_MAX_TRACE_WIDTH;

/// Unitary / traj-marginal / shot fixed widths.
pub const UNITARY_TRACE_WIDTH: usize = AIR_WIDTH; // 21
pub const TRAJ_MARGINAL_TRACE_WIDTH: usize = 2 + 3 * 2 + 1; // K=2 → 9
pub const SHOT_TRACE_WIDTH: usize = SHOT_SAMPLING_AIR_WIDTH; // 26

/// PCS geometry derived from a uni-STARK proof + known trace width.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PcsGeom {
    pub trace_width: usize,
    pub degree_bits: usize,
    pub log_blowup: usize,
    pub num_queries: usize,
    pub max_mmcs_depth: usize,
    pub max_fold_rounds: usize,
}

impl PcsGeom {
    pub fn from_proof(proof: &Proof<WqcStarkConfig>, trace_width: usize) -> Self {
        let config = devnet_circle_config();
        let log_blowup = config.pcs().fri_params.log_blowup;
        let num_queries = config.pcs().fri_params.num_queries;
        // LDE height = 2^(degree_bits + log_blowup); Merkle depth ≤ that log.
        let max_mmcs_depth = (proof.degree_bits + log_blowup).min(FRI_MMCS_MAX_DEPTH);
        // Commit-phase rounds ≈ fri height − blowup; cap generously.
        let max_fold_rounds = proof.degree_bits.saturating_add(2).min(20);
        Self {
            trace_width,
            degree_bits: proof.degree_bits,
            log_blowup,
            num_queries,
            max_mmcs_depth: max_mmcs_depth.max(1),
            max_fold_rounds: max_fold_rounds.max(1),
        }
    }

    pub fn born_width(num_outcomes: usize) -> usize {
        born_distribution_width(num_outcomes)
    }
}

/// Leaf AIR kind for OOD / cert dispatch.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum LeafKind {
    Unitary = 0,
    Born = 1,
    TrajMarginal = 2,
    ShotSampling = 3,
}

impl LeafKind {
    pub fn from_u8(v: u8) -> Option<Self> {
        match v {
            0 => Some(Self::Unitary),
            1 => Some(Self::Born),
            2 => Some(Self::TrajMarginal),
            3 => Some(Self::ShotSampling),
            _ => None,
        }
    }
}

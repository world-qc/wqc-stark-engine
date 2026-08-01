//! Circle STARK configuration (Mersenne31 + Keccak MMCS).
//!
//! # FRI queries and SecurityLevel
//!
//! Orchestrator `security_level` maps to FRI `num_queries` via
//! [`fri_num_queries_for_security_level`]. These counts are an **operational**
//! ladder relative to the historical devnet default ([`DEVNET_FRI_NUM_QUERIES`]);
//! they are **not** calibrated soundness-bit claims.
//!
//! Prove and verify must use the **same** `num_queries`. Until queries are bound
//! into public inputs / transcript, both sides must derive them from the same
//! `security_level` (orch wiring is a follow-on). Existing call sites that use
//! [`devnet_circle_config`] keep `num_queries = 40`.

use core::marker::PhantomData;

use p3_challenger::{HashChallenger, SerializingChallenger32};
use p3_circle::CirclePcs;
use p3_commit::ExtensionMmcs;
use p3_field::extension::BinomialExtensionField;
use p3_fri::FriParameters;
use p3_keccak::Keccak256Hash;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_mersenne_31::Mersenne31;
use p3_symmetric::{CompressionFunctionFromHasher, SerializingHasher};
use p3_uni_stark::StarkConfig;

pub type Val = Mersenne31;
pub type Challenge = BinomialExtensionField<Val, 3>;
pub type ByteHash = Keccak256Hash;
pub type FieldHash = SerializingHasher<ByteHash>;
pub type Compress = CompressionFunctionFromHasher<ByteHash, 2, 32>;
pub type ValMmcs = MerkleTreeMmcs<Val, u8, FieldHash, Compress, 2, 32>;
pub type ChallengeMmcs = ExtensionMmcs<Val, Challenge, ValMmcs>;
pub type Challenger = SerializingChallenger32<Val, HashChallenger<u8, ByteHash, 32>>;
pub type Pcs = CirclePcs<Val, ValMmcs, ChallengeMmcs>;
pub type WqcStarkConfig = StarkConfig<Pcs, Challenge, Challenger>;

/// Legacy / default FRI query count (must match [`devnet_circle_config`]).
///
/// PCS cert aliases (`AGG_FRI_PROVEN_QUERIES` / `LEAF_FRI_PROVEN_QUERIES`) still
/// assume this constant until variable-length certs land.
pub const DEVNET_FRI_NUM_QUERIES: usize = 40;

/// FRI queries for orchestrator `security_level = low`.
pub const FRI_NUM_QUERIES_LOW: usize = 8;
/// FRI queries for orchestrator `security_level = normal`.
pub const FRI_NUM_QUERIES_NORMAL: usize = 16;
/// FRI queries for orchestrator `security_level = high`.
pub const FRI_NUM_QUERIES_HIGH: usize = 32;
/// FRI queries for orchestrator `security_level = ultra` (equals [`DEVNET_FRI_NUM_QUERIES`]).
pub const FRI_NUM_QUERIES_ULTRA: usize = DEVNET_FRI_NUM_QUERIES;

/// Maps orchestrator `security_level` to FRI `num_queries`.
///
/// Unknown / empty levels fall back to [`DEVNET_FRI_NUM_QUERIES`] so existing
/// prove/verify paths remain safe.
pub fn fri_num_queries_for_security_level(level: &str) -> usize {
    match level.trim().to_ascii_lowercase().as_str() {
        "low" => FRI_NUM_QUERIES_LOW,
        "normal" => FRI_NUM_QUERIES_NORMAL,
        "high" => FRI_NUM_QUERIES_HIGH,
        "ultra" => FRI_NUM_QUERIES_ULTRA,
        _ => DEVNET_FRI_NUM_QUERIES,
    }
}

/// Devnet-oriented parameters: modest query count for fast verification.
pub fn devnet_circle_config() -> WqcStarkConfig {
    circle_config_with_blowup(1, DEVNET_FRI_NUM_QUERIES)
}

/// Like [`devnet_circle_config`], but with an explicit FRI query count.
///
/// Callers that experiment with SecurityLevel-mapped queries should prefer this
/// (or [`circle_config_for_security_level`]) and keep prove/verify paired.
pub fn devnet_circle_config_with_queries(num_queries: usize) -> WqcStarkConfig {
    circle_config_with_blowup(1, num_queries)
}

/// Higher blowup for degree-heavy AIRs (R3-M2.5b Keccak sponge).
///
/// `log_blowup = 4` ⇒ blowup 16 ⇒ constraint degree up to 17.
pub fn keccak_circle_config() -> WqcStarkConfig {
    circle_config_with_blowup(4, DEVNET_FRI_NUM_QUERIES)
}

/// Like [`keccak_circle_config`], but with an explicit FRI query count.
pub fn keccak_circle_config_with_queries(num_queries: usize) -> WqcStarkConfig {
    circle_config_with_blowup(4, num_queries)
}

/// Builds a circle STARK config for an orchestrator `security_level`.
pub fn circle_config_for_security_level(level: &str, log_blowup: usize) -> WqcStarkConfig {
    circle_config_with_blowup(log_blowup, fri_num_queries_for_security_level(level))
}

fn circle_config_with_blowup(log_blowup: usize, num_queries: usize) -> WqcStarkConfig {
    let byte_hash = ByteHash {};
    let field_hash = FieldHash::new(byte_hash);
    let compress = Compress::new(byte_hash);
    let val_mmcs = ValMmcs::new(field_hash, compress, 0);
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    let fri_params = FriParameters {
        log_blowup,
        log_final_poly_len: 0,
        max_log_arity: 1,
        num_queries,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: 8,
        mmcs: challenge_mmcs,
    };
    let pcs = Pcs {
        mmcs: val_mmcs,
        fri_params,
        _phantom: PhantomData,
    };
    let challenger = Challenger::from_hasher(vec![], byte_hash);
    WqcStarkConfig::new(pcs, challenger)
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_uni_stark::StarkGenericConfig;

    #[test]
    fn fri_num_queries_for_security_level_table() {
        assert_eq!(fri_num_queries_for_security_level("low"), 8);
        assert_eq!(fri_num_queries_for_security_level("normal"), 16);
        assert_eq!(fri_num_queries_for_security_level("high"), 32);
        assert_eq!(fri_num_queries_for_security_level("ultra"), 40);
        assert_eq!(fri_num_queries_for_security_level("LOW"), 8);
        assert_eq!(fri_num_queries_for_security_level(" Normal "), 16);
        assert_eq!(
            fri_num_queries_for_security_level(""),
            DEVNET_FRI_NUM_QUERIES
        );
        assert_eq!(
            fri_num_queries_for_security_level("dev"),
            DEVNET_FRI_NUM_QUERIES
        );
    }

    #[test]
    fn ultra_matches_devnet_default() {
        assert_eq!(FRI_NUM_QUERIES_ULTRA, DEVNET_FRI_NUM_QUERIES);
        assert_eq!(
            fri_num_queries_for_security_level("ultra"),
            DEVNET_FRI_NUM_QUERIES
        );
    }

    #[test]
    fn devnet_circle_config_defaults_to_forty_queries() {
        let config = devnet_circle_config();
        assert_eq!(config.pcs().fri_params.num_queries, DEVNET_FRI_NUM_QUERIES);
    }

    #[test]
    fn devnet_circle_config_with_queries_overrides() {
        let config = devnet_circle_config_with_queries(8);
        assert_eq!(config.pcs().fri_params.num_queries, 8);
    }

    #[test]
    fn circle_config_for_security_level_uses_mapping() {
        let config = circle_config_for_security_level("normal", 1);
        assert_eq!(config.pcs().fri_params.num_queries, FRI_NUM_QUERIES_NORMAL);
        assert_eq!(config.pcs().fri_params.log_blowup, 1);
    }

    #[test]
    fn keccak_circle_config_defaults_to_forty_queries() {
        let config = keccak_circle_config();
        assert_eq!(config.pcs().fri_params.num_queries, DEVNET_FRI_NUM_QUERIES);
        assert_eq!(config.pcs().fri_params.log_blowup, 4);
    }
}

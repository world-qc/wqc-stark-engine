//! Circle STARK configuration (Mersenne31 + Keccak MMCS).

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

/// Devnet-oriented parameters: modest query count for fast verification.
pub fn devnet_circle_config() -> WqcStarkConfig {
    circle_config_with_blowup(1)
}

/// Higher blowup for degree-heavy AIRs (R3-M2.5b Keccak sponge).
///
/// `log_blowup = 4` ⇒ blowup 16 ⇒ constraint degree up to 17.
pub fn keccak_circle_config() -> WqcStarkConfig {
    circle_config_with_blowup(4)
}

fn circle_config_with_blowup(log_blowup: usize) -> WqcStarkConfig {
    let byte_hash = ByteHash {};
    let field_hash = FieldHash::new(byte_hash);
    let compress = Compress::new(byte_hash);
    let val_mmcs = ValMmcs::new(field_hash, compress, 0);
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    let fri_params = FriParameters {
        log_blowup,
        log_final_poly_len: 0,
        max_log_arity: 1,
        num_queries: 40,
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

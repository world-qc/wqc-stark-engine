//! State-vector STARK leaf (v2).
//!
//! A leaf proves that applying a circuit to |0…0⟩ yields a final state vector with a given
//! Poseidon2 digest. The circuit is fixed by preprocessed columns, and the statement exports
//! a 4-element context and the 4-element digest. Leaves are built as custom non-primitive
//! operations on Plonky3-recursion's circuit prover, so they recurse and aggregate with it.
//!
//! The circuit field is Goldilocks (base, `D = 1`): a recursion layer's first input must be a
//! base-field circuit. Recursion layers run over Goldilocks².

pub mod digest;
pub mod exec;
pub mod leaf;
mod npo;
pub mod recursion;
mod tables;

#[cfg(test)]
mod tests;

use p3_field::extension::BinomialExtensionField;
use p3_goldilocks::Goldilocks;

pub type F = Goldilocks;

/// Largest supported qubit count. The gate table has `gates · 2^(n−1)` rows; at n = 16 and
/// 64 gates a leaf takes about 70 s and 14 GB to prove with [`FriParams::PRODUCTION`].
pub const MAX_QUBITS: usize = 16;

#[derive(Debug)]
pub enum Error {
    /// The circuit is outside what the leaf can prove (qubit count, gate wiring, matrix range).
    InvalidCircuit(String),
    /// A statement value is not a canonical field element.
    InvalidStatement(String),
    Prove(String),
    Verify(String),
    Recursion(String),
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::InvalidCircuit(m) => write!(f, "invalid circuit: {m}"),
            Self::InvalidStatement(m) => write!(f, "invalid statement: {m}"),
            Self::Prove(m) => write!(f, "prove: {m}"),
            Self::Verify(m) => write!(f, "verify: {m}"),
            Self::Recursion(m) => write!(f, "recursion: {m}"),
        }
    }
}

impl std::error::Error for Error {}
/// Circuit field of the leaf: the base field.
pub type EF = F;
/// Recursion-capable built-in config (Goldilocks², Poseidon2 width 8, binary FRI).
pub type Cfg = p3_recursion::builtin_config::GoldilocksD2Poseidon2BinaryConfig;
/// Challenge field of the recursion layers.
pub type Challenge = BinomialExtensionField<F, 2>;

/// FRI parameters of a built-in Goldilocks² config.
#[derive(Clone, Copy, Debug)]
pub struct FriParams {
    pub log_blowup: u32,
    pub log_final_poly_len: u32,
    pub max_log_arity: u32,
    pub num_queries: u32,
    pub query_pow_bits: u32,
}

impl FriParams {
    /// Rate 1/8, 28 queries, 16-bit query PoW (about 100 bits, conjectured).
    pub const PRODUCTION: Self = Self {
        log_blowup: 3,
        log_final_poly_len: 0,
        max_log_arity: 2,
        num_queries: 28,
        query_pow_bits: 16,
    };
    /// Two queries: fast, for tests only.
    pub const TESTING: Self = Self {
        log_blowup: 1,
        log_final_poly_len: 0,
        max_log_arity: 2,
        num_queries: 2,
        query_pow_bits: 0,
    };

    /// Smallest table height the FRI accepts: 2^(log_final_poly_len + log_blowup + 1).
    pub const fn min_trace_height(&self) -> usize {
        1 << (self.log_final_poly_len + self.log_blowup + 1)
    }

    pub fn config(&self) -> Cfg {
        use p3_recursion::artifact::ArtifactLimits;
        use p3_recursion::builtin_config::{
            goldilocks_d2_poseidon2_binary, FriConfigV1, SuiteIdV1,
        };
        let suite = SuiteIdV1::GoldilocksD2Poseidon2BinaryFri;
        let descriptor = FriConfigV1::new(
            suite,
            self.log_blowup,
            self.log_final_poly_len,
            self.max_log_arity,
            self.num_queries,
            0,
            self.query_pow_bits,
            0,
            0,
            0,
            suite.spec().salt_elements as u32,
        );
        goldilocks_d2_poseidon2_binary(&descriptor, &ArtifactLimits::default().verifier)
            .expect("built-in Goldilocks² FRI descriptor")
    }
}

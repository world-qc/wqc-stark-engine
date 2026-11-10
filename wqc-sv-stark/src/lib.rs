//! State-vector STARK leaf (v2).
//!
//! A leaf proves that applying a circuit to |0…0⟩ yields a final state vector with a given
//! Poseidon2 digest. The circuit is fixed by preprocessed columns, and the statement exports
//! a 4-element context and the 4-element digest. Leaves are built as custom non-primitive
//! operations on Plonky3-recursion's circuit prover, so they recurse and aggregate with it.
//!
//! The circuit field is Goldilocks (base, `D = 1`): a recursion layer's first input must be a
//! base-field circuit. Recursion layers run over Goldilocks².

pub mod born;
mod born_tables;
pub mod digest;
pub mod exec;
pub mod leaf;
mod npo;
pub mod recursion;
mod tables;
pub mod verify_cfg;
pub mod wire;

#[cfg(test)]
mod tests;

use p3_field::extension::BinomialExtensionField;
use p3_goldilocks::Goldilocks;

pub type F = Goldilocks;

/// Largest supported qubit count. The gate tables have `2^(n−1)` rows per rounding step (runs
/// of single-qubit gates fuse into one gate, and monomial gates fold away); at n = 16 and 64
/// rounding steps a leaf takes about 33 s and 11 GB to prove at any [`SecurityLevel`].
pub const MAX_QUBITS: usize = 16;

/// Largest number of gate rows (rounding steps × `2^(n−1)`, see [`leaf::gate_rows`]) a leaf
/// may have: 128 rounding steps at n = 16, about 20 GB to prove. The security estimates in
/// the README are for a gate table of this size.
pub const MAX_ROWS: usize = 1 << 22;

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

/// The orchestrator's security tier. It sets the leaf's FRI query count; every recursion proof
/// uses [`FriParams::RECURSION`], so a tree is as sound as its leaves' tier.
///
/// The tier is not in the statement: it is part of the leaf's verifier, and a proof made at
/// another tier fails it. A verifier must therefore be built from the authoritative tier (the
/// dispatched `SubTask.security_level`), never from anything the prover claims.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SecurityLevel {
    Low,
    Normal,
    High,
    Ultra,
}

impl SecurityLevel {
    /// Parses the wire name, trimmed and case-insensitive like v1's ladder. Empty means
    /// `ultra`, as for v1; an unknown name is `None` (v1 falls back to `ultra` instead).
    pub fn parse(s: &str) -> Option<Self> {
        match s.trim().to_ascii_lowercase().as_str() {
            "low" => Some(Self::Low),
            "normal" => Some(Self::Normal),
            "high" => Some(Self::High),
            "ultra" | "" => Some(Self::Ultra),
            _ => None,
        }
    }
}

/// FRI parameters of a built-in Goldilocks² config.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FriParams {
    pub log_blowup: u32,
    pub log_final_poly_len: u32,
    pub max_log_arity: u32,
    pub num_queries: u32,
    pub query_pow_bits: u32,
}

impl FriParams {
    /// Leaf parameters for `level`: rate 1/4 and a 16-bit query PoW at every tier; only the
    /// query count changes. Prove time and memory are set by the blowup, so they are nearly the
    /// same at every tier (n = 16, 64 gates: 32–35 s at both low and ultra); the query count
    /// mainly sets proof size. Estimated conjectured soundness (p3-security, n = 16 leaves):
    /// low 59, normal 79, high 89, ultra 95. Up to high the query phase binds; at ultra the
    /// Goldilocks² field terms (opening batch, LogUp) do, so more queries would not help.
    ///
    /// This ladder is v2's own: v1 leaves use 8 / 16 / 32 / 40 queries on another field.
    pub const fn leaf(level: SecurityLevel) -> Self {
        let num_queries = match level {
            SecurityLevel::Low => 22,
            SecurityLevel::Normal => 32,
            SecurityLevel::High => 37,
            SecurityLevel::Ultra => 42,
        };
        Self {
            log_blowup: 2,
            log_final_poly_len: 0,
            max_log_arity: 2,
            num_queries,
            query_pow_bits: 16,
        }
    }

    /// Every recursion proof (layers and aggregation) at every tier: rate 1/8, 28 queries,
    /// 16-bit query PoW (about 99 bits estimated; the query phase binds, since the recursion's
    /// tables are at most 2^14 rows and the field terms stay above 100). The recursion's own FRI does not vary with the
    /// tier, so recursion proofs are roughly the same size at every tier; the size still varies
    /// a little with the child (first layers over low and ultra leaves at n = 4 and 16 measured
    /// 174–203 KB).
    pub const RECURSION: Self = Self {
        log_blowup: 3,
        log_final_poly_len: 0,
        max_log_arity: 2,
        num_queries: 28,
        query_pow_bits: 16,
    };

    /// Two queries: fast, for tests only.
    #[cfg(test)]
    pub(crate) const TESTING: Self = Self {
        log_blowup: 1,
        log_final_poly_len: 0,
        max_log_arity: 2,
        num_queries: 2,
        query_pow_bits: 0,
    };

    /// The simple FRI query estimate `log_blowup · num_queries + query_pow_bits` (p3-fri's
    /// `FriParameters::conjectured_soundness_bits`). It is an upper bound on what a proof
    /// attains: p3-security's random-words estimate of the query phase is about a bit lower, and
    /// the field terms cap a leaf near 95 bits (see [`FriParams::leaf`]).
    pub const fn conjectured_bits(&self) -> u32 {
        self.log_blowup * self.num_queries + self.query_pow_bits
    }

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

//! Canonical execution-trace schema shared by prover and executors.
//!
//! This module is the contract between:
//! - `wqc-core` executors (CPU today, `wgpu` in the future), and
//! - `wqc-stark-core` AIR/proof logic.
//!
//! Keep this stable unless you intentionally migrate the proof format.

/// Number of columns emitted by `wqc-core` per trace row.
pub const TRACE_WIDTH: usize = 10;

/// Number of selector columns expanded in AIR (`X,Y,Z,H,S,T,CTRL,CCNOT,ROT`).
pub const SELECTOR_COUNT: usize = 9;

/// AIR matrix width after expanding one trace row into selectors and state payload.
pub const AIR_WIDTH: usize = 18;

/// Fixed-point scale used to map floating values into Mersenne31.
///
/// 1e4 is chosen so squaring remains within safe range under the field modulus.
pub const FIXED_POINT_SCALE: f64 = 10_000.0;

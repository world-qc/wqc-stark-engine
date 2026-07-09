//! Canonical execution-trace schema shared by prover and executors.
//!
//! Gate IDs (column 0 of each trace row) match `wqc-core` `Gate::to_stark_id`:
//! 1=X, 2=Y, 3=Z, 4=H, 5=S, 6=T, 7=CNOT, 8=CZ, 9=CCNOT, 10=RX, 11=RY, 12=RZ, 0=padding/boundary.

/// Number of columns emitted by `wqc-core` per trace row.
pub const TRACE_WIDTH: usize = 11;

/// Trace column index for the logical target qubit sampled in amplitude columns.
pub const TRACE_COL_TARGET_QUBIT: usize = 9;

/// Trace column index for transition enforcement (`1` = next row shares the same target).
pub const TRACE_COL_TRANSITION_LINK: usize = 10;

/// Selector columns expanded in AIR (one-hot per active gate family).
pub const SELECTOR_COUNT: usize = 10;

/// AIR matrix width: gate_id + selectors + payload (ctrl×2, trig×2, amp×4, target, link).
pub const AIR_WIDTH: usize = 1 + SELECTOR_COUNT + 8 + 2;

/// Fixed-point scale used to map floating values into Mersenne31.
pub const FIXED_POINT_SCALE: f64 = 10_000.0;

pub const GATE_X: u32 = 1;
pub const GATE_Y: u32 = 2;
pub const GATE_Z: u32 = 3;
pub const GATE_H: u32 = 4;
pub const GATE_S: u32 = 5;
pub const GATE_T: u32 = 6;
pub const GATE_CNOT: u32 = 7;
pub const GATE_CZ: u32 = 8;
pub const GATE_CCNOT: u32 = 9;
pub const GATE_RX: u32 = 10;
pub const GATE_RY: u32 = 11;
pub const GATE_RZ: u32 = 12;

/// Single-row trace for |0⟩ idle boundary (tests and aggregation fixtures).
pub fn idle_qubit0_trace() -> Vec<f64> {
    vec![0.0, 0.0, 0.0, 1.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0, 0.0]
}

/// Golden H(0) trace: pre-gate, post-gate, terminal rows with transition links.
pub fn golden_h_q0_trace() -> Vec<f64> {
    let inv_sqrt2 = 1.0 / 2.0f64.sqrt();
    vec![
        4.0, 0.0, 0.0, 1.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 1.0, 0.0, inv_sqrt2,
        0.0, inv_sqrt2, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 1.0, 0.0, inv_sqrt2, 0.0, inv_sqrt2, 0.0,
        0.0, 0.0,
    ]
}

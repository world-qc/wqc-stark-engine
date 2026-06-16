//! Mersenne31 quantum execution AIR: trace ingestion and constraint accumulation.

use p3_field::{AbstractField, Field, PrimeField32};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_mersenne_31::Mersenne31;

use crate::trace_spec::{
    AIR_WIDTH, FIXED_POINT_SCALE, GATE_CCNOT, GATE_CNOT, GATE_CZ, GATE_RX, GATE_RY, GATE_RZ,
    SELECTOR_COUNT, TRACE_WIDTH,
};

/// One expanded AIR row (19 columns).
#[derive(Debug, Clone)]
pub struct QuantumAirRow {
    pub gate_type: Mersenne31,
    pub sel_x: Mersenne31,
    pub sel_y: Mersenne31,
    pub sel_z: Mersenne31,
    pub sel_h: Mersenne31,
    pub sel_s: Mersenne31,
    pub sel_t: Mersenne31,
    pub sel_ctrl: Mersenne31,
    pub sel_cz: Mersenne31,
    pub sel_ccnot: Mersenne31,
    pub sel_rot: Mersenne31,
    pub ctrl_active: Mersenne31,
    pub ctrl_active_2: Mersenne31,
    pub p_cos: Mersenne31,
    pub p_sin: Mersenne31,
    pub v0_re: Mersenne31,
    pub v0_im: Mersenne31,
    pub v1_re: Mersenne31,
    pub v1_im: Mersenne31,
}

impl QuantumAirRow {
    fn from_air_columns(cols: &[Mersenne31]) -> Self {
        Self {
            gate_type: cols[0],
            sel_x: cols[1],
            sel_y: cols[2],
            sel_z: cols[3],
            sel_h: cols[4],
            sel_s: cols[5],
            sel_t: cols[6],
            sel_ctrl: cols[7],
            sel_cz: cols[8],
            sel_ccnot: cols[9],
            sel_rot: cols[10],
            ctrl_active: cols[11],
            ctrl_active_2: cols[12],
            p_cos: cols[13],
            p_sin: cols[14],
            v0_re: cols[15],
            v0_im: cols[16],
            v1_re: cols[17],
            v1_im: cols[18],
        }
    }

    fn gate_active_weight(&self) -> Mersenne31 {
        self.sel_x
            + self.sel_y
            + self.sel_z
            + self.sel_h
            + self.sel_s
            + self.sel_t
            + self.sel_ctrl
            + self.sel_cz
            + self.sel_ccnot
            + self.sel_rot
    }
}

/// Maps `f64` trace values into Mersenne31 with fixed-point scaling.
pub fn f64_to_m31(val: f64) -> Mersenne31 {
    let scaled = (val * FIXED_POINT_SCALE).round() as i64;
    if scaled >= 0 {
        Mersenne31::from_canonical_u64((scaled as u64) % 2_147_483_647)
    } else {
        let abs_scaled = (scaled.abs() as u64) % 2_147_483_647;
        Mersenne31::from_canonical_u64(2_147_483_647 - abs_scaled)
    }
}

/// Selector index for a gate id (1–12). Returns `None` for padding (`0`).
pub fn selector_index_for_gate(gate_raw: u32) -> Option<usize> {
    match gate_raw {
        1..=6 => Some((gate_raw - 1) as usize),
        GATE_CNOT => Some(6),
        GATE_CZ => Some(7),
        GATE_CCNOT => Some(8),
        GATE_RX | GATE_RY | GATE_RZ => Some(9),
        _ => None,
    }
}

/// Builds one-hot selector columns for a gate id.
pub fn selectors_for_gate(gate_raw: u32) -> [Mersenne31; SELECTOR_COUNT] {
    let mut selectors = [Mersenne31::zero(); SELECTOR_COUNT];
    if let Some(idx) = selector_index_for_gate(gate_raw) {
        selectors[idx] = Mersenne31::one();
    }
    selectors
}

/// Expands a flat `f64` execution trace into an AIR matrix.
pub fn trace_to_air_matrix(execution_trace: &[f64]) -> Option<RowMajorMatrix<Mersenne31>> {
    if execution_trace.is_empty() || !execution_trace.len().is_multiple_of(TRACE_WIDTH) {
        return None;
    }

    let mut flat_m31_data = Vec::with_capacity((execution_trace.len() / TRACE_WIDTH) * AIR_WIDTH);

    for chunk in execution_trace.chunks_exact(TRACE_WIDTH) {
        let gate_raw = chunk[0].round() as u32;
        flat_m31_data.push(Mersenne31::from_canonical_u32(gate_raw));
        flat_m31_data.extend_from_slice(&selectors_for_gate(gate_raw));
        flat_m31_data.push(Mersenne31::from_canonical_u32(chunk[1].round() as u32));
        flat_m31_data.push(Mersenne31::from_canonical_u32(chunk[2].round() as u32));
        flat_m31_data.push(f64_to_m31(chunk[3]));
        flat_m31_data.push(f64_to_m31(chunk[4]));
        flat_m31_data.push(f64_to_m31(chunk[5]));
        flat_m31_data.push(f64_to_m31(chunk[6]));
        flat_m31_data.push(f64_to_m31(chunk[7]));
        flat_m31_data.push(f64_to_m31(chunk[8]));
    }

    Some(RowMajorMatrix::new(flat_m31_data, AIR_WIDTH))
}

/// Evaluates transition constraints across adjacent AIR rows; zero iff the trace is valid.
pub fn evaluate_air_sum(trace_matrix: &RowMajorMatrix<Mersenne31>) -> Mersenne31 {
    let inv_sqrt2 = Mersenne31::from_canonical_u32(7071);
    let scale_factor = Mersenne31::from_canonical_u32(10_000);
    let scale_inverse = scale_factor.inverse();
    let two = Mersenne31::from_canonical_u32(2);
    let one = Mersenne31::one();

    let height = trace_matrix.height();
    let mut constraint_accumulations = Mersenne31::zero();
    let debug_air = std::env::var("WQC_STARK_DEBUG_AIR").ok().as_deref() == Some("1");

    for r in 0..height.saturating_sub(1) {
        let curr = QuantumAirRow::from_air_columns(&trace_matrix.row(r).collect::<Vec<_>>());
        let next = QuantumAirRow::from_air_columns(&trace_matrix.row(r + 1).collect::<Vec<_>>());

        let v0_unchanged_re = next.v0_re - curr.v0_re;
        let v0_unchanged_im = next.v0_im - curr.v0_im;
        let v1_unchanged_re = next.v1_re - curr.v1_re;
        let v1_unchanged_im = next.v1_im - curr.v1_im;
        let identity_cost = v0_unchanged_re * v0_unchanged_re
            + v0_unchanged_im * v0_unchanged_im
            + v1_unchanged_re * v1_unchanged_re
            + v1_unchanged_im * v1_unchanged_im;

        let cost_x = (next.v0_re - curr.v1_re).square()
            + (next.v0_im - curr.v1_im).square()
            + (next.v1_re - curr.v0_re).square()
            + (next.v1_im - curr.v0_im).square();

        let cost_y = (next.v0_re - curr.v1_im).square()
            + (next.v0_im + curr.v1_re).square()
            + (next.v1_re + curr.v0_im).square()
            + (next.v1_im - curr.v0_re).square();

        let cost_z = (next.v0_re - curr.v0_re).square()
            + (next.v0_im - curr.v0_im).square()
            + (next.v1_re + curr.v1_re).square()
            + (next.v1_im + curr.v1_im).square();

        let h_0 = (next.v0_re * scale_factor) - (curr.v0_re + curr.v1_re) * inv_sqrt2;
        let h_1 = (next.v0_im * scale_factor) - (curr.v0_im + curr.v1_im) * inv_sqrt2;
        let h_2 = (next.v1_re * scale_factor) - (curr.v0_re - curr.v1_re) * inv_sqrt2;
        let h_3 = (next.v1_im * scale_factor) - (curr.v0_im - curr.v1_im) * inv_sqrt2;
        let cost_h = (h_0 * scale_inverse).square()
            + (h_1 * scale_inverse).square()
            + (h_2 * scale_inverse).square()
            + (h_3 * scale_inverse).square();

        let cost_s = (next.v0_re - curr.v0_re).square()
            + (next.v0_im - curr.v0_im).square()
            + (next.v1_re + curr.v1_im).square()
            + (next.v1_im - curr.v1_re).square();

        let t_2 = (next.v1_re * scale_factor) - (curr.v1_re - curr.v1_im) * inv_sqrt2;
        let t_3 = (next.v1_im * scale_factor) - (curr.v1_re + curr.v1_im) * inv_sqrt2;
        let cost_t = (next.v0_re - curr.v0_re).square()
            + (next.v0_im - curr.v0_im).square()
            + (t_2 * scale_inverse).square()
            + (t_3 * scale_inverse).square();

        let ctrl_active = curr.ctrl_active;
        let ctrl_inactive = one - ctrl_active;
        let expected_c_v0_re = (ctrl_inactive * curr.v0_re) + (ctrl_active * curr.v1_re);
        let expected_c_v0_im = (ctrl_inactive * curr.v0_im) + (ctrl_active * curr.v1_im);
        let expected_c_v1_re = (ctrl_inactive * curr.v1_re) + (ctrl_active * curr.v0_re);
        let expected_c_v1_im = (ctrl_inactive * curr.v1_im) + (ctrl_active * curr.v0_im);
        let cost_ctrl = (next.v0_re - expected_c_v0_re).square()
            + (next.v0_im - expected_c_v0_im).square()
            + (next.v1_re - expected_c_v1_re).square()
            + (next.v1_im - expected_c_v1_im).square();

        let phase = one - (two * ctrl_active);
        let expected_cz_v1_re = curr.v1_re * phase;
        let expected_cz_v1_im = curr.v1_im * phase;
        let cost_cz = (next.v0_re - curr.v0_re).square()
            + (next.v0_im - curr.v0_im).square()
            + (next.v1_re - expected_cz_v1_re).square()
            + (next.v1_im - expected_cz_v1_im).square();

        let cc_active = curr.ctrl_active * curr.ctrl_active_2;
        let cc_inactive = one - cc_active;
        let expected_cc_v0_re = (cc_inactive * curr.v0_re) + (cc_active * curr.v1_re);
        let expected_cc_v0_im = (cc_inactive * curr.v0_im) + (cc_active * curr.v1_im);
        let expected_cc_v1_re = (cc_inactive * curr.v1_re) + (cc_active * curr.v0_re);
        let expected_cc_v1_im = (cc_inactive * curr.v1_im) + (cc_active * curr.v0_im);
        let cost_ccnot = (next.v0_re - expected_cc_v0_re).square()
            + (next.v0_im - expected_cc_v0_im).square()
            + (next.v1_re - expected_cc_v1_re).square()
            + (next.v1_im - expected_cc_v1_im).square();

        let rot_0 = (next.v0_re * scale_factor) - (curr.v0_re * curr.p_cos - curr.v1_re * curr.p_sin);
        let rot_1 = (next.v0_im * scale_factor) - (curr.v0_im * curr.p_cos - curr.v1_im * curr.p_sin);
        let rot_2 = (next.v1_re * scale_factor) - (curr.v1_re * curr.p_cos + curr.v0_re * curr.p_sin);
        let rot_3 = (next.v1_im * scale_factor) - (curr.v1_im * curr.p_cos + curr.v0_im * curr.p_sin);
        let cost_rot = (rot_0 * scale_inverse).square()
            + (rot_1 * scale_inverse).square()
            + (rot_2 * scale_inverse).square()
            + (rot_3 * scale_inverse).square();

        let gate_costs = curr.sel_x * cost_x
            + curr.sel_y * cost_y
            + curr.sel_z * cost_z
            + curr.sel_h * cost_h
            + curr.sel_s * cost_s
            + curr.sel_t * cost_t
            + curr.sel_ctrl * cost_ctrl
            + curr.sel_cz * cost_cz
            + curr.sel_ccnot * cost_ccnot
            + curr.sel_rot * cost_rot;

        let gate_active = curr.gate_active_weight();
        let row_acc = gate_active * gate_costs + (one - gate_active) * identity_cost;
        constraint_accumulations += row_acc;

        if debug_air && row_acc != Mersenne31::zero() {
            eprintln!(
                "[STARK Core][AIR] row={} gate={} row_acc={}",
                r,
                curr.gate_type.as_canonical_u32(),
                row_acc.as_canonical_u32(),
            );
        }
    }

    constraint_accumulations
}

/// Boundary amplitudes (Mersenne31 canonical u32) from the last AIR row.
pub fn boundary_from_matrix(trace_matrix: &RowMajorMatrix<Mersenne31>) -> Option<[u32; 4]> {
    if trace_matrix.height() == 0 {
        return None;
    }
    let last: Vec<Mersenne31> = trace_matrix
        .row(trace_matrix.height() - 1)
        .collect();
    Some([
        last[15].as_canonical_u32(),
        last[16].as_canonical_u32(),
        last[17].as_canonical_u32(),
        last[18].as_canonical_u32(),
    ])
}

/// Convenience: evaluate AIR sum directly from a flat execution trace.
pub fn evaluate_execution_trace(execution_trace: &[f64]) -> Option<Mersenne31> {
    let matrix = trace_to_air_matrix(execution_trace)?;
    Some(evaluate_air_sum(&matrix))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn selector_mapping_covers_cz_and_ccnot() {
        let cz = selectors_for_gate(GATE_CZ);
        assert_eq!(cz[7], Mersenne31::one());
        assert_eq!(cz[8], Mersenne31::zero());

        let ccnot = selectors_for_gate(GATE_CCNOT);
        assert_eq!(ccnot[8], Mersenne31::one());
        assert_eq!(ccnot[7], Mersenne31::zero());
    }

    #[test]
    fn empty_circuit_trace_has_zero_air_sum() {
        let trace = vec![
            0.0, 0.0, 0.0, 1.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0,
        ];
        let sum = evaluate_execution_trace(&trace).unwrap();
        assert_eq!(sum, Mersenne31::zero());
    }
}

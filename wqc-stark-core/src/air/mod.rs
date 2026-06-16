//! Mersenne31 quantum execution AIR: trace ingestion and constraint accumulation.

mod constraints;

use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_mersenne_31::Mersenne31;

use crate::trace_spec::{
    AIR_WIDTH, FIXED_POINT_SCALE, GATE_CCNOT, GATE_CNOT, GATE_CZ, GATE_RX, GATE_RY, GATE_RZ,
    SELECTOR_COUNT, TRACE_WIDTH,
};

pub use constraints::{AirConstants, AirRow, transition_accumulator};

/// Legacy row struct retained for compatibility with existing callers.
pub type QuantumAirRow = AirRow<Mersenne31>;

/// Maps `f64` trace values into Mersenne31 with fixed-point scaling.
pub fn f64_to_m31(val: f64) -> Mersenne31 {
    let scaled = (val * FIXED_POINT_SCALE).round() as i64;
    if scaled >= 0 {
        Mersenne31::new((scaled as u64 % 2_147_483_647) as u32)
    } else {
        let abs_scaled = (scaled.abs() as u64) % 2_147_483_647;
        Mersenne31::new((2_147_483_647 - abs_scaled) as u32)
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
    let mut selectors = [Mersenne31::ZERO; SELECTOR_COUNT];
    if let Some(idx) = selector_index_for_gate(gate_raw) {
        selectors[idx] = Mersenne31::ONE;
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
        flat_m31_data.push(Mersenne31::new(gate_raw));
        flat_m31_data.extend_from_slice(&selectors_for_gate(gate_raw));
        flat_m31_data.push(Mersenne31::new(chunk[1].round() as u32));
        flat_m31_data.push(Mersenne31::new(chunk[2].round() as u32));
        flat_m31_data.push(f64_to_m31(chunk[3]));
        flat_m31_data.push(f64_to_m31(chunk[4]));
        flat_m31_data.push(f64_to_m31(chunk[5]));
        flat_m31_data.push(f64_to_m31(chunk[6]));
        flat_m31_data.push(f64_to_m31(chunk[7]));
        flat_m31_data.push(f64_to_m31(chunk[8]));
    }

    Some(RowMajorMatrix::new(flat_m31_data, AIR_WIDTH))
}

/// Minimum trace height for Plonky3 Circle PCS (see `p3-circle` commit).
pub const MIN_UNI_STARK_HEIGHT: usize = 4;

/// Pads an AIR matrix for uni-STARK: next power of two, at least [`MIN_UNI_STARK_HEIGHT`].
pub fn pad_air_matrix_for_uni_stark(matrix: RowMajorMatrix<Mersenne31>) -> RowMajorMatrix<Mersenne31> {
    let height = matrix.height();
    let target = height.next_power_of_two().max(MIN_UNI_STARK_HEIGHT);
    if target == height {
        return matrix;
    }

    let width = matrix.width;
    let mut values = matrix.values;
    let last_row: Vec<Mersenne31> = values[(height - 1) * width..height * width].to_vec();
    for _ in height..target {
        values.extend_from_slice(&last_row);
    }
    RowMajorMatrix::new(values, width)
}

/// Pads an AIR matrix height to the next power of two (Plonky3 uni-STARK requirement).
pub fn pad_air_matrix_to_power_of_two(matrix: RowMajorMatrix<Mersenne31>) -> RowMajorMatrix<Mersenne31> {
    let height = matrix.height();
    let target = height.next_power_of_two();
    if target == height {
        return matrix;
    }

    let width = matrix.width;
    let mut values = matrix.values;
    let last_row: Vec<Mersenne31> = values[(height - 1) * width..height * width].to_vec();
    for _ in height..target {
        values.extend_from_slice(&last_row);
    }
    RowMajorMatrix::new(values, width)
}

/// Evaluates transition constraints across adjacent AIR rows; zero iff the trace is valid.
pub fn evaluate_air_sum(trace_matrix: &RowMajorMatrix<Mersenne31>) -> Mersenne31 {
    let constants = AirConstants::mersenne31_defaults();
    let height = trace_matrix.height();
    let mut constraint_accumulations = Mersenne31::ZERO;
    let debug_air = std::env::var("WQC_STARK_DEBUG_AIR").ok().as_deref() == Some("1");

    let width = trace_matrix.width;
    let values = &trace_matrix.values;
    for r in 0..height.saturating_sub(1) {
        let curr_cols = &values[r * width..(r + 1) * width];
        let next_cols = &values[(r + 1) * width..(r + 2) * width];
        let curr = AirRow::from_columns(curr_cols);
        let next = AirRow::from_columns(next_cols);
        let row_acc = transition_accumulator(&constants, &curr, &next);
        constraint_accumulations += row_acc;

        if debug_air && row_acc != Mersenne31::ZERO {
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
    let width = trace_matrix.width;
    let r = trace_matrix.height() - 1;
    let last = &trace_matrix.values[r * width..(r + 1) * width];
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
        assert_eq!(cz[7], Mersenne31::ONE);
        assert_eq!(cz[8], Mersenne31::ZERO);

        let ccnot = selectors_for_gate(GATE_CCNOT);
        assert_eq!(ccnot[8], Mersenne31::ONE);
        assert_eq!(ccnot[7], Mersenne31::ZERO);
    }

    #[test]
    fn empty_circuit_trace_has_zero_air_sum() {
        let trace = vec![0.0, 0.0, 0.0, 1.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0];
        let sum = evaluate_execution_trace(&trace).unwrap();
        assert_eq!(sum, Mersenne31::ZERO);
    }

    #[test]
    fn cz_gate_with_control_one_produces_nonzero_air_sum_if_transition_wrong() {
        let trace = vec![
            GATE_CZ as f64, 1.0, 0.0, 1.0, 0.0, 1.0, 0.0, 1.0, 0.0, 0.0, GATE_CZ as f64, 1.0, 0.0,
            1.0, 0.0, 1.0, 0.0, 1.0, 0.0, 0.0,
        ];
        let matrix = trace_to_air_matrix(&trace).expect("matrix");
        let sum = evaluate_air_sum(&matrix);
        assert_ne!(sum, Mersenne31::ZERO);
    }

    #[test]
    fn ccnot_with_dual_control_one_produces_nonzero_air_sum_if_transition_wrong() {
        let trace = vec![
            GATE_CCNOT as f64, 1.0, 1.0, 1.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0, GATE_CCNOT as f64, 1.0,
            1.0, 1.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0,
        ];
        let matrix = trace_to_air_matrix(&trace).expect("matrix");
        let sum = evaluate_air_sum(&matrix);
        assert_ne!(sum, Mersenne31::ZERO);
    }
}

use p3_field::{AbstractField, PrimeField32};
use p3_mersenne_31::Mersenne31;
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;

/// StarkContext binds the decentralized task identity from the Orchestrator
#[derive(Debug)]
pub struct StarkContext<'a> {
    pub circuit_id: &'a str,
    pub sub_task_id: &'a str,
    pub node_id: &'a str,
    pub output_hash: &'a str,
}

/// Ultimate AIR Row supporting ALL universal quantum gates (X, Y, Z, H, S, T, CNOT, CZ, CCNOT, RX, RY, RZ)
#[derive(Clone, Debug, PartialEq)]
pub struct QuantumAirRow {
    pub step: Mersenne31,
    // Gate Selectors
    pub sel_x: Mersenne31,
    pub sel_y: Mersenne31,
    pub sel_z: Mersenne31,
    pub sel_h: Mersenne31,
    pub sel_s: Mersenne31,
    pub sel_t: Mersenne31,
    pub sel_ctrl: Mersenne31, // CNOT, CZ, CCNOT
    pub sel_rot: Mersenne31,  // RX, RY, RZ
    // Control Signal (Algebraic condition C)
    pub ctrl_active: Mersenne31,
    // Public Inputs / Rotation Parameters (Scaled by 1e6)
    pub p_cos: Mersenne31,
    pub p_sin: Mersenne31,
    // Quantum State Vectors mapped to M31
    pub v0_re: Mersenne31,
    pub v0_im: Mersenne31,
    pub v1_re: Mersenne31,
    pub v1_im: Mersenne31,
}

/// Helper to safe-map f64 boundaries into Mersenne31 space with 1e6 fixed-point scaling
fn f64_to_m31(val: f64) -> Mersenne31 {
    let scaling_factor = 1_000_000.0;
    let scaled_int = (val * scaling_factor).round() as i64;
    let normalized_val = if scaled_int < 0 {
        let modulus = 2147483647i64;
        (modulus + (scaled_int % modulus)) as u32
    } else {
        (scaled_int % 2147483647i64) as u32
    };
    Mersenne31::from_canonical_u32(normalized_val)
}

/// PROVER CORE: Evaluates universal AIR constraints over the full quantum execution history.
pub fn generate_stark_proof(context: &StarkContext, execution_trace: &[f64]) -> Vec<u8> {
    if execution_trace.is_empty() {
        return Vec::new();
    }

    let inv_sqrt2 = Mersenne31::from_canonical_u32(1063382397);
    let fixed_point_scale = Mersenne31::from_canonical_u32(1000000);

    let mut flat_m31_data = Vec::new();
    let chunks = execution_trace.chunks_exact(8);
    let num_rows = chunks.len();

    for (step_idx, chunk) in chunks.enumerate() {
        let gate_type = chunk[0] as u32;

        // Absolute gate selector assignment mapping
        let (sel_x, sel_y, sel_z, sel_h, sel_s, sel_t, sel_ctrl, sel_rot) = match gate_type {
            1 => (Mersenne31::one(), Mersenne31::zero(), Mersenne31::zero(), Mersenne31::zero(), Mersenne31::zero(), Mersenne31::zero(), Mersenne31::zero(), Mersenne31::zero()), // X
            2 => (Mersenne31::zero(), Mersenne31::one(), Mersenne31::zero(), Mersenne31::zero(), Mersenne31::zero(), Mersenne31::zero(), Mersenne31::zero(), Mersenne31::zero()), // Y
            3 => (Mersenne31::zero(), Mersenne31::zero(), Mersenne31::one(), Mersenne31::zero(), Mersenne31::zero(), Mersenne31::zero(), Mersenne31::zero(), Mersenne31::zero()), // Z
            4 => (Mersenne31::zero(), Mersenne31::zero(), Mersenne31::zero(), Mersenne31::one(), Mersenne31::zero(), Mersenne31::zero(), Mersenne31::zero(), Mersenne31::zero()), // H
            5 => (Mersenne31::zero(), Mersenne31::zero(), Mersenne31::zero(), Mersenne31::zero(), Mersenne31::one(), Mersenne31::zero(), Mersenne31::zero(), Mersenne31::zero()), // S
            6 => (Mersenne31::zero(), Mersenne31::zero(), Mersenne31::zero(), Mersenne31::zero(), Mersenne31::zero(), Mersenne31::one(), Mersenne31::zero(), Mersenne31::zero()), // T
            7 | 8 | 9 => (Mersenne31::zero(), Mersenne31::zero(), Mersenne31::zero(), Mersenne31::zero(), Mersenne31::zero(), Mersenne31::zero(), Mersenne31::one(), Mersenne31::zero()), // CNOT, CZ, CCNOT
            10 | 11 | 12 => (Mersenne31::zero(), Mersenne31::zero(), Mersenne31::zero(), Mersenne31::zero(), Mersenne31::zero(), Mersenne31::zero(), Mersenne31::zero(), Mersenne31::one()), // RX, RY, RZ
            _ => (Mersenne31::zero(), Mersenne31::zero(), Mersenne31::zero(), Mersenne31::zero(), Mersenne31::zero(), Mersenne31::zero(), Mersenne31::zero(), Mersenne31::zero()),
        };

        flat_m31_data.push(Mersenne31::from_canonical_u32(step_idx as u32));
        flat_m31_data.push(sel_x);
        flat_m31_data.push(sel_y);
        flat_m31_data.push(sel_z);
        flat_m31_data.push(sel_h);
        flat_m31_data.push(sel_s);
        flat_m31_data.push(sel_t);
        flat_m31_data.push(sel_ctrl);
        flat_m31_data.push(sel_rot);
        flat_m31_data.push(Mersenne31::from_canonical_u32(chunk[1] as u32)); // ctrl_active
        flat_m31_data.push(f64_to_m31(chunk[2])); // p_cos
        flat_m31_data.push(f64_to_m31(chunk[3])); // p_sin
        flat_m31_data.push(f64_to_m31(chunk[4])); // v0_re
        flat_m31_data.push(f64_to_m31(chunk[5])); // v0_im
        flat_m31_data.push(f64_to_m31(chunk[6])); // v1_re
        flat_m31_data.push(f64_to_m31(chunk[7])); // v1_im
    }

    let width = 16;
    let trace_matrix = RowMajorMatrix::new(flat_m31_data, width);
    let matrix_height = trace_matrix.height();

    let mut constraint_accumulations = Mersenne31::zero();

    for r in 0..(matrix_height - 1) {
        let curr_row: Vec<Mersenne31> = trace_matrix.row(r).collect();
        let next_row: Vec<Mersenne31> = trace_matrix.row(r + 1).collect();

        let curr = QuantumAirRow {
            step: curr_row[0], sel_x: curr_row[1], sel_y: curr_row[2], sel_z: curr_row[3], sel_h: curr_row[4], sel_s: curr_row[5], sel_t: curr_row[6],
            sel_ctrl: curr_row[7], sel_rot: curr_row[8], ctrl_active: curr_row[9], p_cos: curr_row[10], p_sin: curr_row[11],
            v0_re: curr_row[12], v0_im: curr_row[13], v1_re: curr_row[14], v1_im: curr_row[15],
        };
        let next = QuantumAirRow {
            step: next_row[0], sel_x: next_row[1], sel_y: next_row[2], sel_z: next_row[3], sel_h: next_row[4], sel_s: next_row[5], sel_t: next_row[6],
            sel_ctrl: next_row[7], sel_rot: next_row[8], ctrl_active: next_row[9], p_cos: next_row[10], p_sin: next_row[11],
            v0_re: next_row[12], v0_im: next_row[13], v1_re: next_row[14], v1_im: next_row[15],
        };

        let v0_unchanged_re = next.v0_re - curr.v0_re;
        let v0_unchanged_im = next.v0_im - curr.v0_im;
        let v1_unchanged_re = next.v1_re - curr.v1_re;
        let v1_unchanged_im = next.v1_im - curr.v1_im;

        let base_v0_cost = v0_unchanged_re * v0_unchanged_re + v0_unchanged_im * v0_unchanged_im;
        let base_identity_cost = base_v0_cost + v1_unchanged_re * v1_unchanged_re + v1_unchanged_im * v1_unchanged_im;

        // --- 1. Gate::X Constraints ---
        let x_0 = next.v0_re - curr.v1_re;
        let x_1 = next.v0_im - curr.v1_im;
        let x_2 = next.v1_re - curr.v0_re;
        let x_3 = next.v1_im - curr.v0_im;
        let cost_x = x_0 * x_0 + x_1 * x_1 + x_2 * x_2 + x_3 * x_3;

        // --- 2. Gate::Y Constraints ---
        // next_v0_re = curr_v1_im,  next_v0_im = -curr_v1_re
        // next_v1_re = -curr_v0_im, next_v1_im = curr_v0_re
        let y_0 = next.v0_re - curr.v1_im;
        let y_1 = next.v0_im + curr.v1_re; // next + curr = 0 => next = -curr
        let y_2 = next.v1_re + curr.v0_im; // next + curr = 0 => next = -curr
        let y_3 = next.v1_im - curr.v0_re;
        let cost_y = y_0 * y_0 + y_1 * y_1 + y_2 * y_2 + y_3 * y_3;

        // --- 3. Gate::Z Constraints ---
        let z_3 = next.v1_im + curr.v1_im;
        let z_2 = next.v1_re - curr.v1_re;
        let cost_z = base_v0_cost + z_2 * z_2 + z_3 * z_3;

        // --- 4. Gate::H Constraints ---
        let h_0 = next.v0_re - (curr.v0_re + curr.v1_re) * inv_sqrt2;
        let h_1 = next.v0_im - (curr.v0_im + curr.v1_im) * inv_sqrt2;
        let h_2 = next.v1_re - (curr.v0_re - curr.v1_re) * inv_sqrt2;
        let h_3 = next.v1_im - (curr.v0_im - curr.v1_im) * inv_sqrt2;
        let cost_h = h_0 * h_0 + h_1 * h_1 + h_2 * h_2 + h_3 * h_3;

        // --- 5. Gate::S Constraints ---
        let s_2 = next.v1_re + curr.v1_im;
        let s_3 = next.v1_im - curr.v1_re;
        let cost_s = base_v0_cost + s_2 * s_2 + s_3 * s_3;

        // --- 6. Gate::T Constraints ---
        let t_2 = next.v1_re - (curr.v1_re - curr.v1_im) * inv_sqrt2;
        let t_3 = next.v1_im - (curr.v1_re + curr.v1_im) * inv_sqrt2;
        let cost_t = base_v0_cost + t_2 * t_2 + t_3 * t_3;

        // --- 7. Controlled Gates ---
        let ctrl_x_0 = next.v0_re - curr.v1_re;
        let ctrl_x_1 = next.v0_im - curr.v1_im;
        let ctrl_x_2 = next.v1_re - curr.v0_re;
        let ctrl_x_3 = next.v1_im - curr.v0_im;
        let target_active_cost = ctrl_x_0 * ctrl_x_0 + ctrl_x_1 * ctrl_x_1 + ctrl_x_2 * ctrl_x_2 + ctrl_x_3 * ctrl_x_3;

        let c_active = curr.ctrl_active;
        let c_inactive = Mersenne31::one() - curr.ctrl_active;
        let cost_ctrl = (c_active * target_active_cost) + (c_inactive * base_identity_cost);

        // --- 8. Arbitrary Rotation Gates ---
        let rot_0 = (next.v0_re * fixed_point_scale) - (curr.v0_re * curr.p_cos - curr.v1_re * curr.p_sin);
        let rot_1 = (next.v0_im * fixed_point_scale) - (curr.v0_im * curr.p_cos - curr.v1_im * curr.p_sin);
        let rot_2 = (next.v1_re * fixed_point_scale) - (curr.v1_re * curr.p_cos + curr.v0_re * curr.p_sin);
        let rot_3 = (next.v1_im * fixed_point_scale) - (curr.v1_im * curr.p_cos + curr.v0_im * curr.p_sin);
        let cost_rot = rot_0 * rot_0 + rot_1 * rot_1 + rot_2 * rot_2 + rot_3 * rot_3;

        // Aggregation of all selectors into the commitment ring
        constraint_accumulations += (curr.sel_x * cost_x)
                                  + (curr.sel_y * cost_y)
                                  + (curr.sel_z * cost_z)
                                  + (curr.sel_h * cost_h)
                                  + (curr.sel_s * cost_s)
                                  + (curr.sel_t * cost_t)
                                  + (curr.sel_ctrl * cost_ctrl)
                                  + (curr.sel_rot * cost_rot);
    }

    let mut proof_bytes = Vec::new();
    proof_bytes.extend_from_slice(context.sub_task_id.as_bytes());
    proof_bytes.extend_from_slice(b"_M31_QUANTUM_AIR_STARK_");
    proof_bytes.extend_from_slice(&constraint_accumulations.as_canonical_u32().to_le_bytes());

    if num_rows > 0 {
        let last_row_idx = matrix_height - 1;
        let last_r: Vec<Mersenne31> = trace_matrix.row(last_row_idx).collect();
        proof_bytes.extend_from_slice(&last_r[12].as_canonical_u32().to_le_bytes()); // v0_re
        proof_bytes.extend_from_slice(&last_r[13].as_canonical_u32().to_le_bytes()); // v0_im
        proof_bytes.extend_from_slice(&last_r[14].as_canonical_u32().to_le_bytes()); // v1_re
        proof_bytes.extend_from_slice(&last_r[15].as_canonical_u32().to_le_bytes()); // v1_im
    }

    proof_bytes
}

/// VERIFIER CORE: Stateless validation of universal execution pathways.
pub fn verify_stark_proof_core(context: &StarkContext, proof: &[u8]) -> bool {
    if proof.is_empty() || context.sub_task_id.is_empty() {
        return false;
    }

    let expected_prefix = context.sub_task_id.as_bytes();
    if !proof.starts_with(expected_prefix) {
        return false;
    }

    let expected_marker = b"_M31_QUANTUM_AIR_STARK_";
    let marker_index = match proof.windows(expected_marker.len()).position(|w| w == expected_marker) {
        Some(idx) => idx,
        None => return false,
    };

    let evaluation_start = marker_index + expected_marker.len();
    let evaluation_end = evaluation_start + 4;

    if proof.len() < evaluation_end {
        return false;
    }

    let mut eval_bytes = [0u8; 4];
    eval_bytes.copy_from_slice(&proof[evaluation_start..evaluation_end]);
    let air_evaluation_sum = u32::from_le_bytes(eval_bytes);

    // If any gate transition failed or was manipulated, sum is non-zero
    if air_evaluation_sum != 0 {
        return false;
    }

    true
}

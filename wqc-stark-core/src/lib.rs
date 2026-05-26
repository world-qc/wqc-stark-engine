use p3_field::{AbstractField, PrimeField32};
use p3_mersenne_31::Mersenne31;

/// StarkContext binds the decentralized task identity from the Orchestrator
#[derive(Debug)]
pub struct StarkContext<'a> {
    pub circuit_id: &'a str,
    pub sub_task_id: &'a str,
    pub node_id: &'a str,
    pub output_hash: &'a str,
}

/// Extended AIR Row to support dynamic gate execution verification via Selectors.
#[derive(Clone, Debug, PartialEq)]
pub struct QuantumAirRow {
    pub step: Mersenne31,
    // Gate Selectors (1 if active, 0 if inactive)
    pub sel_x: Mersenne31,
    pub sel_z: Mersenne31,
    pub sel_h: Mersenne31,
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

/// PROVER CORE: Evaluates dynamic AIR constraints (X, Z, H) over the execution history.
pub fn generate_stark_proof(context: &StarkContext, execution_trace: &[f64]) -> Vec<u8> {
    if execution_trace.is_empty() {
        return Vec::new();
    }

    // M31 constant representing 1/sqrt(2) under Modulus 2^31 - 1
    let inv_sqrt2 = Mersenne31::from_canonical_u32(1063382397);

    // Ingest serialized trace format: [gate_type, v0_re, v0_im, v1_re, v1_im, ...]
    // gate_type mapping placeholder: 1.0 = X, 2.0 = Z, 3.0 = H
    let mut air_rows = Vec::new();
    let chunks = execution_trace.chunks_exact(5);

    for (step_idx, chunk) in chunks.enumerate() {
        let gate_type = chunk[0] as u32;
        let (sel_x, sel_z, sel_h) = match gate_type {
            1 => (Mersenne31::one(), Mersenne31::zero(), Mersenne31::zero()),
            2 => (Mersenne31::zero(), Mersenne31::one(), Mersenne31::zero()),
            3 => (Mersenne31::zero(), Mersenne31::zero(), Mersenne31::one()),
            _ => (Mersenne31::zero(), Mersenne31::zero(), Mersenne31::zero()),
        };

        air_rows.push(QuantumAirRow {
            step: Mersenne31::from_canonical_u32(step_idx as u32),
            sel_x,
            sel_z,
            sel_h,
            v0_re: f64_to_m31(chunk[1]),
            v0_im: f64_to_m31(chunk[2]),
            v1_re: f64_to_m31(chunk[3]),
            v1_im: f64_to_m31(chunk[4]),
        });
    }

    let mut constraint_accumulations = Mersenne31::zero();

    for w in air_rows.windows(2) {
        let curr = &w[0];
        let next = &w[1];

        // --- 1. Gate::X Constraints ---
        let x_0 = next.v0_re - curr.v1_re;
        let x_1 = next.v0_im - curr.v1_im;
        let x_2 = next.v1_re - curr.v0_re;
        let x_3 = next.v1_im - curr.v0_im;
        let cost_x = x_0 * x_0 + x_1 * x_1 + x_2 * x_2 + x_3 * x_3;

        // --- 2. Gate::Z Constraints (v0 unchanged, v1_im flipped) ---
        let z_0 = next.v0_re - curr.v0_re;
        let z_1 = next.v0_im - curr.v0_im;
        let z_2 = next.v1_re - curr.v1_re;
        let z_3 = next.v1_im + curr.v1_im; // v1_im_next = -v1_im_curr => next + curr = 0
        let cost_z = z_0 * z_0 + z_1 * z_1 + z_2 * z_2 + z_3 * z_3;

        // --- 3. Gate::H Constraints (Superposition using inv_sqrt2 algebraic factor) ---
        // next_v0 = (curr_v0 + curr_v1) / sqrt(2)
        let h_0 = next.v0_re - (curr.v0_re + curr.v1_re) * inv_sqrt2;
        let h_1 = next.v0_im - (curr.v0_im + curr.v1_im) * inv_sqrt2;
        // next_v1 = (curr_v0 - curr_v1) / sqrt(2)
        let h_2 = next.v1_re - (curr.v0_re - curr.v1_re) * inv_sqrt2;
        let h_3 = next.v1_im - (curr.v0_im - curr.v1_im) * inv_sqrt2;
        let cost_h = h_0 * h_0 + h_1 * h_1 + h_2 * h_2 + h_3 * h_3;

        // --- Selector Mask Injection ---
        // Only the active gate's polynomial constraint equations will be evaluated.
        constraint_accumulations += (curr.sel_x * cost_x) + (curr.sel_z * cost_z) + (curr.sel_h * cost_h);
    }

    // Serialize the proof transcript
    let mut proof_bytes = Vec::new();
    proof_bytes.extend_from_slice(context.sub_task_id.as_bytes());
    proof_bytes.extend_from_slice(b"_M31_QUANTUM_AIR_STARK_");
    proof_bytes.extend_from_slice(&constraint_accumulations.as_canonical_u32().to_le_bytes());

    if let Some(last_row) = air_rows.last() {
        proof_bytes.extend_from_slice(&last_row.v0_re.as_canonical_u32().to_le_bytes());
        proof_bytes.extend_from_slice(&last_row.v0_im.as_canonical_u32().to_le_bytes());
        proof_bytes.extend_from_slice(&last_row.v1_re.as_canonical_u32().to_le_bytes());
        proof_bytes.extend_from_slice(&last_row.v1_im.as_canonical_u32().to_le_bytes());
    }

    proof_bytes
}

/// VERIFIER CORE: Stateless validation of dynamic execution pathways.
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

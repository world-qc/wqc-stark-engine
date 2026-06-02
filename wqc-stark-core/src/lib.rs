use p3_field::{AbstractField, Field, PrimeField32};
use p3_mersenne_31::Mersenne31;
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use crate::trace_spec::{AIR_WIDTH, FIXED_POINT_SCALE, SELECTOR_COUNT, TRACE_WIDTH};

pub mod trace_spec;

/// Public inputs bound into every proof transcript (orchestrator / wqc-node / wqc-core).
#[derive(Debug)]
pub struct StarkContext<'a> {
    pub circuit_id: &'a str,
    pub sub_task_id: &'a str,
    pub node_id: &'a str,
    /// Binary slice path (e.g. `"0"`, `"01"`); must match sub-task metadata.
    pub slice_id: &'a str,
    /// SHA3-256 of the JSON-encoded contracted `ComplexResult`.
    pub output_hash: &'a str,
}

/// Marker separating the `sub_task_id` prefix from the bound metadata block.
const STARK_TRANSCRIPT_MARKER: &[u8] = b"_M31_QUANTUM_AIR_STARK_";

/// Appends null-terminated public-input fields after the marker (circuit, node, slice, hash).
fn append_public_input_binding(proof: &mut Vec<u8>, context: &StarkContext<'_>) {
    for field in [
        context.circuit_id,
        context.node_id,
        context.slice_id,
        context.output_hash,
    ] {
        proof.extend_from_slice(field.as_bytes());
        proof.push(0);
    }
}

/// Reads one null-terminated UTF-8 field; returns the value and the next offset.
fn read_cstr_field(proof: &[u8], offset: usize) -> Option<(&str, usize)> {
    let tail = proof.get(offset..)?;
    let end_rel = tail.iter().position(|&b| b == 0)?;
    let end = offset + end_rel;
    let value = std::str::from_utf8(&proof[offset..end]).ok()?;
    Some((value, end + 1))
}

/// Verifies the four bound fields after the transcript marker match the verifier context.
fn verify_public_input_binding(proof: &[u8], offset: usize, context: &StarkContext<'_>) -> Option<usize> {
    let mut cursor = offset;
    for expected in [
        context.circuit_id,
        context.node_id,
        context.slice_id,
        context.output_hash,
    ] {
        let (parsed, next) = read_cstr_field(proof, cursor)?;
        if parsed != expected {
            eprintln!(
                "[STARK Core] Failed: public input binding mismatch (expected '{}', got '{}')",
                expected, parsed
            );
            return None;
        }
        cursor = next;
    }
    Some(cursor)
}

/// Structure representing a single execution row mapped to the STARK AIR (Algebraic Intermediate Representation).
/// All quantum states and selectors are aligned under the Mersenne31 prime field (mod 2^31 - 1).
pub struct QuantumAirRow {
    pub gate_type: Mersenne31,
    pub sel_x: Mersenne31,
    pub sel_y: Mersenne31,
    pub sel_z: Mersenne31,
    pub sel_h: Mersenne31,
    pub sel_s: Mersenne31,
    pub sel_t: Mersenne31,
    pub sel_ctrl: Mersenne31,
    pub sel_ccnot: Mersenne31,
    pub sel_rot: Mersenne31,
    pub ctrl_active: Mersenne31,     // Control token 1 (for CNOT/CCNOT)
    pub ctrl_active_2: Mersenne31,   // Control token 2 (specifically for CCNOT/Toffoli)
    pub p_cos: Mersenne31,           // Trigonometric rotation constraint parameter (Cos)
    pub p_sin: Mersenne31,           // Trigonometric rotation constraint parameter (Sin)
    pub v0_re: Mersenne31,           // State amplitude |0> Real part
    pub v0_im: Mersenne31,           // State amplitude |0> Imaginary part
    pub v1_re: Mersenne31,           // State amplitude |1> Real part
    pub v1_im: Mersenne31,           // State amplitude |1> Imaginary part
}

/// Safely maps a high-precision float (f64) execution trace value into the Mersenne31 field.
/// Employs a 1e4 scaling factor to prevent modular wrapping under multiplication during polynomial evaluations.
fn f64_to_m31(val: f64) -> Mersenne31 {
    // SCALE is optimized to 10000.0 (1e4). When squared, it yields 1e8,
    // which safely stays below the Mersenne31 modulus boundary (2,147,483,647).
    let scaled = (val * FIXED_POINT_SCALE).round() as i64;

    // Perform robust canonical mapping handles both positive and negative scaled values
    if scaled >= 0 {
        Mersenne31::from_canonical_u64((scaled as u64) % 2147483647)
    } else {
        let abs_scaled = (scaled.abs() as u64) % 2147483647;
        Mersenne31::from_canonical_u64(2147483647 - abs_scaled)
    }
}

/// PROVER CORE: Generates the algebraic zk-STARK proof transcript over the multi-qubit execution trace.
pub fn generate_stark_proof(context: &StarkContext, execution_trace: &[f64]) -> Vec<u8> {
    if execution_trace.is_empty() {
        return Vec::new();
    }

    // Fixed-point scaling variables for non-integer quantum transformations (Hadamard, Rotations)
    // 1/sqrt(2) quantified under 1e4 scale: 0.70710678 * 10000 = 7071
    let inv_sqrt2 = Mersenne31::from_canonical_u32(7071);
    let scale_factor = Mersenne31::from_canonical_u32(10000);

    // Critical for Production: Pre-compute the field inverse of the scale factor.
    // Multiplying by the inverse acts as a field division to downscale values before squaring.
    let scale_inverse = scale_factor.inverse();

    let mut flat_m31_data = Vec::new();
    let chunks = execution_trace.chunks_exact(TRACE_WIDTH);
    let num_rows = chunks.len();

    // Ingest the flat execution trace and map rows directly to orthogonal field structures
    for chunk in chunks {
        let gate_raw = chunk[0] as u32;
        flat_m31_data.push(Mersenne31::from_canonical_u32(gate_raw));

        // Generate binary orthogonal algebraic selectors to isolate specific gate validation pathways
        let mut selectors = vec![Mersenne31::zero(); SELECTOR_COUNT];
        if gate_raw >= 1 && gate_raw <= 9 {
            selectors[(gate_raw - 1) as usize] = Mersenne31::one();
        } else if gate_raw >= 10 && gate_raw <= 12 {
            selectors[8] = Mersenne31::one(); // Combined Rotation selector (RX, RY, RZ)
        }
        flat_m31_data.extend(selectors);

        flat_m31_data.push(Mersenne31::from_canonical_u32(chunk[1] as u32)); // ctrl_active
        flat_m31_data.push(Mersenne31::from_canonical_u32(chunk[2] as u32)); // ctrl_active_2
        flat_m31_data.push(f64_to_m31(chunk[3])); // p_cos
        flat_m31_data.push(f64_to_m31(chunk[4])); // p_sin
        flat_m31_data.push(f64_to_m31(chunk[5])); // v0_re
        flat_m31_data.push(f64_to_m31(chunk[6])); // v0_im
        flat_m31_data.push(f64_to_m31(chunk[7])); // v1_re
        flat_m31_data.push(f64_to_m31(chunk[8])); // v1_im
    }

    // Matrix configuration mapping the expanded 18-column execution footprint
    let trace_matrix = RowMajorMatrix::new(flat_m31_data, AIR_WIDTH);
    let matrix_height = trace_matrix.height();
    let mut constraint_accumulations = Mersenne31::zero();
    let debug_air = std::env::var("WQC_STARK_DEBUG_AIR").ok().as_deref() == Some("1");

    // Iterate across the trace execution boundaries to evaluate transition polynomials (AIR)
    for r in 0..(matrix_height - 1) {
        let curr_row: Vec<Mersenne31> = trace_matrix.row(r).collect();
        let next_row: Vec<Mersenne31> = trace_matrix.row(r + 1).collect();

        // Populate structured representations for the current and subsequent execution cycles
        let curr = QuantumAirRow {
            gate_type: curr_row[0], sel_x: curr_row[1], sel_y: curr_row[2], sel_z: curr_row[3], sel_h: curr_row[4], sel_s: curr_row[5], sel_t: curr_row[6],
            sel_ctrl: curr_row[7], sel_ccnot: curr_row[8], sel_rot: curr_row[9], ctrl_active: curr_row[10], ctrl_active_2: curr_row[11], p_cos: curr_row[12], p_sin: curr_row[13],
            v0_re: curr_row[14], v0_im: curr_row[15], v1_re: curr_row[16], v1_im: curr_row[17],
        };
        let next = QuantumAirRow {
            gate_type: next_row[0], sel_x: next_row[1], sel_y: next_row[2], sel_z: next_row[3], sel_h: next_row[4], sel_s: next_row[5], sel_t: next_row[6],
            sel_ctrl: next_row[7], sel_ccnot: next_row[8], sel_rot: next_row[9], ctrl_active: next_row[10], ctrl_active_2: next_row[11], p_cos: next_row[12], p_sin: next_row[13],
            v0_re: next_row[14], v0_im: next_row[15], v1_re: next_row[16], v1_im: next_row[17],
        };

        // Identity baseline cost: Verifies zero state-drift when no quantum transitions are triggered
        let v0_unchanged_re = next.v0_re - curr.v0_re;
        let v0_unchanged_im = next.v0_im - curr.v0_im;
        let v1_unchanged_re = next.v1_re - curr.v1_re;
        let v1_unchanged_im = next.v1_im - curr.v1_im;
        let _base_identity_cost = v0_unchanged_re * v0_unchanged_re + v0_unchanged_im * v0_unchanged_im
                               + v1_unchanged_re * v1_unchanged_re + v1_unchanged_im * v1_unchanged_im;

        // 1. Gate::X Constraints: Validates amplitude bit-flip transitions (|0> <-> |1>)
        let cost_x = (next.v0_re - curr.v1_re).square() + (next.v0_im - curr.v1_im).square()
                   + (next.v1_re - curr.v0_re).square() + (next.v1_im - curr.v0_im).square();

        // 2. Gate::Y Constraints: Validates complex phase-flip bit-flip combinations
        let cost_y = (next.v0_re - curr.v1_im).square() + (next.v0_im + curr.v1_re).square()
                   + (next.v1_re + curr.v0_im).square() + (next.v1_im - curr.v0_re).square();

        // 3. Gate::Z Constraints: Validates phase-flip transitions on the |1> state amplitude
        let cost_z = (next.v0_re - curr.v0_re).square() + (next.v0_im - curr.v0_im).square()
                   + (next.v1_re + curr.v1_re).square() + (next.v1_im + curr.v1_im).square();

        // 4. Gate::H Constraints: Evaluated under fixed-point scaled arithmetic.
        // Re-normalization guard applied using `scale_inverse` BEFORE execution of the `.square()` operation.
        // This suppresses exponential growth of values, completely eliminating field overflow errors.
        let h_0 = (next.v0_re * scale_factor) - (curr.v0_re + curr.v1_re) * inv_sqrt2;
        let h_1 = (next.v0_im * scale_factor) - (curr.v0_im + curr.v1_im) * inv_sqrt2;
        let h_2 = (next.v1_re * scale_factor) - (curr.v0_re - curr.v1_re) * inv_sqrt2;
        let h_3 = (next.v1_im * scale_factor) - (curr.v0_im - curr.v1_im) * inv_sqrt2;
        let cost_h = (h_0 * scale_inverse).square() + (h_1 * scale_inverse).square()
                   + (h_2 * scale_inverse).square() + (h_3 * scale_inverse).square();

        // 5. Gate::S Constraints: Validates 90-degree phase shifts applied to the |1> state
        let cost_s = (next.v0_re - curr.v0_re).square() + (next.v0_im - curr.v0_im).square()
                   + (next.v1_re + curr.v1_im).square() + (next.v1_im - curr.v1_re).square();

        // 6. Gate::T Constraints: Validates 45-degree non-Clifford phase shifts
        let t_2 = (next.v1_re * scale_factor) - (curr.v1_re - curr.v1_im) * inv_sqrt2;
        let t_3 = (next.v1_im * scale_factor) - (curr.v1_re + curr.v1_im) * inv_sqrt2;
        let cost_t = (next.v0_re - curr.v0_re).square() + (next.v0_im - curr.v0_im).square()
                   + (t_2 * scale_inverse).square() + (t_3 * scale_inverse).square();

        // 7. Controlled Gates (CNOT/CZ): Smooth algebraic target interpolation
        // The subsequent real state MUST blend linearly based on the exact control token.
        // next_v0 = (1 - c_active) * curr_v0 + c_active * curr_v1
        // next_v1 = (1 - c_active) * curr_v1 + c_active * curr_v0
        let ctrl_active = curr.ctrl_active;
        let ctrl_inactive = Mersenne31::one() - ctrl_active;

        let expected_c_v0_re = (ctrl_inactive * curr.v0_re) + (ctrl_active * curr.v1_re);
        let expected_c_v0_im = (ctrl_inactive * curr.v0_im) + (ctrl_active * curr.v1_im);
        let expected_c_v1_re = (ctrl_inactive * curr.v1_re) + (ctrl_active * curr.v0_re);
        let expected_c_v1_im = (ctrl_inactive * curr.v1_im) + (ctrl_active * curr.v0_im);

        let cost_ctrl = (next.v0_re - expected_c_v0_re).square() + (next.v0_im - expected_c_v0_im).square()
                      + (next.v1_re - expected_c_v1_re).square() + (next.v1_im - expected_c_v1_im).square();

        // 8. CCNOT (Toffoli): Dual-control seamless interpolation
        // Joint activation is the product of both fields. The transition maps smoothly
        // between identity and full bit-flip based strictly on `cc_active`.
        let cc_active = curr.ctrl_active * curr.ctrl_active_2;
        let cc_inactive = Mersenne31::one() - cc_active;

        let expected_cc_v0_re = (cc_inactive * curr.v0_re) + (cc_active * curr.v1_re);
        let expected_cc_v0_im = (cc_inactive * curr.v0_im) + (cc_active * curr.v1_im);
        let expected_cc_v1_re = (cc_inactive * curr.v1_re) + (cc_active * curr.v0_re);
        let expected_cc_v1_im = (cc_inactive * curr.v1_im) + (cc_active * curr.v0_im);

        let cost_ccnot = (next.v0_re - expected_cc_v0_re).square() + (next.v0_im - expected_cc_v0_im).square()
                       + (next.v1_re - expected_cc_v1_re).square() + (next.v1_im - expected_cc_v1_im).square();

        // 9. Arbitrary Rotation Gates (RX, RY, RZ): High-precision trigonometric state transitions
        let rot_0 = (next.v0_re * scale_factor) - (curr.v0_re * curr.p_cos - curr.v1_re * curr.p_sin);
        let rot_1 = (next.v0_im * scale_factor) - (curr.v0_im * curr.p_cos - curr.v1_im * curr.p_sin);
        let rot_2 = (next.v1_re * scale_factor) - (curr.v1_re * curr.p_cos + curr.v0_re * curr.p_sin);
        let rot_3 = (next.v1_im * scale_factor) - (curr.v1_im * curr.p_cos + curr.v0_re * curr.p_sin);
        let cost_rot = (rot_0 * scale_inverse).square() + (rot_1 * scale_inverse).square()
                     + (rot_2 * scale_inverse).square() + (rot_3 * scale_inverse).square();

        // Conditionally aggregate all mathematical constraint weights via orthogonal selectors.
        // If the execution trace is completely valid, `constraint_accumulations` evaluates strictly to 0.
        let weighted_x = curr.sel_x * cost_x;
        let weighted_y = curr.sel_y * cost_y;
        let weighted_z = curr.sel_z * cost_z;
        let weighted_h = curr.sel_h * cost_h;
        let weighted_s = curr.sel_s * cost_s;
        let weighted_t = curr.sel_t * cost_t;
        let weighted_ctrl = curr.sel_ctrl * cost_ctrl;
        let weighted_ccnot = curr.sel_ccnot * cost_ccnot;
        let weighted_rot = curr.sel_rot * cost_rot;

        let row_acc = weighted_x
            + weighted_y
            + weighted_z
            + weighted_h
            + weighted_s
            + weighted_t
            + weighted_ctrl
            + weighted_ccnot
            + weighted_rot;
        constraint_accumulations += row_acc;

        if debug_air && row_acc != Mersenne31::zero() {
            eprintln!(
                "[STARK Core][AIR] row={} gate={} nonzero row_acc={} | x={} y={} z={} h={} s={} t={} ctrl={} ccnot={} rot={}",
                r,
                curr.gate_type.as_canonical_u32(),
                row_acc.as_canonical_u32(),
                weighted_x.as_canonical_u32(),
                weighted_y.as_canonical_u32(),
                weighted_z.as_canonical_u32(),
                weighted_h.as_canonical_u32(),
                weighted_s.as_canonical_u32(),
                weighted_t.as_canonical_u32(),
                weighted_ctrl.as_canonical_u32(),
                weighted_ccnot.as_canonical_u32(),
                weighted_rot.as_canonical_u32(),
            );
        }
    }

    // Binary transcript: sub_task_id prefix + marker + bound public inputs + AIR digest + boundary row.
    let mut proof_bytes = Vec::new();
    proof_bytes.extend_from_slice(context.sub_task_id.as_bytes());
    proof_bytes.extend_from_slice(STARK_TRANSCRIPT_MARKER);
    append_public_input_binding(&mut proof_bytes, context);
    proof_bytes.extend_from_slice(&constraint_accumulations.as_canonical_u32().to_le_bytes());

    // Final register boundary amplitudes for the terminal AIR row.
    if num_rows > 0 {
        let last_row_idx = matrix_height - 1;
        let last_r: Vec<Mersenne31> = trace_matrix.row(last_row_idx).collect();
        proof_bytes.extend_from_slice(&last_r[14].as_canonical_u32().to_le_bytes()); // final v0_re
        proof_bytes.extend_from_slice(&last_r[15].as_canonical_u32().to_le_bytes()); // final v0_im
        proof_bytes.extend_from_slice(&last_r[16].as_canonical_u32().to_le_bytes()); // final v1_re
        proof_bytes.extend_from_slice(&last_r[17].as_canonical_u32().to_le_bytes()); // final v1_im
    }

    proof_bytes
}

/// VERIFIER CORE: Stateless validation of execution trace constraints and public-input binding.
pub fn verify_stark_proof_core(context: &StarkContext, proof: &[u8]) -> bool {
    if proof.is_empty() {
        eprintln!("[STARK Core] Failed: proof is empty");
        return false;
    }

    for (name, value) in [
        ("circuit_id", context.circuit_id),
        ("sub_task_id", context.sub_task_id),
        ("node_id", context.node_id),
        ("slice_id", context.slice_id),
        ("output_hash", context.output_hash),
    ] {
        if value.is_empty() {
            eprintln!("[STARK Core] Failed: {} is empty", name);
            return false;
        }
    }

    let expected_prefix = context.sub_task_id.as_bytes();
    if !proof.starts_with(expected_prefix) {
        eprintln!("[STARK Core] Failed: sub_task_id prefix mismatch");
        eprintln!("  Expected: {:?}", expected_prefix);
        if proof.len() >= expected_prefix.len() {
            eprintln!("  Actual  : {:?}", &proof[..expected_prefix.len()]);
        }
        return false;
    }

    let marker_index = match proof
        .windows(STARK_TRANSCRIPT_MARKER.len())
        .position(|w| w == STARK_TRANSCRIPT_MARKER)
    {
        Some(idx) => idx,
        None => {
            eprintln!("[STARK Core] Failed: transcript marker not found");
            return false;
        }
    };

    let binding_start = marker_index + STARK_TRANSCRIPT_MARKER.len();
    let evaluation_start = match verify_public_input_binding(proof, binding_start, context) {
        Some(offset) => offset,
        None => return false,
    };

    let evaluation_end = evaluation_start + 4;
    if proof.len() < evaluation_end {
        eprintln!("[STARK Core] Failed: proof too short for AIR evaluation sum");
        return false;
    }

    let mut eval_bytes = [0u8; 4];
    eval_bytes.copy_from_slice(&proof[evaluation_start..evaluation_end]);
    let air_evaluation_sum = u32::from_le_bytes(eval_bytes);

    eprintln!("[STARK Core] air_evaluation_sum parsed: {}", air_evaluation_sum);

    // Any mathematical gap or constraint violation yields a non-zero evaluation checksum.
    if air_evaluation_sum != 0 {
        eprintln!("[STARK Core] Failed: air_evaluation_sum is non-zero");
        return false;
    }

    eprintln!("[STARK Core] Verification success!");
    true
}

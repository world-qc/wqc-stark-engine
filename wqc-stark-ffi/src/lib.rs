use std::ffi::CStr;
use std::os::raw::c_char;
use std::panic::catch_unwind;
use std::slice;
use wqc_stark_core::{verify_stark_proof_core, StarkContext};

/// Foreign Function Interface (FFI) for the Go orchestrator CGO layer.
///
/// Returns: `1` = success, `0` = invalid proof/args, `-99` = panic escaped across FFI.
#[no_mangle]
pub unsafe extern "C" fn wqc_verify_stark_proof(
    circuit_id: *const c_char,
    sub_task_id: *const c_char,
    node_id: *const c_char,
    slice_id: *const c_char,
    output_hash: *const c_char,
    proof_bytes: *const u8,
    proof_len: u32,
) -> i32 {
    eprintln!(
        "[Rust FFI] verify: circuit={:?}, sub_task={:?}, slice={:?}, proof_len={}",
        circuit_id, sub_task_id, slice_id, proof_len
    );

    // Prevent Rust panics from crossing the FFI boundary into Go.
    let result = catch_unwind(|| {
        if circuit_id.is_null()
            || sub_task_id.is_null()
            || node_id.is_null()
            || slice_id.is_null()
            || output_hash.is_null()
            || proof_bytes.is_null()
        {
            eprintln!("[Rust FFI] Failed: null pointer in public inputs or proof");
            return 0;
        }

        let c_circuit = CStr::from_ptr(circuit_id).to_str().unwrap_or("");
        let c_sub_task = CStr::from_ptr(sub_task_id).to_str().unwrap_or("");
        let c_node = CStr::from_ptr(node_id).to_str().unwrap_or("");
        let c_slice = CStr::from_ptr(slice_id).to_str().unwrap_or("");
        let c_output = CStr::from_ptr(output_hash).to_str().unwrap_or("");

        let context = StarkContext {
            circuit_id: c_circuit,
            sub_task_id: c_sub_task,
            node_id: c_node,
            slice_id: c_slice,
            output_hash: c_output,
        };

        // Safely map the raw byte array pointer passed from Go memory space
        let proof_slice = slice::from_raw_parts(proof_bytes, proof_len as usize);

        if verify_stark_proof_core(&context, proof_slice) {
            1 // Signal mathematical success
        } else {
            0 // Signal constraint violation
        }
    });

    match result {
        Ok(code) => code,
        Err(_) => -99, // Emergency fallback for unexpected panics
    }
}

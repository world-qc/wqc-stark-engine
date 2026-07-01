use std::ffi::CStr;
use std::os::raw::c_char;
use std::panic::catch_unwind;
use std::slice;
use wqc_stark_core::{
    compose_stark_proofs, proof_has_unitary_statevector_link, verify_distribution_binding,
    verify_root_proof, verify_stark_proof_core, ComposeContext, RootVerifyContext, StarkContext,
};

fn cstr_or_empty<'a>(ptr: *const c_char) -> &'a str {
    if ptr.is_null() {
        return "";
    }
    unsafe { CStr::from_ptr(ptr) }.to_str().unwrap_or("")
}

fn optional_leaf_context<'a>(
    circuit_id: *const c_char,
    sub_task_id: *const c_char,
    node_id: *const c_char,
    slice_id: *const c_char,
    output_hash: *const c_char,
) -> Option<StarkContext<'a>> {
    if circuit_id.is_null() || sub_task_id.is_null() {
        return None;
    }
    let circuit = cstr_or_empty(circuit_id);
    let sub_task = cstr_or_empty(sub_task_id);
    if circuit.is_empty() || sub_task.is_empty() {
        return None;
    }
    Some(StarkContext {
        circuit_id: circuit,
        sub_task_id: sub_task,
        node_id: cstr_or_empty(node_id),
        slice_id: cstr_or_empty(slice_id),
        output_hash: cstr_or_empty(output_hash),
        terminal_statevector_digest: "",
    })
}

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

        let context = StarkContext {
            circuit_id: cstr_or_empty(circuit_id),
            sub_task_id: cstr_or_empty(sub_task_id),
            node_id: cstr_or_empty(node_id),
            slice_id: cstr_or_empty(slice_id),
            output_hash: cstr_or_empty(output_hash),
            terminal_statevector_digest: "",
        };

        let proof_slice = slice::from_raw_parts(proof_bytes, proof_len as usize);

        if verify_stark_proof_core(&context, proof_slice) {
            1
        } else {
            0
        }
    });

    match result {
        Ok(code) => code,
        Err(_) => -99,
    }
}

/// Composes two verified child proofs into a v3 proof-tree transcript.
///
/// Pass null `left_circuit_id` / `right_circuit_id` when the child is already a v3 compose node.
///
/// Returns composed byte length on success, `0` on failure, `-99` on panic.
#[no_mangle]
pub unsafe extern "C" fn wqc_compose_stark_proofs(
    parent_task_id: *const c_char,
    compose_label: *const c_char,
    manifest_root_hash: *const c_char,
    left_circuit_id: *const c_char,
    left_sub_task_id: *const c_char,
    left_node_id: *const c_char,
    left_slice_id: *const c_char,
    left_output_hash: *const c_char,
    left_proof: *const u8,
    left_proof_len: u32,
    right_circuit_id: *const c_char,
    right_sub_task_id: *const c_char,
    right_node_id: *const c_char,
    right_slice_id: *const c_char,
    right_output_hash: *const c_char,
    right_proof: *const u8,
    right_proof_len: u32,
    out_buf: *mut u8,
    out_buf_cap: u32,
) -> i32 {
    let result = catch_unwind(|| {
        if parent_task_id.is_null() || compose_label.is_null() || left_proof.is_null()
            || right_proof.is_null() || out_buf.is_null()
        {
            eprintln!("[Rust FFI] compose: null required pointer");
            return 0;
        }

        let left_slice = slice::from_raw_parts(left_proof, left_proof_len as usize);
        let right_slice = slice::from_raw_parts(right_proof, right_proof_len as usize);

        let left_ctx = optional_leaf_context(
            left_circuit_id,
            left_sub_task_id,
            left_node_id,
            left_slice_id,
            left_output_hash,
        );
        let right_ctx = optional_leaf_context(
            right_circuit_id,
            right_sub_task_id,
            right_node_id,
            right_slice_id,
            right_output_hash,
        );

        let composed = match compose_stark_proofs(
            &ComposeContext {
                parent_task_id: cstr_or_empty(parent_task_id),
                compose_label: cstr_or_empty(compose_label),
                manifest_root_hash: cstr_or_empty(manifest_root_hash),
            },
            left_slice,
            right_slice,
            left_ctx.as_ref(),
            right_ctx.as_ref(),
        ) {
            Ok(bytes) => bytes,
            Err(err) => {
                eprintln!("[Rust FFI] compose failed: {err}");
                return 0;
            }
        };

        if composed.len() > out_buf_cap as usize {
            eprintln!(
                "[Rust FFI] compose output too large: need {}, cap {}",
                composed.len(),
                out_buf_cap
            );
            return 0;
        }

        let out = slice::from_raw_parts_mut(out_buf, composed.len());
        out.copy_from_slice(&composed);
        composed.len() as i32
    });

    match result {
        Ok(code) => code,
        Err(_) => -99,
    }
}

/// Recursively verifies a v3 root proof tree for a parent task.
#[no_mangle]
pub unsafe extern "C" fn wqc_verify_root_proof(
    parent_task_id: *const c_char,
    manifest_root_hash: *const c_char,
    proof_bytes: *const u8,
    proof_len: u32,
) -> i32 {
    let result = catch_unwind(|| {
        if parent_task_id.is_null() || proof_bytes.is_null() {
            eprintln!("[Rust FFI] root verify: null pointer");
            return 0;
        }

        let proof_slice = slice::from_raw_parts(proof_bytes, proof_len as usize);
        if verify_root_proof(
            &RootVerifyContext {
                parent_task_id: cstr_or_empty(parent_task_id),
                manifest_root_hash: cstr_or_empty(manifest_root_hash),
            },
            proof_slice,
        ) {
            1
        } else {
            0
        }
    });

    match result {
        Ok(code) => code,
        Err(_) => -99,
    }
}

/// Returns 1 when the proof transcript includes a non-empty `terminal_statevector_digest` link.
#[no_mangle]
pub unsafe extern "C" fn wqc_proof_has_unitary_statevector_link(
    proof_bytes: *const u8,
    proof_len: u32,
) -> i32 {
    let result = catch_unwind(|| {
        if proof_bytes.is_null() {
            return 0;
        }
        let proof_slice = slice::from_raw_parts(proof_bytes, proof_len as usize);
        if proof_has_unitary_statevector_link(proof_slice) {
            1
        } else {
            0
        }
    });

    match result {
        Ok(code) => code,
        Err(_) => -99,
    }
}

/// Verifies distribution tail binding: Born probabilities + seed → reported counts.
///
/// `counts_json` must be canonical `{"counts":{...},"shots":N}` (orchestrator format).
/// `measurement_spec_hash` may be null/empty to skip spec binding (legacy V1 tails).
#[no_mangle]
pub unsafe extern "C" fn wqc_verify_distribution_binding(
    proof_bytes: *const u8,
    proof_len: u32,
    sample_seed: u64,
    shots: u64,
    measurement_spec_hash: *const c_char,
    counts_json: *const c_char,
) -> i32 {
    let result = catch_unwind(|| {
        if proof_bytes.is_null() || counts_json.is_null() {
            eprintln!("[Rust FFI] distribution binding: null pointer");
            return 0;
        }
        let proof_slice = slice::from_raw_parts(proof_bytes, proof_len as usize);
        let json = cstr_or_empty(counts_json);
        let (reported_counts, reported_shots) = match parse_sample_counts_json(json) {
            Some(v) => v,
            None => {
                eprintln!("[Rust FFI] distribution binding: malformed counts JSON");
                return 0;
            }
        };
        let expected_spec = {
            let s = cstr_or_empty(measurement_spec_hash);
            if s.is_empty() {
                None
            } else {
                Some(s)
            }
        };
        if verify_distribution_binding(
            proof_slice,
            sample_seed,
            shots,
            expected_spec,
            &reported_counts,
            reported_shots,
        ) {
            1
        } else {
            0
        }
    });

    match result {
        Ok(code) => code,
        Err(_) => -99,
    }
}

fn parse_sample_counts_json(
    json: &str,
) -> Option<(std::collections::BTreeMap<String, u64>, u64)> {
    #[derive(serde::Deserialize)]
    struct Payload {
        counts: std::collections::BTreeMap<String, u64>,
        shots: u64,
    }
    let payload: Payload = serde_json::from_str(json).ok()?;
    Some((payload.counts, payload.shots))
}

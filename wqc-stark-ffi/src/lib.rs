use std::ffi::CStr;
use std::os::raw::c_char;
use std::panic::catch_unwind;
use std::slice;
use wqc_stark_core::{
    build_encoded_leaf_pcs_bundle_from_child, compose_stark_proofs_with_pcs,
    decode_leaf_pcs_bundle_bytes, generate_stark_proof, is_unitary_born_leaf_compose,
    is_unitary_trajectory_leaf_compose, proof_has_trajectory_unitary_link,
    proof_has_unitary_statevector_link, trajectory_proof_view, verify_distribution_binding,
    verify_leaf_pcs_bundle, verify_root_proof, verify_stark_proof_core, verify_trajectory_binding,
    ComposeContext, RootVerifyContext, StarkContext,
};

fn unwind_to_ffi_code(result: Result<i32, Box<dyn std::any::Any + Send>>) -> i32 {
    result.unwrap_or(-99)
}

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
    security_level: &'a str,
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
        measurement_spec_hash: "",
        security_level,
    })
}

/// Foreign Function Interface (FFI) for the Go orchestrator CGO layer.
///
/// Returns: `1` = success, `0` = invalid proof/args, `-99` = panic escaped across FFI.
///
/// # Safety
///
/// All pointer arguments must be valid for the duration of this call. String pointers
/// must be null-terminated UTF-8. `proof_bytes` must reference at least `proof_len` bytes.
#[no_mangle]
pub unsafe extern "C" fn wqc_verify_stark_proof(
    circuit_id: *const c_char,
    sub_task_id: *const c_char,
    node_id: *const c_char,
    slice_id: *const c_char,
    output_hash: *const c_char,
    security_level: *const c_char,
    measurement_spec_hash: *const c_char,
    proof_bytes: *const u8,
    proof_len: u32,
) -> i32 {
    eprintln!(
        "[Rust FFI] verify: circuit={:?}, sub_task={:?}, slice={:?}, security={:?}, proof_len={}",
        circuit_id, sub_task_id, slice_id, security_level, proof_len
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
            measurement_spec_hash: cstr_or_empty(measurement_spec_hash),
            security_level: cstr_or_empty(security_level),
        };

        let proof_slice = slice::from_raw_parts(proof_bytes, proof_len as usize);

        if verify_stark_proof_core(&context, proof_slice) {
            1
        } else {
            0
        }
    });

    unwind_to_ffi_code(result)
}

/// Composes two verified child proofs into a v3 proof-tree transcript.
///
/// Pass null `left_circuit_id` / `right_circuit_id` when the child is already a v3 compose node.
/// Optional `left_pcs` / `right_pcs` are prebuilt leaf PCS bundles (`null` / len 0 = fallback build).
///
/// Returns composed byte length on success, `0` on failure, `-2` if `out_buf_cap`
/// is too small (retry with a larger buffer), `-99` on panic.
///
/// # Safety
///
/// Required pointers must be valid for the duration of this call. Proof slices must
/// reference at least `left_proof_len` / `right_proof_len` bytes. `out_buf` must be
/// writable for at least `out_buf_cap` bytes.
#[no_mangle]
pub unsafe extern "C" fn wqc_compose_stark_proofs(
    parent_task_id: *const c_char,
    compose_label: *const c_char,
    manifest_root_hash: *const c_char,
    security_level: *const c_char,
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
    left_pcs: *const u8,
    left_pcs_len: u32,
    right_pcs: *const u8,
    right_pcs_len: u32,
    out_buf: *mut u8,
    out_buf_cap: u32,
) -> i32 {
    let result = catch_unwind(|| {
        if parent_task_id.is_null()
            || compose_label.is_null()
            || left_proof.is_null()
            || right_proof.is_null()
            || out_buf.is_null()
        {
            eprintln!("[Rust FFI] compose: null required pointer");
            return 0;
        }

        let left_slice = slice::from_raw_parts(left_proof, left_proof_len as usize);
        let right_slice = slice::from_raw_parts(right_proof, right_proof_len as usize);
        let left_pcs_slice = optional_bytes(left_pcs, left_pcs_len);
        let right_pcs_slice = optional_bytes(right_pcs, right_pcs_len);

        let compose_security = cstr_or_empty(security_level);
        let left_ctx = optional_leaf_context(
            left_circuit_id,
            left_sub_task_id,
            left_node_id,
            left_slice_id,
            left_output_hash,
            compose_security,
        );
        let right_ctx = optional_leaf_context(
            right_circuit_id,
            right_sub_task_id,
            right_node_id,
            right_slice_id,
            right_output_hash,
            compose_security,
        );

        let composed = match compose_stark_proofs_with_pcs(
            &ComposeContext {
                parent_task_id: cstr_or_empty(parent_task_id),
                compose_label: cstr_or_empty(compose_label),
                manifest_root_hash: cstr_or_empty(manifest_root_hash),
                security_level: compose_security,
            },
            left_slice,
            right_slice,
            left_ctx.as_ref(),
            right_ctx.as_ref(),
            left_pcs_slice,
            right_pcs_slice,
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
            return -2;
        }

        let out = slice::from_raw_parts_mut(out_buf, composed.len());
        out.copy_from_slice(&composed);
        composed.len() as i32
    });

    unwind_to_ffi_code(result)
}

/// Builds an encoded leaf PCS bundle from a leaf STARK proof.
///
/// Returns encoded byte length on success, `0` on failure, `-2` if `out_buf_cap`
/// is too small, `-99` on panic.
///
/// # Safety
///
/// `proof` must reference at least `proof_len` bytes. `out_buf` must be writable
/// for at least `out_buf_cap` bytes.
#[no_mangle]
pub unsafe extern "C" fn wqc_build_leaf_pcs_bundle(
    proof: *const u8,
    proof_len: u32,
    out_buf: *mut u8,
    out_buf_cap: u32,
) -> i32 {
    let result = catch_unwind(|| {
        if proof.is_null() || out_buf.is_null() {
            eprintln!("[Rust FFI] build_leaf_pcs: null required pointer");
            return 0;
        }
        let proof_slice = slice::from_raw_parts(proof, proof_len as usize);
        let encoded = match build_encoded_leaf_pcs_bundle_from_child(proof_slice) {
            Ok(bytes) => bytes,
            Err(err) => {
                eprintln!("[Rust FFI] build_leaf_pcs failed: {err}");
                return 0;
            }
        };
        if encoded.len() > out_buf_cap as usize {
            eprintln!(
                "[Rust FFI] build_leaf_pcs output too large: need {}, cap {}",
                encoded.len(),
                out_buf_cap
            );
            return -2;
        }
        let out = slice::from_raw_parts_mut(out_buf, encoded.len());
        out.copy_from_slice(&encoded);
        encoded.len() as i32
    });
    unwind_to_ffi_code(result)
}

/// Verifies an encoded leaf PCS bundle against its leaf STARK proof.
///
/// Returns `1` on success, `0` on verification/decode failure, `-99` on panic.
///
/// # Safety
///
/// `proof` / `pcs_bundle` must reference at least `proof_len` / `pcs_len` bytes.
#[no_mangle]
pub unsafe extern "C" fn wqc_verify_leaf_pcs_bundle(
    proof: *const u8,
    proof_len: u32,
    pcs_bundle: *const u8,
    pcs_len: u32,
) -> i32 {
    let result = catch_unwind(|| {
        if proof.is_null() || pcs_bundle.is_null() || proof_len == 0 || pcs_len == 0 {
            eprintln!("[Rust FFI] verify_leaf_pcs: null/empty required pointer");
            return 0;
        }
        let proof_slice = slice::from_raw_parts(proof, proof_len as usize);
        let pcs_slice = slice::from_raw_parts(pcs_bundle, pcs_len as usize);
        let bundle = match decode_leaf_pcs_bundle_bytes(pcs_slice) {
            Some(b) => b,
            None => {
                eprintln!("[Rust FFI] verify_leaf_pcs: decode failed");
                return 0;
            }
        };
        match verify_leaf_pcs_bundle(proof_slice, &bundle) {
            Ok(()) => 1,
            Err(err) => {
                eprintln!("[Rust FFI] verify_leaf_pcs failed: {err}");
                0
            }
        }
    });
    unwind_to_ffi_code(result)
}

fn optional_bytes<'a>(ptr: *const u8, len: u32) -> Option<&'a [u8]> {
    if ptr.is_null() || len == 0 {
        return None;
    }
    Some(unsafe { slice::from_raw_parts(ptr, len as usize) })
}

/// Generates a minimal idle-qubit leaf proof for orch CGO RecAgg V6 compose E2E.
///
/// Uses the lightweight v1 AIR leaf (same idle trace as engine integration tests).
/// Compose still appends AggregationAir + RecAgg V6 tails via `wqc_compose_stark_proofs`.
///
/// Returns proof length on success, `0` on failure, `-2` if `out_buf_cap` is too small,
/// `-99` on panic.
///
/// # Safety
///
/// String pointers must be null-terminated UTF-8. `out_buf` must be writable for at
/// least `out_buf_cap` bytes.
#[no_mangle]
pub unsafe extern "C" fn wqc_generate_demo_leaf_proof(
    circuit_id: *const c_char,
    sub_task_id: *const c_char,
    node_id: *const c_char,
    slice_id: *const c_char,
    output_hash: *const c_char,
    out_buf: *mut u8,
    out_buf_cap: u32,
) -> i32 {
    let result = catch_unwind(|| {
        if circuit_id.is_null()
            || sub_task_id.is_null()
            || node_id.is_null()
            || slice_id.is_null()
            || output_hash.is_null()
            || out_buf.is_null()
        {
            eprintln!("[Rust FFI] demo leaf: null required pointer");
            return 0;
        }
        let context = StarkContext {
            circuit_id: cstr_or_empty(circuit_id),
            sub_task_id: cstr_or_empty(sub_task_id),
            node_id: cstr_or_empty(node_id),
            slice_id: cstr_or_empty(slice_id),
            output_hash: cstr_or_empty(output_hash),
            terminal_statevector_digest: "",
            measurement_spec_hash: "",
            security_level: "",
        };
        let proof =
            generate_stark_proof(&context, &wqc_stark_core::trace_spec::idle_qubit0_trace());
        if proof.is_empty() {
            eprintln!("[Rust FFI] demo leaf prove returned empty");
            return 0;
        }
        if proof.len() > out_buf_cap as usize {
            eprintln!(
                "[Rust FFI] demo leaf too large: need {}, cap {}",
                proof.len(),
                out_buf_cap
            );
            return -2;
        }
        let out = slice::from_raw_parts_mut(out_buf, proof.len());
        out.copy_from_slice(&proof);
        proof.len() as i32
    });
    unwind_to_ffi_code(result)
}

/// Recursively verifies a v3 root proof tree for a parent task.
///
/// # Safety
///
/// `parent_task_id` and `proof_bytes` must be valid for the duration of this call.
/// `proof_bytes` must reference at least `proof_len` bytes.
#[no_mangle]
pub unsafe extern "C" fn wqc_verify_root_proof(
    parent_task_id: *const c_char,
    manifest_root_hash: *const c_char,
    security_level: *const c_char,
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
                security_level: cstr_or_empty(security_level),
            },
            proof_slice,
        ) {
            1
        } else {
            0
        }
    });

    unwind_to_ffi_code(result)
}

/// Returns 1 when the proof transcript includes a non-empty `terminal_statevector_digest` link.
///
/// # Safety
///
/// `proof_bytes` must reference at least `proof_len` bytes when non-null.
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

    unwind_to_ffi_code(result)
}

/// Returns 1 when the proof transcript includes a C2c trajectory marginal Plonky3 tail.
///
/// # Safety
///
/// `proof_bytes` must reference at least `proof_len` bytes when non-null.
#[no_mangle]
pub unsafe extern "C" fn wqc_has_trajectory_zk_tail(proof_bytes: *const u8, proof_len: u32) -> i32 {
    let result = catch_unwind(|| {
        if proof_bytes.is_null() {
            return 0;
        }
        let proof_slice = slice::from_raw_parts(proof_bytes, proof_len as usize);
        if wqc_stark_core::plonky3_stark::has_trajectory_stark_tail(trajectory_proof_view(
            proof_slice,
        )) {
            return 1;
        }
        0
    });

    unwind_to_ffi_code(result)
}

/// Returns 1 when the proof transcript includes a per-shot sampling STARK inner marker.
///
/// # Safety
///
/// `proof_bytes` must reference at least `proof_len` bytes when non-null.
#[no_mangle]
pub unsafe extern "C" fn wqc_has_trajectory_shot_sampling(
    proof_bytes: *const u8,
    proof_len: u32,
) -> i32 {
    let result = catch_unwind(|| {
        if proof_bytes.is_null() {
            return 0;
        }
        let proof_slice = slice::from_raw_parts(proof_bytes, proof_len as usize);
        if wqc_stark_core::plonky3_stark::has_trajectory_shot_sampling_stark(trajectory_proof_view(
            proof_slice,
        )) {
            return 1;
        }
        0
    });

    unwind_to_ffi_code(result)
}

/// Returns 1 when the proof transcript includes a non-empty trajectory `unitary_link_digest`.
///
/// # Safety
///
/// `proof_bytes` must reference at least `proof_len` bytes when non-null.
#[no_mangle]
pub unsafe extern "C" fn wqc_proof_has_trajectory_unitary_link(
    proof_bytes: *const u8,
    proof_len: u32,
) -> i32 {
    let result = catch_unwind(|| {
        if proof_bytes.is_null() {
            return 0;
        }
        let proof_slice = slice::from_raw_parts(proof_bytes, proof_len as usize);
        if proof_has_trajectory_unitary_link(proof_slice) {
            1
        } else {
            0
        }
    });

    unwind_to_ffi_code(result)
}

/// Returns 1 when the proof is a v3 `leaf:unitary_traj` compose transcript.
///
/// # Safety
///
/// `proof_bytes` must reference at least `proof_len` bytes when non-null.
#[no_mangle]
pub unsafe extern "C" fn wqc_is_unitary_trajectory_compose(
    proof_bytes: *const u8,
    proof_len: u32,
) -> i32 {
    let result = catch_unwind(|| {
        if proof_bytes.is_null() {
            return 0;
        }
        let proof_slice = slice::from_raw_parts(proof_bytes, proof_len as usize);
        if is_unitary_trajectory_leaf_compose(proof_slice) {
            1
        } else {
            0
        }
    });

    unwind_to_ffi_code(result)
}

/// Returns 1 when the proof is a v3 `leaf:unitary_born` compose transcript.
///
/// # Safety
///
/// `proof_bytes` must reference at least `proof_len` bytes when non-null.
#[no_mangle]
pub unsafe extern "C" fn wqc_is_unitary_born_compose(
    proof_bytes: *const u8,
    proof_len: u32,
) -> i32 {
    let result = catch_unwind(|| {
        if proof_bytes.is_null() {
            return 0;
        }
        let proof_slice = slice::from_raw_parts(proof_bytes, proof_len as usize);
        if is_unitary_born_leaf_compose(proof_slice) {
            1
        } else {
            0
        }
    });

    unwind_to_ffi_code(result)
}

/// Verifies trajectory tail binding: shot outcomes + seed → reported counts.
///
/// `measurement_spec_hash` is required (non-null, non-empty).
///
/// # Safety
///
/// `proof_bytes` must reference at least `proof_len` bytes. `counts_json` and
/// `measurement_spec_hash` must be null-terminated UTF-8.
#[no_mangle]
pub unsafe extern "C" fn wqc_verify_trajectory_binding(
    proof_bytes: *const u8,
    proof_len: u32,
    sample_seed: u64,
    shots: u64,
    measurement_spec_hash: *const c_char,
    counts_json: *const c_char,
) -> i32 {
    let result = catch_unwind(|| {
        if proof_bytes.is_null() || counts_json.is_null() || measurement_spec_hash.is_null() {
            eprintln!("[Rust FFI] trajectory binding: null pointer");
            return 0;
        }
        let expected_spec = cstr_or_empty(measurement_spec_hash);
        if expected_spec.is_empty() {
            eprintln!("[Rust FFI] trajectory binding: measurement_spec_hash required");
            return 0;
        }
        let proof_slice = slice::from_raw_parts(proof_bytes, proof_len as usize);
        let json = cstr_or_empty(counts_json);
        let (reported_counts, reported_shots) = match parse_sample_counts_json(json) {
            Some(v) => v,
            None => {
                eprintln!("[Rust FFI] trajectory binding: malformed counts JSON");
                return 0;
            }
        };
        if verify_trajectory_binding(
            proof_slice,
            sample_seed,
            shots,
            Some(expected_spec),
            &reported_counts,
            reported_shots,
        ) {
            1
        } else {
            0
        }
    });

    unwind_to_ffi_code(result)
}

/// Verifies distribution tail binding: Born probabilities + seed → reported counts.
///
/// `counts_json` must be canonical `{"counts":{...},"shots":N}` (orchestrator format).
/// `measurement_spec_hash` is required (non-null, non-empty) — matches orch fail-closed policy.
///
/// # Safety
///
/// `proof_bytes` must reference at least `proof_len` bytes. `counts_json` and
/// `measurement_spec_hash` must be null-terminated UTF-8.
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
        if proof_bytes.is_null() || counts_json.is_null() || measurement_spec_hash.is_null() {
            eprintln!("[Rust FFI] distribution binding: null pointer");
            return 0;
        }
        let expected_spec = cstr_or_empty(measurement_spec_hash);
        if expected_spec.is_empty() {
            eprintln!("[Rust FFI] distribution binding: measurement_spec_hash required");
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
        if verify_distribution_binding(
            proof_slice,
            sample_seed,
            shots,
            Some(expected_spec),
            &reported_counts,
            reported_shots,
        ) {
            1
        } else {
            0
        }
    });

    unwind_to_ffi_code(result)
}

fn parse_sample_counts_json(json: &str) -> Option<(std::collections::BTreeMap<String, u64>, u64)> {
    #[derive(serde::Deserialize)]
    struct Payload {
        counts: std::collections::BTreeMap<String, u64>,
        shots: u64,
    }
    let payload: Payload = serde_json::from_str(json).ok()?;
    Some((payload.counts, payload.shots))
}

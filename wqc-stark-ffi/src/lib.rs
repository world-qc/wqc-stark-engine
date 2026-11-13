use std::ffi::CStr;
use std::os::raw::c_char;
use std::panic::catch_unwind;
use std::slice;
use wqc_stark_core::{
    build_encoded_leaf_pcs_bundle_from_child, compose_stark_proofs_with_pcs,
    decode_leaf_pcs_bundle_bytes, generate_stark_proof, has_overlap_tail,
    is_unitary_born_leaf_compose, is_unitary_trajectory_leaf_compose,
    proof_has_trajectory_unitary_link, proof_has_unitary_statevector_link, trajectory_proof_view,
    verify_distribution_binding, verify_leaf_pcs_bundle, verify_overlap_binding, verify_root_proof,
    verify_stark_proof_core, verify_trajectory_binding, ComposeContext, RootVerifyContext,
    StarkContext,
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
            Err(_err) => {
                eprintln!("[Rust FFI] build_leaf_pcs failed");
                return 0;
            }
        };
        if encoded.len() > out_buf_cap as usize {
            eprintln!("[Rust FFI] build_leaf_pcs output too large");
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
            Err(_err) => {
                eprintln!("[Rust FFI] verify_leaf_pcs failed");
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

/// Returns 1 when the proof transcript includes an overlap tail.
///
/// # Safety
///
/// `proof_bytes` must reference at least `proof_len` bytes.
#[no_mangle]
pub unsafe extern "C" fn wqc_has_overlap_tail(proof_bytes: *const u8, proof_len: u32) -> i32 {
    let result = catch_unwind(|| {
        if proof_bytes.is_null() {
            return 0;
        }
        let proof_slice = slice::from_raw_parts(proof_bytes, proof_len as usize);
        if has_overlap_tail(proof_slice) {
            1
        } else {
            0
        }
    });
    unwind_to_ffi_code(result)
}

/// Verifies overlap tail binding to `output_result_hash`.
///
/// # Safety
///
/// `proof_bytes` must reference at least `proof_len` bytes.
/// `output_hash` must be null-terminated UTF-8.
#[no_mangle]
pub unsafe extern "C" fn wqc_verify_overlap_binding(
    proof_bytes: *const u8,
    proof_len: u32,
    output_hash: *const c_char,
) -> i32 {
    let result = catch_unwind(|| {
        if proof_bytes.is_null() || output_hash.is_null() {
            eprintln!("[Rust FFI] overlap binding: null pointer");
            return 0;
        }
        let expected = cstr_or_empty(output_hash);
        if expected.is_empty() {
            eprintln!("[Rust FFI] overlap binding: output_hash required");
            return 0;
        }
        let proof_slice = slice::from_raw_parts(proof_bytes, proof_len as usize);
        if verify_overlap_binding(proof_slice, expected) {
            1
        } else {
            0
        }
    });
    unwind_to_ffi_code(result)
}

// ---------------------------------------------------------------------------------------------
// State-vector leaf (v2, `wqc-sv-stark`)
// ---------------------------------------------------------------------------------------------

use std::panic::AssertUnwindSafe;
use wqc_sv_stark::born::Sampling;
use wqc_sv_stark::leaf::{gate_rows, LeafVerifier};
use wqc_sv_stark::wire::{parse_circuit, parse_counts, parse_leaf};

/// A v2 leaf's verifier, opaque to C. Verifying through it from several threads at once is
/// safe; free it once with [`wqc_sv_leaf_free`].
pub struct WqcSvLeaf(LeafVerifier);

const _: fn() = || {
    fn shared<T: Send + Sync>() {}
    shared::<WqcSvLeaf>();
};

/// A required string: null or invalid UTF-8 is `None` (an empty string is a value).
fn cstr<'a>(ptr: *const c_char) -> Option<&'a str> {
    if ptr.is_null() {
        return None;
    }
    unsafe { CStr::from_ptr(ptr) }.to_str().ok()
}

/// Gate rows `W` of the v2 leaf for `circuit_json` on `qubit_count` qubits (rounding steps ×
/// 2^(n−1)): the work that sets a leaf's proving time and memory, for scheduling and TTLs.
/// `circuit_json` is wqc-core's gate list, read by `wire::parse_leaf`: a mid-circuit circuit
/// (RESET, IF, a gate after a MEASURE) is counted as its rewritten unitary circuit, whose `n`
/// includes one ancilla per RESET that needs one. MEASUREs are allowed and their qubits
/// checked; their cbits are not (the register size is not an argument), so
/// `wqc_sv_leaf_new` can still reject a circuit this accepts. It does not apply the leaf's
/// row limit (`wqc_sv_max_rows`), so a scheduler can see how far over a circuit is.
///
/// A `sample_counts` leaf has further tables (weights, draws, counts) this does not count;
/// with many shots and few qubits they outweigh the gate rows, so `W` alone underestimates
/// such a leaf.
///
/// Returns the row count (≥ 0), `-1` if the circuit has no v2 leaf (bad JSON, a gate on a
/// measured qubit before its RESET, an IF of CCNOT or of a non-unitary gate, a gate or MEASURE
/// qubit outside `qubit_count`, more than 16 qubits with ancillas), or `-99` on panic.
///
/// # Safety
///
/// `circuit_json` must be a null-terminated string valid for the duration of this call.
#[no_mangle]
pub unsafe extern "C" fn wqc_sv_leaf_rows(qubit_count: u32, circuit_json: *const c_char) -> i64 {
    let result = catch_unwind(|| {
        let Some(json) = cstr(circuit_json) else {
            eprintln!("[Rust FFI] sv_leaf_rows: null or non-UTF-8 circuit");
            return -1;
        };
        let n = qubit_count as usize;
        let rows = parse_leaf(json, n).and_then(|c| {
            if let Some(m) = c.measures.iter().find(|m| m.qubit >= c.qubits) {
                return Err(wqc_sv_stark::Error::InvalidCircuit(format!(
                    "MEASURE of qubit {} with {n} qubits",
                    m.qubit
                )));
            }
            gate_rows(c.qubits, &c.gates)
        });
        match rows {
            Ok(rows) => rows as i64,
            Err(err) => {
                eprintln!("[Rust FFI] sv_leaf_rows: {err}");
                -1
            }
        }
    });
    result.unwrap_or(-99)
}

/// An upper estimate, in bytes, of the memory `wqc_sv_leaf_new` peaks at for a leaf of `rows`
/// gate rows (`wqc_sv_leaf_rows`) on `qubit_count` qubits with `shots` (0 for
/// `statevector_scalar`). The orchestrator compares it with the memory it can spare to decide
/// which circuits it can verify as v2, so the limit follows the machine (about 2^21 rows in
/// 1.4 GB, 2^22 in 2 GB). It does not check the arguments; out-of-range ones saturate to
/// `u64::MAX`.
#[no_mangle]
pub extern "C" fn wqc_sv_verifier_peak_bytes(qubit_count: u32, rows: u64, shots: u64) -> u64 {
    wqc_sv_stark::leaf::verifier_peak_bytes(qubit_count as usize, rows as usize, shots)
}

/// The most gate rows a v2 leaf may have (`2^22`); a circuit over it has no v2 leaf.
#[no_mangle]
pub extern "C" fn wqc_sv_max_rows() -> i64 {
    wqc_sv_stark::MAX_ROWS as i64
}

/// Builds the verifier of a v2 leaf, to cache per circuit (`leaf::build_verifier`: the
/// preprocessed commitment a run of rows at a time, no proving data). Building peaks at about
/// 370 bytes of memory per gate row and takes about 4 µs per row on an 8-core machine (1.45 GB
/// and 16 s at the 2^22-row limit); the handle keeps under 1 MB.
///
/// - `shots == 0`: a `statevector_scalar` leaf; `circuit_json` must have no MEASURE.
/// - `shots > 0`: a `sample_counts` leaf over the circuit as `wire::parse_leaf` reads it
///   (mid-circuit MEASURE, RESET and IF rewritten into unitary gates and terminal MEASUREs on
///   `qubit_count` qubits plus ancillas), with `classical_bit_count` classical bits (1..=16)
///   and `shots` (at most 2^16).
///
/// `security_level` is the dispatched tier (`low|normal|high|ultra`, empty = `ultra`); a proof
/// made at another tier fails this verifier. Returns null on any error.
///
/// # Safety
///
/// `circuit_json` and `security_level` must be null-terminated strings valid for the duration
/// of this call.
#[no_mangle]
pub unsafe extern "C" fn wqc_sv_leaf_new(
    qubit_count: u32,
    circuit_json: *const c_char,
    classical_bit_count: u32,
    shots: u64,
    security_level: *const c_char,
) -> *mut WqcSvLeaf {
    let result = catch_unwind(|| {
        let (Some(json), Some(level)) = (cstr(circuit_json), cstr(security_level)) else {
            eprintln!("[Rust FFI] sv_leaf_new: null or non-UTF-8 argument");
            return std::ptr::null_mut();
        };
        let Some(level) = wqc_sv_stark::SecurityLevel::parse(level) else {
            eprintln!("[Rust FFI] sv_leaf_new: unknown security level {level:?}");
            return std::ptr::null_mut();
        };
        let n = qubit_count as usize;
        let built = if shots == 0 {
            parse_circuit(json).and_then(|c| {
                if !c.measures.is_empty() {
                    return Err(wqc_sv_stark::Error::InvalidCircuit(
                        "MEASURE in a circuit without shots".into(),
                    ));
                }
                wqc_sv_stark::leaf::build_verifier(level, n, c.gates, None)
            })
        } else {
            parse_leaf(json, n).and_then(|c| {
                let shots = u32::try_from(shots)
                    .map_err(|_| wqc_sv_stark::Error::InvalidCircuit(format!("{shots} shots")))?;
                let sampling = Sampling {
                    measures: c.measures,
                    cbits: classical_bit_count as usize,
                    shots,
                };
                wqc_sv_stark::leaf::build_verifier(level, c.qubits, c.gates, Some(sampling))
            })
        };
        match built {
            Ok(verifier) => Box::into_raw(Box::new(WqcSvLeaf(verifier))),
            Err(err) => {
                eprintln!("[Rust FFI] sv_leaf_new: {err}");
                std::ptr::null_mut()
            }
        }
    });
    result.unwrap_or(std::ptr::null_mut())
}

/// Frees a verifier from [`wqc_sv_leaf_new`]. Null is a no-op.
///
/// # Safety
///
/// `leaf` must come from [`wqc_sv_leaf_new`], be freed once, and not be in use.
#[no_mangle]
pub unsafe extern "C" fn wqc_sv_leaf_free(leaf: *mut WqcSvLeaf) {
    if !leaf.is_null() {
        drop(Box::from_raw(leaf));
    }
}

/// The dispatch a leaf proof is bound to, as the orchestrator signed it (no normalization).
unsafe fn dispatch<'a>(
    circuit_id: *const c_char,
    sub_task_id: *const c_char,
    node_id: *const c_char,
    slice_id: *const c_char,
) -> Option<wqc_sv_stark::leaf::Dispatch<'a>> {
    Some(wqc_sv_stark::leaf::Dispatch {
        circuit_id: cstr(circuit_id)?,
        sub_task_id: cstr(sub_task_id)?,
        node_id: cstr(node_id)?,
        slice_id: cstr(slice_id)?,
    })
}

/// Shared checks of the two verify calls: the handle, the dispatch, the digest and the proof.
unsafe fn leaf_inputs<'a>(
    what: &str,
    leaf: *const WqcSvLeaf,
    dispatch_fields: [*const c_char; 4],
    digest: *const u64,
    proof_bytes: *const u8,
    proof_len: u32,
) -> Option<(
    &'a LeafVerifier,
    wqc_sv_stark::leaf::Dispatch<'a>,
    [u64; 4],
    &'a [u8],
)> {
    if leaf.is_null() || digest.is_null() || proof_bytes.is_null() {
        eprintln!("[Rust FFI] {what}: null pointer");
        return None;
    }
    let [c, s, n, sl] = dispatch_fields;
    let Some(d) = dispatch(c, s, n, sl) else {
        eprintln!("[Rust FFI] {what}: null or non-UTF-8 dispatch field");
        return None;
    };
    let digest: [u64; 4] = slice::from_raw_parts(digest, 4).try_into().ok()?;
    let proof = slice::from_raw_parts(proof_bytes, proof_len as usize);
    Some((&(*leaf).0, d, digest, proof))
}

/// Verifies a `statevector_scalar` v2 leaf proof for its dispatch and the expected terminal
/// state digest (four canonical words: the quorum's, never the prover's own claim).
///
/// Returns `1` = valid, `0` = invalid proof or arguments (including a sampling verifier),
/// `-99` = panic.
///
/// # Safety
///
/// `leaf` must be a live handle from [`wqc_sv_leaf_new`]. String pointers must be
/// null-terminated. `digest` must point to 4 `u64`s and `proof_bytes` to `proof_len` bytes.
#[no_mangle]
pub unsafe extern "C" fn wqc_sv_verify_leaf(
    leaf: *const WqcSvLeaf,
    circuit_id: *const c_char,
    sub_task_id: *const c_char,
    node_id: *const c_char,
    slice_id: *const c_char,
    digest: *const u64,
    proof_bytes: *const u8,
    proof_len: u32,
) -> i32 {
    let result = catch_unwind(AssertUnwindSafe(|| {
        let Some((v, d, digest, proof)) = leaf_inputs(
            "sv_verify_leaf",
            leaf,
            [circuit_id, sub_task_id, node_id, slice_id],
            digest,
            proof_bytes,
            proof_len,
        ) else {
            return 0;
        };
        if v.sampling().is_some() {
            eprintln!("[Rust FFI] sv_verify_leaf: a sampling leaf needs its seed and counts");
            return 0;
        }
        match v.verify_dispatch(proof, &d, digest) {
            Ok(()) => 1,
            Err(err) => {
                eprintln!("[Rust FFI] sv_verify_leaf: {err}");
                0
            }
        }
    }));
    unwind_to_ffi_code(result)
}

/// Verifies a `sample_counts` v2 leaf proof for its dispatch, the expected terminal state
/// digest, the dispatched `sample_seed`, and the reported counts. `counts_json` must be the
/// canonical `{"counts":{...},"shots":N}` (keys of exactly `classical_bit_count` bits, no zero
/// counts, `shots` and the sum equal to the verifier's shots).
///
/// Returns `1` = valid, `0` = invalid proof or arguments, `-99` = panic.
///
/// # Safety
///
/// As [`wqc_sv_verify_leaf`]; `counts_json` must be null-terminated.
#[no_mangle]
pub unsafe extern "C" fn wqc_sv_verify_sampling_leaf(
    leaf: *const WqcSvLeaf,
    circuit_id: *const c_char,
    sub_task_id: *const c_char,
    node_id: *const c_char,
    slice_id: *const c_char,
    digest: *const u64,
    sample_seed: u64,
    counts_json: *const c_char,
    proof_bytes: *const u8,
    proof_len: u32,
) -> i32 {
    let result = catch_unwind(AssertUnwindSafe(|| {
        let Some((v, d, digest, proof)) = leaf_inputs(
            "sv_verify_sampling_leaf",
            leaf,
            [circuit_id, sub_task_id, node_id, slice_id],
            digest,
            proof_bytes,
            proof_len,
        ) else {
            return 0;
        };
        let Some(sampling) = v.sampling() else {
            eprintln!("[Rust FFI] sv_verify_sampling_leaf: not a sampling leaf");
            return 0;
        };
        let Some(json) = cstr(counts_json) else {
            eprintln!("[Rust FFI] sv_verify_sampling_leaf: null or non-UTF-8 counts");
            return 0;
        };
        let checked = parse_counts(json, sampling)
            .and_then(|counts| v.verify_sampling(proof, &d, digest, sample_seed, &counts));
        match checked {
            Ok(()) => 1,
            Err(err) => {
                eprintln!("[Rust FFI] sv_verify_sampling_leaf: {err}");
                0
            }
        }
    }));
    unwind_to_ffi_code(result)
}

/// One leaf of [`wqc_sv_verify_root`]: its circuit, as for [`wqc_sv_leaf_new`], and the
/// dispatch and result the orchestrator accepted, as for [`wqc_sv_verify_sampling_leaf`]
/// (`shots == 0`: a `statevector_scalar` leaf, without seed and counts).
#[derive(serde::Deserialize)]
struct RootLeaf {
    qubit_count: u32,
    circuit: String,
    #[serde(default)]
    classical_bit_count: u32,
    #[serde(default)]
    shots: u64,
    security_level: String,
    circuit_id: String,
    sub_task_id: String,
    node_id: String,
    slice_id: String,
    digest: [u64; 4],
    #[serde(default)]
    sample_seed: u64,
    #[serde(default)]
    counts: String,
    /// The leaf proof (standard base64): it fixes the layer's shape, the expected statement
    /// is built from the fields above.
    proof: String,
}

#[derive(serde::Deserialize)]
struct RootInput {
    leaves: Vec<RootLeaf>,
}

/// Prepares `l`'s leaf with its proof and the statement the orchestrator expects of it.
fn root_leaf(
    l: &RootLeaf,
) -> Result<(wqc_sv_stark::leaf::Leaf, wqc_sv_stark::leaf::LeafProof), wqc_sv_stark::Error> {
    use base64::Engine as _;
    use wqc_sv_stark::leaf::{self, Dispatch, LeafProof};
    use wqc_sv_stark::Error;
    let level = wqc_sv_stark::SecurityLevel::parse(&l.security_level).ok_or_else(|| {
        Error::InvalidCircuit(format!("unknown security level {:?}", l.security_level))
    })?;
    let bytes = base64::engine::general_purpose::STANDARD
        .decode(&l.proof)
        .map_err(|e| Error::Verify(format!("leaf proof base64: {e}")))?;
    let proof = leaf::decode_proof(&bytes)?;
    let n = l.qubit_count as usize;
    let d = Dispatch {
        circuit_id: &l.circuit_id,
        sub_task_id: &l.sub_task_id,
        node_id: &l.node_id,
        slice_id: &l.slice_id,
    };
    if l.shots == 0 {
        let c = parse_circuit(&l.circuit)?;
        if !c.measures.is_empty() {
            return Err(Error::InvalidCircuit(
                "MEASURE in a circuit without shots".into(),
            ));
        }
        let statement = leaf::statement(d.context(), l.digest)?;
        return Ok((
            leaf::build(level, n, c.gates)?,
            LeafProof { proof, statement },
        ));
    }
    let c = parse_leaf(&l.circuit, n)?;
    let shots =
        u32::try_from(l.shots).map_err(|_| Error::InvalidCircuit(format!("{} shots", l.shots)))?;
    let sampling = Sampling {
        measures: c.measures,
        cbits: l.classical_bit_count as usize,
        shots,
    };
    let counts = parse_counts(&l.counts, &sampling)?;
    let statement =
        leaf::expected_sampling_statement(&sampling, &d, l.digest, l.sample_seed, &counts)?;
    let built = leaf::build_sampling(level, c.qubits, c.gates, sampling)?;
    Ok((built, LeafProof { proof, statement }))
}

/// An upper estimate, in bytes, of the memory `wqc_sv_verify_root` peaks at per leaf of `rows`
/// gate rows on `qubit_count` qubits with `shots`: it prepares each leaf with its proving data
/// (about 1 KB per gate row) and a recursion layer over it (about 180 MB). Out-of-range
/// arguments saturate to `u64::MAX`.
#[no_mangle]
pub extern "C" fn wqc_sv_root_peak_bytes(qubit_count: u32, rows: u64, shots: u64) -> u64 {
    wqc_sv_stark::root::verify_peak_bytes(qubit_count as usize, rows as usize, shots)
}

/// Verifies a task's v2 root (`root::encode_root` bytes, from the composer) over its leaves.
/// `leaves_json` is `{"leaves":[...]}`, in the order the composer was given them, each with
/// the circuit, the dispatch, the digest, seed and canonical counts the orchestrator accepted,
/// and the leaf proof (base64): the root verifies against the statements built from those
/// fields, never against a prover's claim.
///
/// This prepares every leaf with its proving data and a layer over it; see
/// [`wqc_sv_root_peak_bytes`] for the memory.
///
/// Returns `1` = valid, `0` = invalid root or arguments, `-99` = panic.
///
/// # Safety
///
/// `leaves_json` must be null-terminated; `root_bytes` must point to `root_len` bytes.
#[no_mangle]
pub unsafe extern "C" fn wqc_sv_verify_root(
    leaves_json: *const c_char,
    root_bytes: *const u8,
    root_len: u32,
) -> i32 {
    let result = catch_unwind(AssertUnwindSafe(|| {
        let Some(json) = cstr(leaves_json) else {
            eprintln!("[Rust FFI] sv_verify_root: null or non-UTF-8 leaves");
            return 0;
        };
        if root_bytes.is_null() {
            eprintln!("[Rust FFI] sv_verify_root: null root");
            return 0;
        }
        let root = slice::from_raw_parts(root_bytes, root_len as usize);
        let checked = serde_json::from_str::<RootInput>(json)
            .map_err(|e| wqc_sv_stark::Error::Verify(format!("leaves JSON: {e}")))
            .and_then(|input| {
                let leaves = input
                    .leaves
                    .iter()
                    .map(root_leaf)
                    .collect::<Result<Vec<_>, _>>()?;
                let refs: Vec<_> = leaves.iter().map(|(l, p)| (l, p)).collect();
                wqc_sv_stark::root::verify_root(&refs, &wqc_sv_stark::root::decode_root(root)?)
            });
        match checked {
            Ok(()) => 1,
            Err(err) => {
                eprintln!("[Rust FFI] sv_verify_root: {err}");
                0
            }
        }
    }));
    unwind_to_ffi_code(result)
}

#[cfg(test)]
mod sv_tests {
    use super::*;
    use std::ffi::CString;
    use wqc_sv_stark::digest::terminal_digest;
    use wqc_sv_stark::exec::execute;
    use wqc_sv_stark::leaf::{encode_proof, Dispatch};
    use wqc_sv_stark::wire::counts_json;

    const BELL: &str = r#"[{"type":"H","params":0},{"type":"CNOT","params":[0,1]},
        {"type":"RY","params":[1,0.7]}]"#;
    const BELL_MEASURED: &str = r#"[{"type":"H","params":0},{"type":"CNOT","params":[0,1]},
        {"type":"RY","params":[1,0.7]},{"type":"MEASURE","params":{"qubit":0,"cbit":0}},
        {"type":"MEASURE","params":{"qubit":1,"cbit":1}}]"#;
    const IDS: [&str; 4] = ["circuit", "sub", "node", "0"];

    fn c(s: &str) -> CString {
        CString::new(s).unwrap()
    }

    fn digest() -> [u64; 4] {
        let gates = parse_circuit(BELL).unwrap().gates;
        terminal_digest(&execute(2, &gates).1)
    }

    fn dispatch() -> Dispatch<'static> {
        Dispatch {
            circuit_id: IDS[0],
            sub_task_id: IDS[1],
            node_id: IDS[2],
            slice_id: IDS[3],
        }
    }

    unsafe fn verify(leaf: *const WqcSvLeaf, node: &str, digest: [u64; 4], proof: &[u8]) -> i32 {
        let ids = [IDS[0], IDS[1], node, IDS[3]].map(c);
        wqc_sv_verify_leaf(
            leaf,
            ids[0].as_ptr(),
            ids[1].as_ptr(),
            ids[2].as_ptr(),
            ids[3].as_ptr(),
            digest.as_ptr(),
            proof.as_ptr(),
            proof.len() as u32,
        )
    }

    unsafe fn verify_sampling(
        leaf: *const WqcSvLeaf,
        seed: u64,
        counts: &str,
        proof: &[u8],
    ) -> i32 {
        let ids = IDS.map(c);
        let counts = c(counts);
        wqc_sv_verify_sampling_leaf(
            leaf,
            ids[0].as_ptr(),
            ids[1].as_ptr(),
            ids[2].as_ptr(),
            ids[3].as_ptr(),
            digest().as_ptr(),
            seed,
            counts.as_ptr(),
            proof.as_ptr(),
            proof.len() as u32,
        )
    }

    #[test]
    fn sv_leaf_rows_reads_core_json() {
        unsafe {
            // H and RY round (the CNOT flushes H first): two steps of 2^(n−1) rows.
            assert_eq!(wqc_sv_leaf_rows(2, c(BELL).as_ptr()), 4);
            assert_eq!(wqc_sv_leaf_rows(16, c(BELL).as_ptr()), 2 << 15);
            assert_eq!(wqc_sv_leaf_rows(2, c(BELL_MEASURED).as_ptr()), 4);
            assert_eq!(wqc_sv_leaf_rows(1, c(BELL).as_ptr()), -1);
            assert_eq!(wqc_sv_leaf_rows(17, c("[]").as_ptr()), -1);
            assert_eq!(wqc_sv_leaf_rows(2, c("not json").as_ptr()), -1);
            assert_eq!(wqc_sv_leaf_rows(2, std::ptr::null()), -1);
            let far = r#"[{"type":"MEASURE","params":{"qubit":9,"cbit":0}}]"#;
            assert_eq!(wqc_sv_leaf_rows(2, c(far).as_ptr()), -1);
            // Mid-circuit: the IF becomes a controlled X (no rows) and the RESET of a used
            // qubit an ancilla, so the H and RY count on three qubits.
            let mid = r#"[{"type":"H","params":0},{"type":"MEASURE","params":{"qubit":0,"cbit":0}},
                {"type":"IF","params":{"cbit":0,"value":1,"gate":{"type":"X","params":1}}},
                {"type":"RESET","params":0},{"type":"RY","params":[0,0.4]},
                {"type":"MEASURE","params":{"qubit":0,"cbit":1}}]"#;
            assert_eq!(wqc_sv_leaf_rows(2, c(mid).as_ptr()), 2 << 2);
            let after =
                r#"[{"type":"MEASURE","params":{"qubit":0,"cbit":0}},{"type":"H","params":0}]"#;
            assert_eq!(wqc_sv_leaf_rows(2, c(after).as_ptr()), -1);
            // 16 qubits are the limit; a RESET that takes an ancilla makes 17.
            let full = r#"[{"type":"H","params":0},{"type":"RESET","params":0},
                {"type":"H","params":0},{"type":"MEASURE","params":{"qubit":0,"cbit":0}}]"#;
            assert_eq!(wqc_sv_leaf_rows(15, c(full).as_ptr()), 2 << 15);
            assert_eq!(wqc_sv_leaf_rows(16, c(full).as_ptr()), -1);
        }
        assert_eq!(wqc_sv_max_rows(), 1 << 22);
        // Above the measured peaks: 1.45 GB at 2^22 rows on 16 qubits, 0.75 GB at 2^21 with
        // 2^16 shots, 3.2 MB at n = 8.
        assert!(wqc_sv_verifier_peak_bytes(16, 1 << 22, 0) > 1_454 << 20);
        assert!(wqc_sv_verifier_peak_bytes(16, 1 << 21, 1 << 16) > 748 << 20);
        assert!(wqc_sv_verifier_peak_bytes(8, 2048, 0) > 4 << 20);
        assert!(wqc_sv_verifier_peak_bytes(16, 1 << 22, 0) < 2 << 30);
        // Out-of-range arguments saturate instead of wrapping to a small estimate.
        assert_eq!(wqc_sv_verifier_peak_bytes(64, 0, 0), u64::MAX);
        assert_eq!(wqc_sv_verifier_peak_bytes(0, u64::MAX, 0), u64::MAX);
        assert_eq!(wqc_sv_verifier_peak_bytes(0, 0, u64::MAX), u64::MAX);
    }

    #[test]
    fn sv_leaf_new_rejects_what_has_no_leaf() {
        let low = c("low");
        unsafe {
            for (json, cbits, shots, level) in [
                (BELL_MEASURED, 0, 0, "low"),
                (BELL, 2, 0, "nope"),
                (BELL_MEASURED, 2, 1 << 17, "low"),
                (BELL_MEASURED, 0, 16, "low"),
                // core rejects sample_counts without a MEASURE; so does the verifier.
                (BELL, 2, 16, "low"),
                (r#"[{"type":"RESET","params":0}]"#, 0, 0, "low"),
            ] {
                let leaf = wqc_sv_leaf_new(2, c(json).as_ptr(), cbits, shots, c(level).as_ptr());
                assert!(leaf.is_null(), "{json} {cbits} {shots} {level}");
            }
            assert!(wqc_sv_leaf_new(2, std::ptr::null(), 0, 0, low.as_ptr()).is_null());
            wqc_sv_leaf_free(std::ptr::null_mut());
        }
    }

    #[test]
    fn sv_verify_leaf_through_ffi() {
        let level = wqc_sv_stark::SecurityLevel::Low;
        let gates = parse_circuit(BELL).unwrap().gates;
        let leaf = wqc_sv_stark::leaf::build(level, 2, gates).unwrap();
        let proof = encode_proof(&leaf.prove(dispatch().context()).unwrap().proof);
        unsafe {
            let v = wqc_sv_leaf_new(2, c(BELL).as_ptr(), 0, 0, c("LOW").as_ptr());
            assert!(!v.is_null());
            assert_eq!(verify(v, IDS[2], digest(), &proof), 1);
            assert_eq!(verify(v, "other", digest(), &proof), 0);
            let mut wrong = digest();
            wrong[3] ^= 1;
            assert_eq!(verify(v, IDS[2], wrong, &proof), 0);
            assert_eq!(verify(v, IDS[2], digest(), &proof[1..]), 0);
            assert_eq!(
                verify_sampling(v, 1, r#"{"counts":{},"shots":0}"#, &proof),
                0
            );
            // A verifier at another tier rejects the proof.
            let ultra = wqc_sv_leaf_new(2, c(BELL).as_ptr(), 0, 0, c("").as_ptr());
            assert!(!ultra.is_null());
            assert_eq!(verify(ultra, IDS[2], digest(), &proof), 0);
            wqc_sv_leaf_free(ultra);
            wqc_sv_leaf_free(v);
        }
    }

    #[test]
    fn sv_verify_sampling_leaf_through_ffi() {
        let level = wqc_sv_stark::SecurityLevel::Low;
        let circuit = parse_circuit(BELL_MEASURED).unwrap();
        let sampling = Sampling {
            measures: circuit.measures,
            cbits: 2,
            shots: 64,
        };
        let leaf = wqc_sv_stark::leaf::build_sampling(level, 2, circuit.gates, sampling).unwrap();
        let seed = 0xDEAD_BEEF;
        let (p, counts) = leaf.prove_sampling(dispatch().context(), seed).unwrap();
        let proof = encode_proof(&p.proof);
        let json = counts_json(&counts, 2);
        unsafe {
            let v = wqc_sv_leaf_new(2, c(BELL_MEASURED).as_ptr(), 2, 64, c("low").as_ptr());
            assert!(!v.is_null());
            assert_eq!(verify_sampling(v, seed, &json, &proof), 1);
            assert_eq!(verify_sampling(v, seed + 1, &json, &proof), 0);
            let mut other = counts.clone();
            let k = other.iter().position(|&x| x > 0).unwrap();
            other[k] -= 1;
            other[(k + 1) % 4] += 1;
            assert_eq!(verify_sampling(v, seed, &counts_json(&other, 2), &proof), 0);
            // The same counts, not as the canonical bytes or not canonical as integers.
            let spaced = json.replacen(':', ": ", 1);
            assert_eq!(verify_sampling(v, seed, &spaced, &proof), 0);
            let p = 0xFFFF_FFFF_0000_0001u64;
            let shifted = format!("{{\"counts\":{{\"00\":{}}},\"shots\":64}}", 64 + p);
            assert_eq!(verify_sampling(v, seed, &shifted, &proof), 0);
            let zero = json.replacen("\"counts\":{", "\"counts\":{\"00\":0,", 1);
            assert_eq!(verify_sampling(v, seed, &zero, &proof), 0);
            let long_key = json.replacen("\"0", "\"00", 1);
            assert_eq!(verify_sampling(v, seed, &long_key, &proof), 0);
            assert_eq!(verify(v, IDS[2], digest(), &proof), 0);
            wqc_sv_leaf_free(v);
        }
    }

    #[test]
    fn sv_verify_root_through_ffi() {
        use base64::Engine as _;
        let level = wqc_sv_stark::SecurityLevel::Low;
        let circuit = parse_circuit(BELL_MEASURED).unwrap();
        let sampling = Sampling {
            measures: circuit.measures,
            cbits: 2,
            shots: 64,
        };
        let leaf = wqc_sv_stark::leaf::build_sampling(level, 2, circuit.gates, sampling).unwrap();
        let seed = 7;
        let (p, counts) = leaf.prove_sampling(dispatch().context(), seed).unwrap();
        let (root, _) = wqc_sv_stark::root::prove_root(&[(&leaf, &p)]).unwrap();
        let root = wqc_sv_stark::root::encode_root(&root);
        let input = |node: &str, seed: u64, counts: &str| {
            serde_json::json!({"leaves": [{
                "qubit_count": 2,
                "circuit": BELL_MEASURED,
                "classical_bit_count": 2,
                "shots": 64,
                "security_level": "low",
                "circuit_id": IDS[0],
                "sub_task_id": IDS[1],
                "node_id": node,
                "slice_id": IDS[3],
                "digest": digest(),
                "sample_seed": seed,
                "counts": counts,
                "proof": base64::engine::general_purpose::STANDARD.encode(encode_proof(&p.proof)),
            }]})
            .to_string()
        };
        let json = counts_json(&counts, 2);
        let verify = |leaves: String, root: &[u8]| unsafe {
            wqc_sv_verify_root(c(&leaves).as_ptr(), root.as_ptr(), root.len() as u32)
        };
        assert_eq!(verify(input(IDS[2], seed, &json), &root), 1);
        assert_eq!(verify(input("other", seed, &json), &root), 0);
        assert_eq!(verify(input(IDS[2], seed + 1, &json), &root), 0);
        let mut other = counts.clone();
        let k = other.iter().position(|&x| x > 0).unwrap();
        other[k] -= 1;
        other[(k + 1) % 4] += 1;
        assert_eq!(
            verify(input(IDS[2], seed, &counts_json(&other, 2)), &root),
            0
        );
        assert_eq!(verify(input(IDS[2], seed, &json), &root[1..]), 0);
        assert_eq!(verify(r#"{"leaves":[]}"#.into(), &root), 0);
        assert!(wqc_sv_root_peak_bytes(2, 1, 64) > 256 << 20);
    }
}

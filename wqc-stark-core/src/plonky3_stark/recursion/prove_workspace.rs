//! C10′: reclaim prove workspace between sequential nested uni-STARKs.
//!
//! Plonky3 `prove` takes the trace matrix by value (already freed after return),
//! but the structured `Proof` still holds FRI/LDE-related allocations until dropped.
//! PCS builders prove many outer STARKs back-to-back; encode to wire bytes then
//! drop the structured proof so the next prove does not accumulate those buffers.

use serde::Serialize;

/// Postcard-encode `proof`, then drop it so nested prove buffers can be reclaimed.
pub fn encode_stark_and_drop<T: Serialize>(proof: T, label: &str) -> Result<Vec<u8>, String> {
    let bytes =
        postcard::to_allocvec(&proof).map_err(|e| format!("postcard encode {label}: {e}"))?;
    drop(proof);
    Ok(bytes)
}

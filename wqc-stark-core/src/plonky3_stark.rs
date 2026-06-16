//! Phase 3: Plonky3 `p3-uni-stark` integration scaffold.
//!
//! Enable with `--features plonky3-stark` after upgrading Plonky3 to 0.5+.
//! See `docs/PHASE3_PLONKY3.md` for the migration checklist.

use crate::transcript::{StarkContext, V2_MARKER};

/// Generates a v2 Plonky3 uni-STARK proof (not yet implemented).
pub fn generate_plonky3_proof(
    _context: &StarkContext<'_>,
    _execution_trace: &[f64],
) -> Result<Vec<u8>, String> {
    Err(
        "Plonky3 uni-STARK prover not implemented yet (Phase 3). Use v1 AIR proofs.".to_string(),
    )
}

/// Verifies a v2 Plonky3 uni-STARK proof transcript.
pub fn verify_plonky3_proof(context: &StarkContext<'_>, proof: &[u8]) -> bool {
    if !proof.starts_with(context.sub_task_id.as_bytes()) {
        eprintln!("[STARK Core] Failed: sub_task_id prefix mismatch (v2)");
        return false;
    }

    let prefix_len = context.sub_task_id.len();
    if !proof[prefix_len..].starts_with(V2_MARKER) {
        eprintln!("[STARK Core] Failed: v2 marker missing");
        return false;
    }

    eprintln!("[STARK Core] Failed: v2 Plonky3 verifier not implemented yet (Phase 3)");
    false
}

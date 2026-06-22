# Proof Aggregation (v3 Compose)

Phase R1 of WP §3.3 recursive aggregation pipeline.

## Model

```
Ingest (per vote)     wqc_verify_stark_proof   ← already in orchestrator
        ↓
Quorum winner π_slice stored per slice
        ↓
compose (pairwise)    wqc_compose_stark_proofs ← this crate
        ↓
Root verify           wqc_verify_root_proof
```

Each leaf is verified **before** rewards at ingest. Compose re-verifies children as a safety check, then embeds them in a v3 transcript.

## v3 Compose Transcript

```
parent_task_id\0
_WQC_COMPOSE_V3_
compose_label\0
manifest_root_hash\0
left_child_sha3_256[32]
right_child_sha3_256[32]
left_len u32 LE + left_bytes
right_len u32 LE + right_bytes
```

- `compose_label`: `"L1:0"`, `"L2:1"`, or `"root"` for the task root.
- `manifest_root_hash`: bound at root node (matches compute manifest `root_hash`).

## FFI

| Function | Role |
|----------|------|
| `wqc_verify_stark_proof` | Leaf verify (existing) |
| `wqc_compose_stark_proofs` | Pair two child proofs → v3 transcript |
| `wqc_verify_root_proof` | Recursively verify entire tree |

### `wqc_compose_stark_proofs`

Pass **null** `left_circuit_id` / `right_circuit_id` when the child is already a v3 compose node (internal tree node).

Returns composed byte length on success, `0` on failure.

### `wqc_verify_root_proof`

Requires top-level `compose_label == "root"` and matching `manifest_root_hash`.

## Limitations (Phase R1)

This is a **structural** proof tree, not a true recursive Plonky3 STARK:

- Root verify walks the tree and re-runs leaf STARK verify on every leaf → **O(N)** crypto work inside one FFI call.
- WP §3.3 target (single STARK, O(log² N) verify) requires **Phase R2: AggregationAir** in `plonky3_stark/`.

The v3 format is forward-compatible: internal nodes can later be replaced by recursive STARK bytes with the same outer framing.

## Rust API

```rust
use wqc_stark_core::{compose_stark_proofs, verify_root_proof, ComposeContext, RootVerifyContext};

let root = compose_stark_proofs(&ComposeContext { ... }, &left, &right, Some(&left_ctx), Some(&right_ctx))?;
assert!(verify_root_proof(&RootVerifyContext { ... }, &root));
```

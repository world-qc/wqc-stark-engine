# Proof Aggregation (v3 Compose + R2 AggregationAir)

WP §3.3 recursive aggregation pipeline.

## Phases

| Phase | Status | Verify cost at root |
|-------|--------|---------------------|
| **R1** | Complete | O(N) leaf STARK re-verify (tree walk) |
| **R2** | Complete (devnet) | O(1) single `AggregationAir` STARK (fast path) |
| **R3** | Planned | In-circuit child STARK verify (true recursion) |

## Model

```
Ingest (per vote)     wqc_verify_stark_proof   ← orchestrator
        ↓
Quorum winner π_slice stored per slice
        ↓
compose (pairwise)    wqc_compose_stark_proofs
        ↓              ├─ v3 structural tree (audit)
        ↓              └─ R2 AggregationAir STARK tail (fast path)
Root verify           wqc_verify_root_proof
```

Each leaf is verified **before** rewards at ingest. Compose re-verifies children natively, then (R2) proves digest binding via `AggregationAir`.

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

## R2 Aggregation STARK (v4 tail)

Appended to each v3 compose node when built with `plonky3-stark`:

```
_WQC_AGG_TAIL_V4_
agg_len u32 LE + agg_transcript
```

Inner `agg_transcript`:

```
parent_task_id\0
_WQC_AGG_STARK_V4_
compose_label\0
manifest_root_hash\0
left_hash[32]
right_hash[32]
postcard_len u32 LE + postcard(p3_uni_stark::Proof)
```

### AggregationAir

Located in `wqc-stark-core/src/plonky3_stark/aggregation_air.rs`.

- Binds left/right child SHA3-256 digests in the trace.
- Constrains both child verification flags to `1` (children verified natively before prove).
- Uses the same Circle STARK config as leaf `QuantumExecutionAir`.

**R2 limitation:** Child STARK verification is performed **outside** the circuit at compose time. The aggregation STARK cryptographically attests digest binding + compose metadata. Root fast-path verify runs **one** STARK instead of walking all leaves.

**R3 target:** Replace native child verify with in-circuit STARK recursion for full WP §3.3 soundness on L2.

## FFI

| Function | Role |
|----------|------|
| `wqc_verify_stark_proof` | Leaf verify |
| `wqc_compose_stark_proofs` | Pair children → v3 + R2 agg tail |
| `wqc_verify_root_proof` | R2 fast path, else v3 audit walk |

## Root verify paths

1. **Fast (R2):** If root has `_WQC_AGG_TAIL_V4_`, verify single `AggregationAir` STARK bound to header digests + manifest.
2. **Audit (R1):** Recursively walk v3 tree and re-verify every leaf STARK.

## Build

```bash
cargo test -p wqc-stark-core --features plonky3-stark
cargo build --release -p wqc-stark-ffi
```

Rebuild `dist/libwqc_stark_verifier.so` and restart orchestrator after R2 changes.

## Rust API

```rust
use wqc_stark_core::{
    compose_stark_proofs, verify_root_proof, ComposeContext, RootVerifyContext,
};

#[cfg(feature = "plonky3-stark")]
use wqc_stark_core::plonky3_stark::{
    generate_aggregation_proof, verify_aggregation_proof, AggregationContext,
};
```

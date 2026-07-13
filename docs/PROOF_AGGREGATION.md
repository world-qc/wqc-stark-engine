# Proof Aggregation (v3 Compose + R2 AggregationAir)

WP §3.3 recursive aggregation pipeline, plus C2 **leaf compose** labels that wrap unitary + distribution/trajectory children.

## Phases

| Phase | Status | Verify cost at root |
|-------|--------|---------------------|
| **R1** | Complete | O(N) leaf STARK re-verify (tree walk) |
| **R2** | Complete (devnet) | O(1) single `AggregationAir` STARK (fast path) |
| **R3** | Planned | In-circuit child STARK verify (true recursion) |

## Model

```
Ingest (per vote)     wqc_verify_stark_proof   ← orchestrator
        ↓               (routes leaf:unitary_born / leaf:unitary_traj)
Quorum winner π_slice stored per slice
        ↓
compose (pairwise)    wqc_compose_stark_proofs
        ↓              ├─ v3 structural tree (audit)
        ↓              └─ R2 AggregationAir STARK tail (fast path)
Root verify           wqc_verify_root_proof
```

Each leaf is verified **before** rewards at ingest. Compose re-verifies children natively, then (R2) proves digest binding via `AggregationAir`.

C2 leaf proofs may themselves be **v3 compose nodes** (`leaf:unitary_born` / `leaf:unitary_traj`) before they enter the slice tree; see [DISTRIBUTION_STARK.md](./DISTRIBUTION_STARK.md).

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

### Compose labels

| Label | Meaning |
|-------|---------|
| *(task / slice tree)* | Binary aggregation of verified slice winners (orchestrator R2) |
| `leaf:unitary_born` | Unitary Plonky3 child + Born distribution child (terminal C2) |
| `leaf:unitary_traj` | Unitary Plonky3 child + trajectory child (mid-circuit C2) |

Constants: `UNITARY_BORN_COMPOSE_LABEL`, `UNITARY_TRAJ_COMPOSE_LABEL` in `wqc-stark-core`.

Right-child markers:

- Born leaf: `_M31_BORN_LEAF_V1_`
- Trajectory leaf: `_M31_TRAJ_LEAF_V1_`

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
| `wqc_verify_stark_proof` | Leaf verify (incl. C2 compose leaves) |
| `wqc_compose_stark_proofs` | Pair children → v3 + R2 agg tail |
| `wqc_verify_root_proof` | R2 fast path, else v3 audit walk |
| `wqc_is_unitary_born_compose` | Detect `leaf:unitary_born` |
| `wqc_is_unitary_trajectory_compose` | Detect `leaf:unitary_traj` |

Distribution / trajectory binding and scheme probes: see [DISTRIBUTION_STARK.md](./DISTRIBUTION_STARK.md).

## Root verify paths

1. **Fast (R2):** If root has `_WQC_AGG_TAIL_V4_`, verify single `AggregationAir` STARK bound to header digests + manifest.
2. **Audit (R1):** Recursively walk v3 tree and re-verify every leaf STARK.

## Build

```bash
cargo test -p wqc-stark-core --features plonky3-stark
cargo build --release -p wqc-stark-ffi
```

Rebuild `dist/libwqc_stark_verifier.so` and restart orchestrator after R2 / C2 compose changes.

## Rust API

```rust
use wqc_stark_core::{
    compose_stark_proofs, verify_root_proof, ComposeContext, RootVerifyContext,
};

#[cfg(feature = "plonky3-stark")]
use wqc_stark_core::{
    compose_unitary_born_leaf, compose_unitary_trajectory_leaf,
    verify_unitary_born_leaf_compose, verify_unitary_trajectory_leaf_compose,
};
#[cfg(feature = "plonky3-stark")]
use wqc_stark_core::plonky3_stark::{
    generate_aggregation_proof, verify_aggregation_proof, AggregationContext,
};
```

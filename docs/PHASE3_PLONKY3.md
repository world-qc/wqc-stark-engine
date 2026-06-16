# Phase 3: Plonky3 uni-STARK migration

Phase 1 delivers an **AIR commitment** proof (embedded trace + recomputed constraint sum).
Phase 3 adds a **real STARK** using Polygon Plonky3 `p3-uni-stark` (Mersenne31 + Circle PCS).

## Status: Complete (devnet)

| Item | Location |
|------|----------|
| Plonky3 0.6.1 deps | `wqc-stark-core/Cargo.toml` (`plonky3-stark` feature) |
| Shared numeric constraints | `wqc-stark-core/src/air/constraints.rs` |
| `p3_air::Air` implementation | `wqc-stark-core/src/plonky3_stark/quantum_air.rs` |
| Circle `StarkConfig` | `wqc-stark-core/src/plonky3_stark/config.rs` |
| v2 prove / verify | `wqc-stark-core/src/plonky3_stark/mod.rs` |
| v1 + v2 verifier dispatch | `wqc-stark-core/src/lib.rs` |
| FFI (v2 enabled) | `wqc-stark-ffi` with `features = ["plonky3-stark"]` |

## Proof format (v2)

```text
<sub_task_id><_M31_PLONKY3_STARK_V2_><circuit_id\0><node_id\0><slice_id\0><output_hash\0>
<postcard_len: u32 LE><postcard(p3_uni_stark::Proof)>
```

v1 proofs (`_M31_QUANTUM_AIR_V1_`) remain valid. The verifier auto-detects the marker.

## API

```rust
// v1 (default, no extra features)
let proof = generate_stark_proof(&ctx, &trace);

// v2 (requires `plonky3-stark` feature)
let proof = generate_plonky3_stark_proof(&ctx, &trace)?;

// Both formats
verify_stark_proof_core(&ctx, &proof);
```

## Build

```bash
# v1 only
cargo test -p wqc-stark-core

# v1 + v2 Plonky3 STARK
cargo test -p wqc-stark-core --features plonky3-stark

# FFI shared library (orchestrator CGO)
cargo build --release -p wqc-stark-ffi
```

Docker builder image enables `plonky3-stark` by default (`Dockerfile`).

## Trace padding

Circle PCS requires at least 4 trace rows. The prover pads to `max(4, next_power_of_two(height))`
by repeating the last row (`pad_air_matrix_for_uni_stark`). Padding rows must remain AIR-satisfied
(idle terminal row or steady-state repetition).

## Rollout (remaining ops work)

| Step | Action |
|------|--------|
| 1 | ~~Land `Air` + `StarkConfig` behind `plonky3-stark`~~ Done |
| 2 | ~~Dual-prove golden traces in CI~~ Done (`v1_and_v2_dual_prove_on_golden_traces`) |
| 3 | Node prover emits v2; orchestrator accepts v1 + v2 during transition |
| 4 | Remove v1 after quorum on v2 |

## Open design items

- **Blowup / query count**: tune `devnet_circle_config` for ~28-qubit slice traces.
- **Public inputs**: bound fields are transcript-checked; optional PCS public-value binding TBD.
- **RX/RY/RZ**: separate rotation AIR columns vs shared `sel_rot` (trace-spec follow-up).

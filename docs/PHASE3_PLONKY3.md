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

Distribution / Born / trajectory Plonky3 AIRs built on the same feature flag are documented in [DISTRIBUTION_STARK.md](./DISTRIBUTION_STARK.md).

## Proof format (v2)

```text
<sub_task_id><_M31_PLONKY3_STARK_V2_>
<circuit_id\0><node_id\0><slice_id\0><output_hash\0>
[optional terminal_statevector_digest\0]    # 64-char ASCII hex
[optional MSH1||measurement_spec_hash\0]  # C2c measurement-spec PI
<postcard_len: u32 LE><postcard(p3_uni_stark::Proof)>
```

`MSH1` is `MEASUREMENT_SPEC_HASH_PI_PREFIX` and disambiguates the second optional field from a raw hex digest.

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

`StarkContext` fields used for binding: `circuit_id`, `sub_task_id`, `node_id`, `slice_id`, `output_hash`, plus optional `terminal_statevector_digest` and `measurement_spec_hash`.

## Build

```bash
# v1 only
cargo test -p wqc-stark-core

# v1 + v2 Plonky3 STARK (+ C2 Plonky3 paths)
cargo test -p wqc-stark-core --features plonky3-stark

# FFI shared library (orchestrator CGO)
cargo build --release -p wqc-stark-ffi
```

Docker builder image enables `plonky3-stark` by default (`Dockerfile`).

## Trace padding

Circle PCS requires at least 4 trace rows. The prover pads to `max(4, next_power_of_two(height))`
by repeating the last row (`pad_air_matrix_for_uni_stark`). Padding rows must remain AIR-satisfied
(idle terminal row or steady-state repetition).

## Rollout

| Step | Action | Status |
|------|--------|--------|
| 1 | Land `Air` + `StarkConfig` behind `plonky3-stark` | Done |
| 2 | Dual-prove golden traces in CI | Done (`v1_and_v2_dual_prove_on_golden_traces`) |
| 3 | Node / core prover emits v2; orchestrator accepts v1 + v2 | Done (devnet produces v2 / compose leaves) |
| 4 | Remove v1 after quorum on v2 | **Ops backlog** (not scheduled) |

## Open design / follow-ups

- **Blowup / query count**: tune `devnet_circle_config` for larger ~28-qubit slice traces.
- **RX/RY/RZ**: separate rotation AIR columns vs shared `sel_rot` (trace-spec follow-up).
- **R3**: in-circuit recursion over child STARKs ([PROOF_AGGREGATION.md](./PROOF_AGGREGATION.md)).

Transcript public-input binding for unitary link digests and `measurement_spec_hash` is **implemented** (see [DISTRIBUTION_STARK.md](./DISTRIBUTION_STARK.md)); PCS-native public-value columns remain optional future work.

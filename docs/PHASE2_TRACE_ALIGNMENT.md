# Phase 2: Trace alignment (complete)

Phase 2 locks the execution-trace contract between `wqc-core` and `wqc-stark-core`.

## Deliverables

| Item | Location |
|------|----------|
| 10 selector columns + CZ/CCNOT mapping | `wqc-stark-core/src/trace_spec.rs`, `air.rs` |
| Discrete `ctrl_active` / `ctrl_active_2` (`> 0.5` threshold) | `wqc-core/src/engine.rs` |
| Canonical trace spec (v2 multi-target) | `wqc-core/doc/trace-spec.md` |
| Pre/post rows per gate + `target_qubit` / `transition_link` | `wqc-core/src/engine.rs`, `wqc-stark-core/src/air/constraints.rs` |
| Executor trace unit tests (H, CNOT, CZ, CCNOT, H+CCNOT AIR) | `wqc-core/src/engine.rs` |
| Executor ↔ AIR integration tests | `wqc-core/src/engine.rs`, `proof.rs` |
| AIR / transcript / Plonky3 unit tests | `wqc-stark-core/src/air.rs`, `transcript.rs`, `lib.rs`, `plonky3_stark/` |

## Contract summary

- **Trace width**: 11 `f64` columns per row (`TRACE_WIDTH`).
- **Row pattern**: pre-gate + post-gate per active gate, then terminal boundary row.
- **AIR width**: 21 columns after selector expansion (`AIR_WIDTH`).
- **Multi-target**: `transition_link` gates cross-wire transitions; AIR skips amplitude continuity when `link = 0`.
- **Control columns**: discrete `0.0` or `1.0` before AIR ingestion.
- **Gate ids**: 1–12 per `trace-spec.md`; `0` for post-gate and terminal rows.
- **Proof format**: v1 embedded trace (`_M31_QUANTUM_AIR_V1_`); v2 Plonky3 uni-STARK optional.

## Verification

```bash
# wqc-stark-engine
cargo test -p wqc-stark-core --features plonky3-stark

# wqc-core (requires wqc-stark-engine dependency)
cargo test
```

Key integration cases:

- `executor_traces_satisfy_stark_air_for_h_and_cnot` — includes `h_ccnot_devnet` (`H(0)` → `CCNOT(0,1,2)`)
- `v1_and_v2_dual_prove_on_golden_traces` — v1 digest + Plonky3 uni-STARK on 11-column traces

End-to-end devnet validation: circuits at `qubit_count = WQC_MAX_QUBITS` (no slice pruning) with mixed target wires should verify with `air_sum == 0`.

## Multi-target AIR (resolved)

Prior limitation: consecutive rows sampled different target qubits, so amplitude columns were incomparable.

**Fix (trace-schema v2)**:

1. Two rows per gate on a fixed target wire (pre with active `gate_id`, post with `gate_id = 0`).
2. Column 9 (`target_qubit`) records the sampled wire.
3. Column 10 (`transition_link`) enables transition constraints only when the next row shares the same target.

Old 10-column traces are **not** compatible with the new AIR.

## Next: Phase 3

See [PHASE3_PLONKY3.md](./PHASE3_PLONKY3.md) for Plonky3 uni-STARK migration and aggregation.

# Phase 2: Trace alignment (complete)

Phase 2 locks the execution-trace contract between `wqc-core` and `wqc-stark-core`.

## Deliverables

| Item | Location |
|------|----------|
| 10 selector columns + CZ/CCNOT mapping | `wqc-stark-core/src/trace_spec.rs`, `air.rs` |
| Discrete `ctrl_active` / `ctrl_active_2` (`> 0.5` threshold) | `wqc-core/src/engine.rs` |
| Canonical trace spec (v1) | `wqc-core/doc/trace-spec.md` |
| Executor trace unit tests (H, CNOT, CZ, CCNOT) | `wqc-core/src/engine.rs` |
| Executor ↔ AIR integration tests | `wqc-core/src/engine.rs`, `proof.rs` |
| AIR / transcript unit tests | `wqc-stark-core/src/air.rs`, `transcript.rs`, `lib.rs` |

## Contract summary

- **Trace width**: 10 `f64` columns per row (`TRACE_WIDTH`).
- **AIR width**: 19 columns after selector expansion (`AIR_WIDTH`).
- **Control columns**: discrete `0.0` or `1.0` before AIR ingestion.
- **Gate ids**: 1–12 per `trace-spec.md`; `0` for terminal boundary rows.
- **Proof format**: v1 embedded trace (`_M31_QUANTUM_AIR_V1_`).

## Verification

```bash
# wqc-stark-engine
cargo test

# wqc-core (requires wqc-stark-engine dependency)
cargo test
```

End-to-end devnet validation: 28-qubit parent task sliced to 26-qubit nodes with v1 AIR
verification on the orchestrator (`Verification success (v1 AIR, trace_len=...)`).

## Known limitation

AIR transition rows compare amplitude columns on consecutive trace rows. Because each row
samples the **current gate's target qubit**, multi-target gate sequences (e.g. `X(0)` then
`CNOT(0,1)`) may produce a non-zero `air_sum` even when the simulator is correct. Phase 3
trace-schema work will address this; current devnet circuits are chosen to stay within the
supported subset.

## Next: Phase 3

See [PHASE3_PLONKY3.md](./PHASE3_PLONKY3.md) for Plonky3 uni-STARK migration.

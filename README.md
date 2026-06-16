# wqc-stark-engine

Cryptographic proof engine for the WQC decentralized quantum compute mesh. Provides Mersenne31 **AIR commitment** proofs (Phase 1) with a Plonky3 uni-STARK migration path (Phase 3).

## Architecture

```text
wqc-stark-engine/
├── wqc-stark-core/     # AIR prover/verifier (Rust lib)
├── wqc-stark-ffi/      # CGO-compatible `libwqc_stark_verifier`
└── docs/PHASE3_PLONKY3.md
```

* **`wqc-stark-core`**: Quantum execution AIR over Plonky3 Mersenne31 field types. Phase 1 embeds the execution trace and recomputes constraints at verify time. Phase 3 adds real FRI STARKs behind `plonky3-stark`.
* **`wqc-stark-ffi`**: Panic-safe C ABI for the Go orchestrator.

## Public inputs (`StarkContext`)

| Field | Role |
|-------|------|
| `circuit_id` | Hash of the pruned tensor sub-graph |
| `sub_task_id` | Unique sub-task identifier |
| `node_id` | Executing node |
| `slice_id` | Binary slice path in the TN tree |
| `output_hash` | SHA3-256 of the JSON `ComplexResult` |

## Proof transcript (v1)

```text
<sub_task_id><_M31_QUANTUM_AIR_V1_><circuit_id\0><node_id\0><slice_id\0><output_hash\0>
<trace_rows: u32 LE><trace f64 LE><air_sum: u32 LE><boundary v0_re,v0_im,v1_re,v1_im: u32 LE each>
```

The verifier:

1. Checks public-input binding
2. Re-expands the embedded trace to AIR
3. Recomputes `air_sum` (must be `0`)
4. Checks boundary amplitudes match the terminal row

Legacy `_M31_QUANTUM_AIR_STARK_` proofs (no embedded trace) are **rejected**.

Trace column semantics: see `wqc-core/doc/trace-spec.md`.

## Build

```bash
cargo build --release
cargo test
```

### Docker

```bash
docker build -t wqc-stark-builder .
docker run --rm -v "$(pwd)/dist:/output" wqc-stark-builder \
    cp target/release/libwqc_stark_verifier.a \
       target/release/libwqc_stark_verifier.so \
       /output/
```

## Phase roadmap

| Phase | Status |
|-------|--------|
| 1 | AIR bugfixes, embedded trace, verifier re-eval |
| 2 | Trace-spec alignment (`ctrl` discretization, 10 selectors) |
| 3 | Plonky3 `p3-uni-stark` (feature `plonky3-stark`) |

## License

GPLv3 — see `LICENSE`.

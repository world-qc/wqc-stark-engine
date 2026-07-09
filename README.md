# wqc-stark-engine

Cryptographic proof engine for the WQC decentralized quantum compute mesh. Provides Mersenne31 **AIR commitment** proofs (Phase 1) with a Plonky3 uni-STARK migration path (Phase 3).

## Architecture

```text
wqc-stark-engine/
├── wqc-stark-core/     # AIR prover/verifier (Rust lib)
├── wqc-stark-ffi/      # CGO-compatible `libwqc_stark_verifier`
├── docs/PHASE2_TRACE_ALIGNMENT.md
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

## Proof transcript (v2, Phase 3)

```text
<sub_task_id><_M31_PLONKY3_STARK_V2_><public inputs\0...><postcard_len: u32 LE><p3 proof bytes>
```

Real FRI STARK via Plonky3 Circle PCS (Mersenne31). See `docs/PHASE3_PLONKY3.md`.

The verifier (v1):

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
cargo test -p wqc-stark-core --features plonky3-stark
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
| 1 | Complete — AIR bugfixes, embedded trace, verifier re-eval |
| 2 | Complete — trace-spec alignment, executor tests, cross-crate AIR checks |
| 3 | Complete — Plonky3 `p3-uni-stark` (`plonky3-stark` feature, v2 transcript) |
| R1 | Complete — v3 proof tree compose + FFI |
| R2 | Complete (devnet) — `AggregationAir` STARK tail, O(1) root fast verify |

See `docs/PROOF_AGGREGATION.md`.

## Contributing

Contributions are welcome. See [CONTRIBUTING.md](CONTRIBUTING.md) for development setup, coding guidelines, and the pull request process.

## License

GPLv3 — see `LICENSE`.

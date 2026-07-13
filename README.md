# wqc-stark-engine

Cryptographic proof engine for the WQC decentralized quantum compute mesh. Provides Mersenne31 **AIR commitment** proofs and Plonky3 uni-STARKs with recursive compose, distribution binding, and trajectory binding for `sample_counts`.

See the [STARK proof specification](https://github.com/world-qc/wqc-docs/tree/main/spec/stark) for the full protocol definition (transcript format, AIR constraints, distribution binding, proof aggregation).

## Architecture

```text
wqc-stark-engine/
├── wqc-stark-core/     # AIR prover/verifier (Rust lib)
└── wqc-stark-ffi/      # CGO-compatible `libwqc_stark_verifier`
```

* **`wqc-stark-core`**: Quantum execution AIR over Plonky3 Mersenne31 field types. Supports embedded trace verification, FRI STARKs via Plonky3 Circle PCS, distribution / trajectory segments, Born and shot-sampling AIRs, and leaf compose proofs.
* **`wqc-stark-ffi`**: Panic-safe C ABI for the Go orchestrator (leaf verify, compose, root verify, distribution/trajectory binding, scheme detection).

## Public inputs (`StarkContext`)

| Field | Role |
|-------|------|
| `circuit_id` | Hash of the pruned circuit sub-graph |
| `sub_task_id` | Unique sub-task identifier |
| `node_id` | Executing node |
| `slice_id` | Binary slice path in the tensor network tree |
| `output_hash` | SHA3-256 of the result payload (scalar `ComplexResult` **or** canonical `sample_counts` JSON) |
| `terminal_statevector_digest` | Optional; SHA3-256 hex linking unitary leaf ↔ Born / trajectory distribution (empty when unbound) |
| `measurement_spec_hash` | Optional; SHA3-256 hex of canonical measurement spec JSON bound in the proof transcript (empty when unbound) |

## Proof transcript (v1)

```text
<sub_task_id><_M31_QUANTUM_AIR_V1_><circuit_id\0><node_id\0><slice_id\0><output_hash\0>
<trace_rows: u32 LE><trace f64 LE><air_sum: u32 LE><boundary v0_re,v0_im,v1_re,v1_im: u32 LE each>
```

Optional binding fields (`terminal_statevector_digest`, `MSH1`+`measurement_spec_hash`) follow the same rules as v2 when non-empty.

## Proof transcript (v2)

```text
<sub_task_id><_M31_PLONKY3_STARK_V2_>
<circuit_id\0><node_id\0><slice_id\0><output_hash\0>
[optional terminal_statevector_digest\0]   # 64-char hex
[optional MSH1||measurement_spec_hash\0] # prefix + 64-char hex
<postcard_len: u32 LE><p3 proof bytes>
```

Real FRI STARK via Plonky3 Circle PCS (Mersenne31).

Auxiliary distribution, Born zk, trajectory, and trajectory zk segments may follow the unitary proof body.

The verifier (v1):

1. Checks public-input binding
2. Re-expands the embedded trace to AIR
3. Recomputes `air_sum` (must be `0`)
4. Checks boundary amplitudes match the terminal row

v2 verifies the Plonky3 proof, then any attached distribution / trajectory / compose paths.

Legacy `_M31_QUANTUM_AIR_STARK_` proofs (no embedded trace) are **rejected**.

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

## Planned

- **In-circuit child STARK verification (true recursion):** currently child proofs are verified natively outside the circuit at compose time; the aggregation STARK attests digest binding only. Full in-circuit recursion over child STARKs is planned.

## Contributing

Contributions are welcome. See [CONTRIBUTING.md](CONTRIBUTING.md) for development setup, coding guidelines, and the pull request process.

## License

GPLv3 — see `LICENSE`.

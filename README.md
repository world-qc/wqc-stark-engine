# wqc-stark-engine

[![License: GPL v3](https://img.shields.io/badge/License-GPLv3-blue.svg)](https://www.gnu.org/licenses/gpl-3.0)
[![Status: Beta](https://img.shields.io/badge/Status-Beta-orange.svg)]()
[![CI](https://github.com/world-qc/wqc-stark-engine/actions/workflows/ci.yml/badge.svg)](https://github.com/world-qc/wqc-stark-engine/actions/workflows/ci.yml)

Cryptographic proof engine for the WQC decentralized quantum compute mesh. Provides Mersenne31 **AIR commitment** proofs and Plonky3 uni-STARKs with recursive compose, distribution binding, and trajectory binding for `sample_counts`.

See the [STARK proof specification](https://github.com/world-qc/wqc-docs/blob/main/spec/zk-STARK.md) for the full protocol definition (transcript format, AIR constraints, distribution binding, proof aggregation).

## Architecture

```text
wqc-stark-engine/
├── wqc-stark-core/     # AIR prover/verifier (Rust lib)
└── wqc-stark-ffi/      # CGO-compatible `libwqc_stark_verifier`
```

* **`wqc-stark-core`**: Quantum execution AIR over Plonky3 Mersenne31 field types. Supports embedded trace verification, FRI STARKs via Plonky3 Circle PCS, distribution / trajectory segments, Born and shot-sampling AIRs, leaf compose proofs, and **R3 in-circuit recursion** (RecAgg V6, agg/leaf PCS certificates, in-circuit OOD / FriFold / DeepRo / Keccak Mmcs; Born K≤21, W≤68).
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

## Proof transcripts

| Version | Marker | Role |
|---------|--------|------|
| v1 | `_M31_QUANTUM_AIR_V1_` | Legacy embedded-trace AIR (unitary only); **rejected** by current verifiers |
| v2 | `_M31_PLONKY3_STARK_V2_` | Plonky3 Circle PCS uni-STARK (unitary); still the primary leaf proof |
| v3 | `_WQC_COMPOSE_V3_` | Proof-tree compose — binds two child proofs by SHA3-256 hash (leaf or agg pairs) |
| v4 | `_WQC_AGG_STARK_V4_` / `_WQC_AGG_TAIL_V4_` | AggregationAir Plonky3 STARK (R2); parent of two child digests |
| v5 | `_WQC_REC_AGG_V5_` / `_WQC_REC_TAIL_V5_` | Recursive aggregation (R3-M1); wraps AggregationAir proof + child metadata |
| v6 | `_WQC_REC_AGG_V6_` / `_WQC_REC_TAIL_V6_` | Recursive aggregation (R3-M2–M3e); agg/leaf PCS certificates with in-circuit OOD, FriFold, DeepRo, FRI Val/Challenge Mmcs STARKs |

**Layout** — v2/v4 carry a postcard-encoded Plonky3 proof after C-string public inputs. v3/v5/v6 embed compose headers (`parent_task_id`, `compose_label`, child hashes/digests/kinds) followed by the child proof bytes.

**Auxiliary segments** — Distribution (`_M31_DIST_V1_` / `_M31_DIST_V2_`), Born-zk (`_M31_BORN_STARK_V1_` / `_M31_BORN_LEAF_V1_`), trajectory (`_M31_TRAJ_V1_` / `_M31_TRAJ_V2_`), and trajectory-zk (`_M31_TRAJ_MARG_STARK_INNER_V1_` / `_M31_TRAJ_STARK_V1_` / `_M31_TRAJ_LEAF_V1_`) segments may follow or precede the unitary proof body.

All transcript details (field layout, verification steps, binding rules) are defined in the [STARK proof specification](https://github.com/world-qc/wqc-docs/blob/main/spec/zk-STARK.md).

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

## In-circuit recursion (R3)

**M3e landed** (`plonky3-stark` feature): leaf and agg PCS bundles through RecAgg V6 + compose; verify-time in-circuit OOD (agg + all leaf AIR kinds), FriFold, DeepRo, Val/Challenge Mmcs; Born trace width capped at W≤68 (K≤21). Protocol (soundness ladder, V6 side flags, residuals): [zk-STARK.md §8](https://github.com/world-qc/wqc-docs/blob/main/spec/zk-STARK.md).

| Path under `wqc-stark-core/.../recursion/` | Role |
|--------------------------------------------|------|
| `ood_air.rs` | `OodCheckAir` STARK: ζ quotient + agg in-circuit fold |
| `ood_native.rs` | Prove-time OOD witness extraction (FS replay) |
| `ood_bind.rs` | Bind OOD step to child openings at verify |
| `ood_leaf_fold.rs` | In-circuit leaf constraint fold (Unitary / Distribution / Shot) |
| `ood_fold.rs` | Native fold for prove-time witness sanity checks |
| `leaf_pcs_cert.rs` | Leaf cert prove/verify + born/traj bundle decode |
| `transcript_v6.rs` | V6 encode / decode (agg cert OR leaf bundle) |
| `prove.rs` | RecAgg matrix bind for leaf bundles |
| `air.rs` | kind=leaf no longer zeroes PCS columns |
| `../aggregation/mod.rs` | `pcs_for_child` → compose / verify context |

## Roadmap

- Prove-time witness oracles in-circuit (verify-time OOD is done; proving still extracts OOD / DeepRo / FriFold witnesses via native Plonky3)
- Multi-chunk quotient leaf DeepRo STARKs (deferred today)
- Full-stack multislice RecAgg V6 compose on docs/devnet (orch CGO unit E2E: `TestRecAggV6ComposeE2E`)

## Contributing

Contributions are welcome. See [CONTRIBUTING.md](CONTRIBUTING.md) for development setup, coding guidelines, and the pull request process.

## License

Distributed under the GNU General Public License v3.0 (GPLv3). See `LICENSE` for more information.

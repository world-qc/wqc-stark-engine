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

* **`wqc-stark-core`**: Quantum execution AIR over Plonky3 Mersenne31 field types. Supports embedded trace verification, FRI STARKs via Plonky3 Circle PCS, distribution / trajectory segments, Born and shot-sampling AIRs, leaf compose proofs, and in-circuit recursive aggregation (`RecursiveAggregationAir` v6 with agg/leaf PCS certificates, in-circuit OOD / FriFold / DeepRo / Keccak Mmcs; Born K≤21, W≤68).
* **`wqc-stark-ffi`**: Panic-safe C ABI for the Go orchestrator (leaf verify, compose with optional prebuilt leaf PCS, root verify, `wqc_build_leaf_pcs_bundle`, distribution/trajectory binding, scheme detection).

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
| v4 | `_WQC_AGG_STARK_V4_` / `_WQC_AGG_TAIL_V4_` | AggregationAir digest attestation |
| v5 | `_WQC_REC_AGG_V5_` / `_WQC_REC_TAIL_V5_` | Recursive aggregation (legacy); wraps AggregationAir + child metadata |
| v6 | `_WQC_REC_AGG_V6_` / `_WQC_REC_TAIL_V6_` | Recursive aggregation with agg/leaf PCS certificates, in-circuit OOD, FriFold, DeepRo, Val/Challenge Mmcs |

**Layout** — v2/v4 carry a postcard-encoded Plonky3 proof after C-string public inputs. v3/v5/v6 embed compose headers (`parent_task_id`, `compose_label`, child hashes/digests/kinds) followed by the child proof bytes.

**Auxiliary segments** — Distribution (`_M31_DIST_V1_` / `_M31_DIST_V2_`), Born-zk (`_M31_BORN_STARK_V1_` / `_M31_BORN_LEAF_V1_`), trajectory (`_M31_TRAJ_V1_` / `_M31_TRAJ_V2_`), and trajectory-zk (`_M31_TRAJ_MARG_STARK_INNER_V1_` / `_M31_TRAJ_STARK_V1_` / `_M31_TRAJ_LEAF_V1_`) segments may follow or precede the unitary proof body.

All transcript details (field layout, verification steps, binding rules) are defined in the [STARK proof specification](https://github.com/world-qc/wqc-docs/blob/main/spec/zk-STARK.md).

## Build

```bash
cargo build --release
# CI / default: fast suite only (ignored heavy tests are skipped)
cargo test --release
```

### Heavy tests (local only)

RecAgg V6 / leaf PCS roundtrips prove nested Keccak STARKs and can take **hours** even in release. They are marked `#[ignore]` and **not** run on GitHub Actions (timeout + Actions minute quota).

Each ignored test can use **several GiB RAM** while proving. Uncapped parallelism (cargo default) often ends in **SIGKILL (signal 9)** from the OS OOM killer. Cap threads:

```bash
# Optional local stress / regression (release strongly recommended)
# --test-threads=4: ~5.5 h wall on a 16 GiB+ machine (16/16 ok measured)
# --test-threads=1: safer on low-RAM hosts
cargo test -p wqc-stark-core --features plonky3-stark --release -- --ignored --test-threads=4

# Single test (faster feedback; e.g. 2-leaf compose size ~85 min)
cargo test -p wqc-stark-core --features plonky3-stark --release unitary_trajectory_compose_roundtrip -- --ignored --nocapture
```

**Leaf PCS memory:** `build_leaf_pcs_certificate` / aggregation PCS use FriFold group proofs,
DeepRo per query, and chunked Keccak Mmcs groups (`WQC_PCS_MMCS_GROUP_CHUNK`, default **24**; see
[zk-STARK.md §8.4](https://github.com/world-qc/wqc-docs/blob/main/spec/zk-STARK.md)). Nested
uni-STARK workspaces are dropped after postcard encode between proves. **Memory gate:** when
`WQC_MAX_MEMORY_GB` is set and the peak estimate exceeds budget, `WQC_PCS_MEMORY_POLICY` is
`refuse` (default) or `spill` (auto-lower Mmcs chunk for that build). Cap `RAYON_NUM_THREADS`
on low-RAM hosts; raise core `mem_limit` (8G+) or use `spill` if refuse/OOM persists.

### Docker

```bash
docker build -t wqc-stark-builder .
docker run --rm -v "$(pwd)/dist:/output" wqc-stark-builder \
    cp target/release/libwqc_stark_verifier.a \
       target/release/libwqc_stark_verifier.so \
       /output/
```

## In-circuit recursion

With the `plonky3-stark` feature, leaf and aggregation PCS certificates bind FRI openings inside
`RecursiveAggregationAir` (v6) compose. Verify-time checks include in-circuit OOD (aggregation
and all leaf AIR kinds), FriFold, DeepRo, and Val/Challenge Mmcs. Born recursion supports
outcome dimension K≤21 (AIR width W≤68). Protocol details:
[zk-STARK.md §8](https://github.com/world-qc/wqc-docs/blob/main/spec/zk-STARK.md).

| Module (`wqc-stark-core/.../recursion/`) | Role |
|--------------------------------------------|------|
| `ood_air.rs` | `OodCheckAir` STARK: ζ quotient + aggregation in-circuit fold |
| `ood_native.rs` | Prove-time OOD witness extraction (FS replay) |
| `ood_bind.rs` | Bind OOD step to child openings at verify |
| `ood_leaf_fold.rs` | In-circuit leaf constraint fold (Unitary / Distribution / Shot) |
| `ood_fold.rs` | Native fold for prove-time witness sanity checks |
| `fri_mmcs_path.rs` | Per-step Keccak Mmcs path proofs (superseded by group fold on wire) |
| `fri_mmcs_path_m4a.rs` | Single Merkle path → batched Keccak path STARK |
| `fri_mmcs_group_m4b.rs` | Homogeneous Val/Chal paths → `KeccakGroupFoldProof` |
| `fri_mmcs_m4c.rs` | Leaf + aggregation Mmcs groups (bind, strip nested proofs) |
| `fri_fold_group.rs` | FriFold steps → `FriFoldGroupProof` (Y or X) |
| `fri_fold_m4c.rs` | Apply / strip / bind FriFold groups |
| `pcs_memory.rs` | PCS peak-RAM estimate, `refuse` / `spill` memory gate |
| `leaf_pcs_cert.rs` | Leaf cert prove/verify + Born/trajectory bundle decode |
| `transcript_v6.rs` | v6 encode / decode (agg cert or leaf bundle) |
| `prove.rs` | RecAgg matrix bind for leaf bundles |
| `air.rs` | Recursive aggregation AIR (leaf PCS columns) |
| `../aggregation/mod.rs` | Compose / verify context; optional prebuilt leaf PCS |

## Roadmap

- **Proof size / PCS:** Keccak Mmcs and FriFold group proofs; idle 2-leaf compose ≈ **16 MiB**.
  Mmcs chunk tunable via `WQC_PCS_MMCS_GROUP_CHUNK` (default **24**). Optional: recursion-friendly
  hash (e.g. Poseidon2) inside fold circuits.
- **Leaf PCS delivery:** winner `POST /leaf_pcs` + orchestrator P2P; compose binds prebuilt
  bundles with orchestrator fallback on refuse / timeout.
- Prove-time witness oracles in-circuit
- Multi-chunk quotient leaf DeepRo STARKs
- Full-stack multislice recursive aggregation compose on devnet

## Contributing

Contributions are welcome. See [CONTRIBUTING.md](CONTRIBUTING.md) for development setup, coding guidelines, and the pull request process.

## License

Distributed under the GNU General Public License v3.0 (GPLv3). See `LICENSE` for more information.

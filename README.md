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

* **`wqc-stark-core`**: Quantum execution AIR over Plonky3 Mersenne31 field types. Supports embedded trace verification, FRI STARKs via Plonky3 Circle PCS, distribution / trajectory segments, Born and shot-sampling AIRs, leaf compose proofs, and recursive aggregation (`RecursiveAggregationAir` v6 with agg/leaf PCS certificates; host-bound Mmcs/FriFold/OOD digests + optional nested group STARKs; Born K≤21, W≤68).
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
| v1 | `_M31_QUANTUM_AIR_V1_` | Legacy embedded-trace AIR (unitary only); still accepted by verifiers per [zk-STARK.md](https://github.com/world-qc/wqc-docs/blob/main/spec/zk-STARK.md), but production leaves use **v2** |
| v2 | `_M31_PLONKY3_STARK_V2_` | Plonky3 Circle PCS uni-STARK (unitary); primary leaf proof |
| v3 | `_WQC_COMPOSE_V3_` | Proof-tree compose — binds two child proofs by SHA3-256 hash (leaf or agg pairs) |
| v4 | `_WQC_AGG_STARK_V4_` / `_WQC_AGG_TAIL_V4_` | AggregationAir digest attestation |
| v5 | `_WQC_REC_AGG_V5_` / `_WQC_REC_TAIL_V5_` | Recursive aggregation (legacy); wraps AggregationAir + child metadata |
| v6 | `_WQC_REC_AGG_V6_` / `_WQC_REC_TAIL_V6_` | Recursive aggregation with agg/leaf PCS certificates (host Mmcs/FriFold/OOD bind; DeepRo when present) |

**Layout** — v2/v4 carry a postcard-encoded Plonky3 proof after C-string public inputs. v3/v5/v6 embed compose headers (`parent_task_id`, `compose_label`, child hashes/digests/kinds) followed by the child proof bytes.

**Auxiliary segments** — Distribution (`_M31_DIST_V1_` / `_M31_DIST_V2_`), Born-zk (`_M31_BORN_STARK_V1_` / `_M31_BORN_LEAF_V1_`), trajectory (`_M31_TRAJ_V1_` / `_M31_TRAJ_V2_`), and trajectory-zk (`_M31_TRAJ_MARG_STARK_INNER_V1_` / `_M31_TRAJ_STARK_V1_` / `_M31_TRAJ_LEAF_V1_`) segments may follow or precede the unitary proof body.

All transcript details (field layout, verification steps, binding rules) are defined in the [STARK proof specification](https://github.com/world-qc/wqc-docs/blob/main/spec/zk-STARK.md).

## FRI queries and SecurityLevel

Orchestrator `security_level` maps to FRI `num_queries` (operational ladder, **not** calibrated soundness bits):

| `security_level` | `num_queries` |
|------------------|---------------|
| `low` | 8 |
| `normal` | 16 |
| `high` | 32 |
| `ultra` | 40 (current default / [`DEVNET_FRI_NUM_QUERIES`]) |

API:

- `fri_num_queries_for_security_level(level)`
- `devnet_circle_config_with_queries(n)` / `circle_config_for_security_level(level, log_blowup)`

Leaf unitary, Born, trajectory, AggregationAir, RecAgg, and leaf/agg PCS certificates
select outer FRI query count from the same task-level `security_level` (PCS `n` comes from
`proof.query_proofs.len()`, cross-checked with the level when present).

**Nested Mmcs / FriFold policy** (see [zk-STARK.md §5.1](https://github.com/world-qc/wqc-docs/blob/main/spec/zk-STARK.md#51-securitylevel--fri-query-ladder)):

- **Production default:** nested FRI `num_queries` = outer `n` (weakest attestation link matches the task tier).
- **Shrink / experiment:** `WQC_PCS_NESTED_FRI_QUERIES` ∈ `{1,…,n}` when nested group STARKs are present. Idle Poseidon compose currently uses **host-only** Mmcs/FriFold/OOD (no nested group STARKs), so this knob does not change that root size. Not a silent `security_level` downgrade.
- Nested Mmcs / FriFold / OOD / DeepRo uni-STARKs follow `WQC_PCS_NESTED_FRI_QUERIES` (default = outer) when those STARKs are proven.
- **Idle Poseidon host-only:** nested group STARKs are empty, so changing nested query count does **not** change root size (nested4/8/16q fixtures match nested=outer at `173_483` B).

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

# Shrink regression: full idle two-leaf RecAgg (see CONTRIBUTING.md)
cargo test -p wqc-stark-core --features plonky3-stark --release \
  idle_two_leaf_rec_agg_compose_under_regression_ceiling -- --ignored --exact --nocapture
```

**Leaf PCS memory:** production idle Poseidon PCS is **host-only** (empty nested Mmcs/FriFold/OOD
group STARKs); the memory gate estimates decode + sibling + native-check workspace, not the
old blowup-16 group-prove matrix. See [zk-STARK.md §8.4](https://github.com/world-qc/wqc-docs/blob/main/spec/zk-STARK.md).
**Memory gate:** when `WQC_MAX_MEMORY_GB` is set and the peak estimate exceeds budget,
`WQC_PCS_MEMORY_POLICY` is `refuse` (default) or `spill` (auto-lower Mmcs chunk). Host-only
estimates typically fit a 2 GiB budget at 40q without spilling.

### Docker

```bash
docker build -t wqc-stark-builder .
docker run --rm -v "$(pwd)/dist:/output" wqc-stark-builder \
    cp target/release/libwqc_stark_verifier.a \
       target/release/libwqc_stark_verifier.so \
       /output/
```

## Recursive aggregation (RecAgg v6)

With the `plonky3-stark` feature, compose attaches a `RecursiveAggregationAir` (v6) tail when
both children carry verified PCS certificates. The RecAgg STARK asserts child digests, kinds,
and `pcs_ok` flags in-circuit — it does **not** re-verify nested Mmcs/FriFold/OOD Circle STARKs.

**PCS verify model (production idle Poseidon):** leaf/agg certificates ship **host-only**
Mmcs / FriFold / OOD: nested group STARKs are empty; verify replays Merkle digests from
retained siblings and checks FriFold/OOD algebra natively against openings already bound to
the parent FRI proof. DeepRo nested STARKs still apply on single-chunk paths (idle multi-chunk
ships `deep_ro=0`). Optional nested group STARKs remain supported on the wire for benchmarks.
Born recursion supports outcome dimension K≤21 (AIR width W≤68). Protocol details:
[zk-STARK.md §8](https://github.com/world-qc/wqc-docs/blob/main/spec/zk-STARK.md).

| Module (`wqc-stark-core/.../recursion/`) | Role |
|--------------------------------------------|------|
| `ood_air.rs` | OOD witness + host-native fold/quotient (empty `ood_stark` on wire) |
| `ood_native.rs` | Prove-time OOD witness extraction (FS replay) |
| `ood_bind.rs` | Bind OOD step to child openings at verify |
| `ood_leaf_fold.rs` | Leaf constraint fold helpers (Unitary / Distribution / Shot) |
| `ood_fold.rs` | Native OOD fold used at host bind |
| `fri_mmcs_path.rs` | Path stubs / digest verify (nested path STARKs stripped) |
| `fri_mmcs_path_m4a.rs` | Optional single-path batched STARK (benchmark / legacy) |
| `fri_mmcs_group_m4b.rs` | Optional homogeneous path → group STARK (benchmark / legacy) |
| `fri_mmcs_m4c.rs` | Leaf + agg Mmcs apply/bind (host-only empty groups by default) |
| `fri_fold_group.rs` | Optional FriFold group STARK (benchmark / legacy) |
| `fri_fold_m4c.rs` | FriFold apply/bind (host-native YX marker by default) |
| `pcs_memory.rs` | PCS peak-RAM estimate, `refuse` / `spill` memory gate |
| `leaf_pcs_cert.rs` | Leaf cert prove/verify + Born/trajectory bundle decode |
| `transcript_v6.rs` | v6 encode / decode (agg cert or leaf bundle) |
| `prove.rs` | RecAgg matrix bind for leaf bundles |
| `air.rs` | Recursive aggregation AIR (digest / pcs_ok columns) |
| `../aggregation/mod.rs` | Compose / verify context; optional prebuilt leaf PCS |

## Roadmap

- **Pre-wrap size KPI signed off (2026-09-04):** idle two-leaf Poseidon nested=outer / chunk40 host-only Mmcs/FriFold/OOD — `173_483` B ≤500 KB (`fixtures/e5b/poseidon-compose-default-chunk40.json`).
- **SNARK wrap of $\pi_{\text{Root}}$:** thin toolchain done in **[`wqc-snark-wrap`](https://github.com/world-qc/wqc-snark-wrap)** (E5b-2a–2c; E5b-2d thin KPIs). **E5b-3** thicken track: ValMmcs → FriFold → OOD → RecAgg/audit (`on-chain_settlement_scope.md` §7.2 / §7.6). E5b-3a host Poseidon2 goldens in `fixtures/e5b/wrap_poseidon2_mmcs_golden.json`. This repo stays the STARK engine / authoritative off-chain verify.
- **Root footprint shrink (Poseidon compose, idle two-leaf):**
  - Keccak-era documented baseline ≈ **10.2 MiB** (`fixtures/e5b/baseline.json` regression reference)
  - Production nested=outer / chunk40 ≈ **169 KiB** (`173_483` B) — **PASS ≤500 KB**
  - `low`/8q ≈ **38 KiB** (`39_386` B)
  - Host-only Mmcs/FriFold/OOD (siblings + digests; empty nested group STARKs)
  - `WQC_PCS_NESTED_FRI_QUERIES` does **not** change idle Poseidon root size under host-only
  - Prove/remeasure: `--features plonky3-stark`; `WQC_PCS_MMCS_GROUP_CHUNK=40`; `--poseidon-compose`
  - PR CI asserts `poseidon-compose-default-chunk40.json` ≤ gate (`poseidon_default_chunk40_fixture_under_shrink_gate`)
- **Leaf PCS delivery:** winner `POST /leaf_pcs` + orchestrator P2P; compose binds prebuilt
  bundles with orchestrator fallback on refuse / timeout
- Prove-time witness oracles in-circuit
- Multi-chunk quotient leaf DeepRo STARKs
- Full-stack multislice recursive aggregation compose on devnet

## Contributing

Contributions are welcome. See [CONTRIBUTING.md](CONTRIBUTING.md) for development setup, coding guidelines, and the pull request process.

## License

Distributed under the GNU General Public License v3.0 (GPLv3). See `LICENSE` for more information.

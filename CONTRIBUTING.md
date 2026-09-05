# Contributing to wqc-stark-engine

Thank you for your interest in contributing to **wqc-stark-engine**, the cryptographic proof engine for the World Quantum Computer decentralized quantum compute mesh.

## Code of Conduct

This project follows the [Contributor Covenant Code of Conduct](CODE_OF_CONDUCT.md). By participating, you agree to uphold it. Report unacceptable behavior using the contact details in that document.

## How to Contribute

Contributions are welcome in many forms:

- Bug reports and feature requests via [GitHub Issues](https://github.com/world-qc/wqc-stark-engine/issues)
- Documentation improvements
- Code changes via pull requests

If you plan a larger change, please open an issue first so we can discuss the approach and avoid duplicate work.

## Development Setup

### Prerequisites

- [Rust](https://www.rust-lang.org/tools/install) **1.95** or newer
- (Optional) [Docker](https://docs.docker.com/get-docker/) for containerized builds

### Clone and build

```bash
git clone https://github.com/world-qc/wqc-stark-engine.git
cd wqc-stark-engine
cargo build
```

### Workspace layout

```text
wqc-stark-engine/
├── wqc-stark-core/     # AIR prover/verifier (Rust library)
└── wqc-stark-ffi/      # CGO-compatible libwqc_stark_verifier
```

### Run tests

```bash
# Workspace tests (includes wqc-stark-core via wqc-stark-ffi)
cargo test

# Plonky3 STARK feature tests in wqc-stark-core
cargo test -p wqc-stark-core --features plonky3-stark
```

See [README.md](README.md) for release builds and Docker usage.

## Making Changes

1. Fork the repository and create a branch from `main`.
2. Make your changes in a focused, reviewable scope.
3. Run the checks below before opening a pull request.
4. Open a pull request against `main` with a clear description of the change and why it is needed.

### Branch naming

Use short, descriptive names, for example:

- `fix/air-boundary-check`
- `docs/phase3-plonky3`
- `feat/aggregation-compose`

## Coding Guidelines

- Write all source code, documentation, and comments in **English**.
- Keep proof transcript formats backward-compatible unless a version bump is intentional and documented.
- Follow common Rust conventions (`cargo fmt`, idiomatic error handling).
- Add or update tests when changing verifier behavior, AIR constraints, or FFI boundaries.

## Checks

Before submitting a pull request, run:

```bash
cargo fmt --all
cargo clippy --all-targets --all-features -- -D warnings
cargo test
cargo test -p wqc-stark-core --features plonky3-stark
cargo build --release -p wqc-stark-ffi
```

### Shrink regression (root size)

Idle two-leaf root proof size is tracked toward the 500 KB pre-wrap gate (`wqc-contracts` `on-chain_settlement_scope.md` §7).

**Pre-wrap size KPI signed off (2026-09-04):** production profile Poseidon nested=outer / `WQC_PCS_MMCS_GROUP_CHUNK=40`, host-only Mmcs/FriFold/OOD → `root_bytes = 173_483` (≤ `512_000`). Evidence fixture `fixtures/e5b/poseidon-compose-default-chunk40.json`; CI lock `poseidon_default_chunk40_fixture_under_shrink_gate`. KPI is idle two-leaf only; `fixtures/e5b/baseline.json` remains the Keccak-era regression reference (~10.7 MiB), not the shrink-gate number.

**Wrap status (sibling repos):** thin Groth16 toolchain (E5b-2a–2c) and thin KPI locks (E5b-2d partial) live in [`wqc-snark-wrap`](https://github.com/world-qc/wqc-snark-wrap) + `wqc-contracts` (§7.5). **E5b-3** thickens toward bit-for-bit parity with this engine’s `verify_root_proof` (scope §7.2 / §7.6). **E5b-3a** host Poseidon2 ValMmcs goldens: `fixtures/e5b/wrap_poseidon2_mmcs_golden.json` (locked by `poseidon2_default_permute_and_mmcs_golden`). Mainnet wrap gate remains blocked until E5b-3d + audit + target L2 gas. Until then, keep `verify_root_proof` / FFI as the authoritative root check (E5a challenge path).

Fast PR checks:

```bash
cargo test -p wqc-stark-core --features plonky3-stark --release \
  shrink_gate_constants_match_scope baseline_json_matches_constants r2_idle_two_leaf_root_under_max \
  poseidon_default_chunk40_fixture_under_shrink_gate
```

Full RecAgg + PCS compose (~hours) — local or scheduled workflow `.github/workflows/e5b-shrink-benchmark.yml`:

```bash
cargo test -p wqc-stark-core --features plonky3-stark --release \
  idle_two_leaf_rec_agg_compose_under_regression_ceiling -- --ignored --exact

# Or refresh fixtures/e5b/baseline.json + idle_two_leaf_root.bin:
cargo run -p wqc-stark-core --bin shrink-baseline --features plonky3-stark --release -- \
  --write-baseline --write-fixture

# Shrink optimization knobs (R3/PCS wire size):
#   --security-level low|normal|high|ultra   (outer FRI ladder; default = 40 queries)
#   WQC_PCS_MMCS_GROUP_CHUNK=40              (historical group chunk; host-only idle
#                                            Poseidon still records this in fixtures)
#   WQC_PCS_NESTED_FRI_QUERIES=8             (only affects size when nested group
#                                            STARKs are proven; host-only idle = no effect;
#                                            production default = match outer)
#
# Production Poseidon shrink-gate profile (nested=outer, chunk40):
WQC_PCS_MMCS_GROUP_CHUNK=40 \
cargo run -p wqc-stark-core --bin shrink-baseline \
  --features plonky3-stark --release -- --poseidon-compose

cargo run -p wqc-stark-core --bin shrink-baseline --features plonky3-stark --release -- \
  --security-level low
```

Baseline JSON lives at `fixtures/e5b/baseline.json`; the golden `idle_two_leaf_root.bin` is gitignored until generated locally.

Poseidon compose fixtures: `fixtures/e5b/poseidon-compose-default-chunk40.json` (outer=nested=40, **PASS** ≤500 KB; PR CI asserts `root_bytes`), `poseidon-compose.json` (low/8q), `poseidon-compose-default-chunk40-nested{4,8,16}q.json` (same root as nested=outer under host-only — nested FRI knob is size-inert). `fixtures/e5b/*-run.log` are local stdout captures and are gitignored.

Feature flags: use **`plonky3-stark`** for all shrink tooling (including `--poseidon-compose`). `poseidon-mmcs` remains a deprecated alias of `plonky3-stark`.

## Pull Request Guidelines

A good pull request:

- Has a concise title and description
- Explains the problem and the chosen solution
- Links related issues (for example, `Fixes #123`)
- Passes local checks listed above
- Keeps unrelated changes out of the diff
- Notes any proof-format or FFI ABI changes clearly

Maintainers may request changes or suggest an alternative approach. Once approved, your contribution will be merged.

## Licensing

By contributing, you agree that your contributions will be licensed under the same terms as the project: the [GNU General Public License v3.0](LICENSE).

## Questions

If something is unclear, open a [GitHub Issue](https://github.com/world-qc/wqc-stark-engine/issues) or ask in your pull request. We are happy to help you get started.

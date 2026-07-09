# Contributing to wqc-stark-engine

Thank you for your interest in contributing to **wqc-stark-engine**, the cryptographic proof engine for the World Quantum Computer decentralized quantum compute mesh.

## Code of Conduct

This project follows the [Contributor Covenant Code of Conduct](CODE_OF_CONDUCT.md). By participating, you agree to uphold it. Report unacceptable behavior using the contact details in that document.

## How to Contribute

Contributions are welcome in many forms:

- Bug reports and feature requests via [GitHub Issues](https://github.com/world-qc/wqc-stark-engine/issues)
- Documentation improvements (including `docs/`)
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
├── wqc-stark-ffi/      # CGO-compatible libwqc_stark_verifier
└── docs/               # Phase and aggregation design notes
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
- Cross-check trace semantics with `wqc-core/doc/trace-spec.md` when touching execution traces.

## Checks

Before submitting a pull request, run:

```bash
cargo fmt --all
cargo clippy --all-targets --all-features -- -D warnings
cargo test
cargo test -p wqc-stark-core --features plonky3-stark
cargo build --release -p wqc-stark-ffi
```

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

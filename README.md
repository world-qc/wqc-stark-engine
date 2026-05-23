# wqc-stark-engine

A high-performance STARK (Scalable Transparent ARgument of Knowledge) cryptographic engine designed for the decentralized mesh network. This repository serves as the core cryptographic backend for the Go-based orchestrator (`wqc-orchestrator`).

## Architecture Overview

This repository is structured as a Cargo Workspace to maintain a clean separation between the pure cryptographic logic and the C-compatible Foreign Function Interface (FFI).

```text
wqc-stark-engine/
├── Cargo.toml          # Workspace manifest
├── wqc-stark-core/     # Pure Rust implementation of STARK prover/verifier (crate-type = ["lib"])
└── wqc-stark-ffi/      # C-compatible wrapper for Go/CGO integration (crate-type = ["staticlib", "cdylib"])
```

* **`wqc-stark-core`**: Contains the core STARK proving and verifying logic (targeting production-grade frameworks such as Lambdaworks or Polygon Plonky3).
* **`wqc-stark-ffi`**: Provides a panic-safe, C-compatible API layer that compiles into static and dynamic libraries for seamless CGO binding.

## License
Distributed under the GNU General Public License v3.0 (GPLv3). See `LICENSE` for more information.

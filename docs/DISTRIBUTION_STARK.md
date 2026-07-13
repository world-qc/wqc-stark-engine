# Distribution & Trajectory STARKs (Phase C2)

Binds deterministic measurement distributions into the leaf proof pipeline (whitepaper §3.4.3 / §3.4.5).  
Planning notes live in the monorepo root `C2.md`; this document is the **engine contract**.

**Status (devnet):** C2a–C2c complete for noiseless `sample_counts`.

## Goal

```text
Unitary execution STARK
  → Born / marginal probabilities (deterministic)
  → PRNG(sample_seed) + inverse-CDF sampling (deterministic)
  → counts / output_result_hash
```

Guarantee shape: *these `counts` are the unique result of the proved unitary (or mid-circuit trajectory), the bound `sample_seed`, and the bound measurement spec.*

Noise-model trajectories (Phase C3) stay **unbound** (`distribution_bound = false`).

## Layers

| Layer | What is bound | Verify |
|-------|---------------|--------|
| **C2a algebraic** | Dist / traj segment: seed, shots, `measurement_spec_hash`, probability / trajectory digests; recompute counts | `verify_distribution_binding` / `verify_trajectory_binding` |
| **C2b Born zk** | Streaming `DistributionAir` over terminal Born table (+ optional unitary link digest) | Born STARK tail or `leaf:unitary_born` |
| **C2c trajectory zk** | Per unique pre-measure state Z-marginal AIR + optional per-shot Bernoulli AIR | Trajectory STARK bundle or `leaf:unitary_traj` |
| **C2c PI** | `measurement_spec_hash` in unitary v2 public-input binding (`MSH1` prefix) | Transcript binding + orch meta check |

## Soft caps

| Limit | Value | Notes |
|-------|------:|-------|
| Algebraic Born / marginal qubits | 16 | `BORN_AIR_MAX_QUBITS` |
| Plonky3 Born zk qubits | 16 | `BORN_ZK_MAX_QUBITS` (streaming AIR) |
| Born zk outcomes | 64 | `BORN_ZK_MAX_OUTCOMES` |
| Trajectory marginal zk qubits | 16 | `TRAJ_MARGINAL_ZK_MAX_QUBITS` |
| Per-shot sampling events | 2048 | `TRAJ_SHOT_SAMPLING_ZK_MAX_EVENTS` |

## Transcript appendages

### Distribution segment

Appended after the unitary proof body (or after compose children as appropriate):

| Marker | Payload |
|--------|---------|
| `_M31_DIST_V1_` | Legacy: seed, shots, probability digest, probs (no `measurement_spec_hash`) |
| `_M31_DIST_V2_` | seed, shots, `measurement_spec_hash`, probability digest, probs (+ optional Born binding) |

Optional Born zk tail: `_M31_BORN_TAIL_V1_` wrapping an inner Born STARK transcript.

### Trajectory segment

| Marker | Payload |
|--------|---------|
| `_M31_TRAJ_V1_` / `_M31_TRAJ_V2_` | Mid-circuit measure events, digests, optional `unitary_link_digest` |

Optional trajectory zk tail: `_M31_TRAJ_STARK_V1_` (marginal inners + optional shot-sampling inner).

## Public-input binding (unitary v2)

After the required cstr fields (`circuit_id`, `node_id`, `slice_id`, `output_hash`):

1. Optional `terminal_statevector_digest` — raw 64-char hex cstr (unitary↔Born / traj link).
2. Optional `measurement_spec_hash` — cstr `MSH1` + 64-char hex (`MEASUREMENT_SPEC_HASH_PI_PREFIX`).

`measurement_spec_hash` is **not** part of the Ed25519-style signed bid payload elsewhere; it is transcript-bound on the leaf STARK and mirrored in the JSON `PublicInputs` envelope by `wqc-core`.

`output_hash` for `sample_counts` is SHA3-256 of canonical counts JSON (not a scalar `ComplexResult`).

## Leaf compose labels (C2c)

Special v3 compose nodes (see also [PROOF_AGGREGATION.md](./PROOF_AGGREGATION.md)):

| `compose_label` | Left child | Right child | Typical orch scheme |
|-----------------|------------|-------------|---------------------|
| `leaf:unitary_born` | Unitary v2 (+ optional MSH / terminal digest) | Born leaf (`_M31_BORN_LEAF_V1_`) | `born_air_zk_composed_v1` |
| `leaf:unitary_traj` | Unitary v2 (+ link digest) | Trajectory leaf (`_M31_TRAJ_LEAF_V1_`) | `trajectory_air_zk_composed_shot_v1` (with shot AIR) |

Both attach an R2 `_WQC_AGG_TAIL_V4_` when built with `plonky3-stark`.

### Scheme ladder (orchestrator)

Terminal noiseless:

- `born_air_v1` → `born_air_zk_v1` → `born_air_zk_linked_v1` → `born_air_zk_composed_v1`

Mid-circuit noiseless:

- `trajectory_bound_v1` → `trajectory_air_zk_v1` → `…_linked_…` / `…_shot_…` → `trajectory_air_zk_composed_shot_v1`

## AIR sketch

### Streaming Born / marginal (`DistributionAir`)

One trace row per basis outcome (width independent of \(2^n\) column blowup). Fixed-point probabilities; sum-to-one and binding to digests / statevector link as configured.

### Shot sampling (`ShotSamplingAir`)

Per MEASURE event: fixed-point \(p_0,p_1\), host-supplied \(u\) (from `StdRng(shot_seed)` replay on verify), Bernoulli outcome, gap bit decomposition. Seed→\(u\) stays host-side; the AIR proves the fixed-point inequality for the claimed outcome.

## Rust API (high level)

```rust
use wqc_stark_core::{
    verify_distribution_binding, verify_trajectory_binding,
    append_distribution_tail, append_trajectory_tail,
};

#[cfg(feature = "plonky3-stark")]
use wqc_stark_core::{
    compose_unitary_born_leaf, compose_unitary_trajectory_leaf,
    generate_born_stark_proof, generate_trajectory_stark_bundle,
};
```

## FFI (orchestrator CGO)

| Function | Role |
|----------|------|
| `wqc_verify_distribution_binding` | Algebraic dist segment ↔ meta ↔ counts |
| `wqc_verify_trajectory_binding` | Algebraic traj segment ↔ meta ↔ counts |
| `wqc_proof_has_unitary_statevector_link` | Non-empty terminal digest link |
| `wqc_proof_has_trajectory_unitary_link` | Non-empty traj unitary link |
| `wqc_has_trajectory_zk_tail` | Marginal zk present |
| `wqc_has_trajectory_shot_sampling` | Shot-sampling zk present |
| `wqc_is_unitary_born_compose` | `leaf:unitary_born` |
| `wqc_is_unitary_trajectory_compose` | `leaf:unitary_traj` |

Leaf / root verify remain `wqc_verify_stark_proof` / `wqc_verify_root_proof` (compose routing is inside the core verifier).

## Out of scope (engine)

- Noise-model binding (C3)
- Expectation-mode distribution STARKs
- OpenQASM import
- Full in-circuit StdRng (seed→\(u\) remains host algebraic)

## Related docs

- [PROOF_AGGREGATION.md](./PROOF_AGGREGATION.md) — v3 tree + R2 agg + leaf compose
- [PHASE3_PLONKY3.md](./PHASE3_PLONKY3.md) — unitary Plonky3 leaf
- Monorepo `C2.md`, `wqc-docs/whitepaper/PHASE_C_SCOPE.md`

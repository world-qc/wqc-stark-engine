# Phase 3: Plonky3 uni-STARK migration

Phase 1 delivers an **AIR commitment** proof (embedded trace + recomputed constraint sum).
Phase 3 upgrades to a **real STARK** using Polygon Plonky3 `p3-uni-stark`.

## Prerequisites

1. Upgrade Plonky3 workspace deps from `0.1` → `0.5+` (Mersenne31 field + `p3-uni-stark`).
2. Implement `p3_air::Air` for the 19-column quantum execution matrix (`AIR_WIDTH`).
3. Wire Poseidon2 / FRI parameters consistent with devnet performance targets.

## Proof format (v2)

```text
<sub_task_id><_M31_PLONKY3_STARK_V2_><public inputs\0...><p3 proof bytes>
```

The v2 marker is reserved in `transcript::V2_MARKER`. v1 proofs remain valid until nodes upgrade provers.

## Feature flag

```bash
cargo build --release --features plonky3-stark
```

Scaffold lives in `wqc-stark-core/src/plonky3_stark.rs`.

## Rollout

| Step | Action |
|------|--------|
| 1 | Land `Air` + `StarkConfig` behind `plonky3-stark` feature |
| 2 | Dual-prove in CI: v1 AIR sum == 0 implies v2 verify OK on golden traces |
| 3 | Node prover emits v2; orchestrator accepts v1 + v2 during transition |
| 4 | Remove v1 after quorum on v2 |

## Open design items

- **Blowup / query count**: tune for ~28-qubit slice traces (variable row count).
- **Public inputs**: hash-bound fields should enter `StarkConfig` verifier instance.
- **RX/RY/RZ**: separate rotation AIR columns vs shared `sel_rot` (trace-spec follow-up).

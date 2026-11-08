# wqc-sv-stark

State-vector STARK leaf (v2). A leaf proves that applying a circuit to |0…0⟩ yields a final
state vector with a given terminal digest, and leaves recurse and aggregate into a root of
roughly constant size.

Status: experimental. Nothing in the network uses it yet; it will ship behind the
`feat_sv_stark_v2` capability bit.

## What a proof means

- **Circuit.** The gate list and qubit count are committed as preprocessed columns when the
  leaf is built. A proof only verifies against the verifier of the circuit it was built for
  (`Leaf::verifier()`), so a verifier must be derived from the expected circuit, never taken
  from the prover.
- **Statement.** `[context(4), digest(4)]`. The context is caller-supplied (task binding); the
  digest is computed in-circuit from the final state. The statement does not name the
  circuit: it is meaningful only together with that circuit's verifier.
- **Digest.** A Poseidon2 sponge (Goldilocks, width 8, rate 4) over the final amplitudes, two
  amplitudes per block, from the zero state; the digest is the first four state elements.
  The round constants are not the standard Goldilocks Poseidon2 ones: they are drawn from
  `SmallRng::seed_from_u64(7)` (rand pinned to `=0.10.3`) and fixed by a known-answer test.
- **Arithmetic.** Amplitudes are fixed point in units of 2^-24. Each gate output is floored,
  and the remainder and output are range-checked, so the error grows by at most 2^-24 per
  gate per component.

## Limits

- `1 ≤ n ≤ 16` qubits (`MAX_QUBITS`). Gates act on one target with distinct controls, all
  below `n`, and matrix entries of magnitude at most 1. `build` rejects anything else.
- The gate table has `gates · 2^(n−1)` rows. With `FriParams::PRODUCTION` on an 8-core
  machine, 64 gates take about 1.5 s at n = 10 and 70 s / 14 GB at n = 16.

## Usage

```rust,ignore
use wqc_sv_stark::exec::Gate;
use wqc_sv_stark::recursion::{verify, Aggregation, Layer};
use wqc_sv_stark::{leaf, FriParams};

let fri = FriParams::PRODUCTION;
let gates = vec![Gate::h(0), Gate::cnot(0, 1)];
let bell = leaf::build(fri, 2, gates)?;

// Leaf: prove under a context, verify against the expected statement.
let a = bell.prove([1, 2, 3, 4])?;
bell.verify(&a.proof, &a.statement)?;

// First recursion layer over leaves of this circuit; its proofs verify against the leaf
// statement with the layer's verifier.
let layer = Layer::over_leaf(&bell, &a, fri)?;
let ra = layer.prove(&a.proof, &a.statement)?;
verify(&layer.verifier(), &ra.proof, &a.statement)?;

// 2-to-1 aggregation: the root verifies against left ‖ right.
let b = bell.prove([5, 6, 7, 8])?;
let rb = layer.prove(&b.proof, &b.statement)?;
let agg = Aggregation::new((layer.verifier(), &ra), (layer.verifier(), &rb), fri)?;
let root = agg.prove(&ra, &rb)?;
verify(&agg.verifier(), &root.proof, &root.statement)?;
```

Recursion goes through Plonky3-recursion's trusted prepared owners: each layer keeps its
child's verifier, so the child relation (tables, AIRs, preprocessed commitment) is fixed by
that verifier rather than read from the proof.

## Tests

Run in release:

```sh
cargo test -p wqc-sv-stark --release
```

Debug builds assert AIR constraints inside `prove`, so the forgery tests are ignored there.
The crate is outside the workspace's `default-members` (Plonky3-recursion builds slowly) and
has its own CI job.

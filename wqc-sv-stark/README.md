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
- **Arithmetic.** Amplitudes are integers in units of 2^-28 (`S = 2^28`). Each gate output
  is `Σ m·a / S` rounded to nearest, ties up: the gate table proves `b·S + r = Σ m·a + S/2`
  with `r ∈ [0, S)` and `b ∈ [−2S, 2S)` range-checked. Both sides stay below 2^60 in
  magnitude, so the field equation is the integer one.
- **What the result is.** The final integer state vector is the result: execution is
  integer-only and bit-exact on any hardware (CPU or GPU), and a float view is that vector
  divided by `S`. Gate matrices are rounded from `f64` once, at build; the one
  platform-dependent step there would be the `sin`/`cos` of RX/RY/RZ, so they come from the
  pure-Rust `libm` (pinned to `=0.2.16`) and every party derives the same circuit. A
  known-answer test pins a few quantized rotations; the pin is what guarantees the rest.
- **Error.** Per gate, the L2 distance from the ideal state grows by at most
  `(√(2^(n+1)) + 2√8) · 2^-29` (output rounding, plus matrix quantization). For n = 16 and
  1000 gates that bound is 6.8e-4; random circuits measure about 7e-6, since nearest rounding
  is unbiased and the error walks rather than drifts.

## Limits

- `1 ≤ n ≤ 16` qubits (`MAX_QUBITS`).
- Gates: wqc-core's unitary gate set — H, X, Y, Z, S, T, CNOT, CZ, CCNOT, RX, RY, RZ — with the same
  matrices and phases as its dense engine (a test checks each gate against those formulas,
  global phase included, since it changes the digest). Rotation angles become fixed-point
  matrices. There is no public arbitrary-matrix gate; the protocol has none (the
  `CUSTOM_UNITARY` capability bit names the rotations).
- `build` rejects targets or controls outside `n`, repeated controls, and matrices that are
  not unitary up to rounding (which includes a NaN or infinite angle).
- The gate table has `gates · 2^(n−1)` rows. On an 8-core machine, a 64-gate leaf at n = 16
  takes about 33 s and 11 GB to prove at any tier (see below).

## Security levels

The orchestrator's `security_level` sets the leaf's FRI query count (`FriParams::leaf`).
Every tier uses rate 1/4 and a 16-bit query PoW, so prove time and memory are the same at
every tier; only the leaf proof size changes. Recursion layers and aggregation always use
`FriParams::RECURSION`, so a tree is as sound as its leaves' tier, every layer above the first
has one verifier, and the root has the same size at every tier.

| Tier | Leaf queries | Conjectured bits | Leaf proof (n = 16, 64 gates) |
|---|---:|---:|---:|
| `low` | 22 | 60 | 209 KB |
| `normal` | 32 | 80 | 289 KB |
| `high` | 37 | 90 | 332 KB |
| `ultra` (or empty) | 42 | 100 | 365 KB |
| recursion / aggregation | 28 at rate 1/8 | 100 | 187 KB (first layer) |

Bits are the FRI estimate `log_blowup · queries + PoW bits`. The rest of the soundness error
is bounded by the 128-bit Goldilocks² field less the domain size and constraint degree; a
rough estimate puts that ceiling near 100 bits, so no tier claims more.

## Usage

```rust,ignore
use wqc_sv_stark::exec::Gate;
use wqc_sv_stark::recursion::{verify, Aggregation, Layer};
use wqc_sv_stark::{leaf, FriParams, SecurityLevel};

let level = SecurityLevel::parse("normal").expect("known tier");
let gates = vec![Gate::h(0), Gate::cnot(0, 1)];
let bell = leaf::build(FriParams::leaf(level), 2, gates)?;
let fri = FriParams::RECURSION;

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

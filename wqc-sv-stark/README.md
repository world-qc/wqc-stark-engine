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
- The gate tables have `2^(n−1)` rows per rounding gate. The rounding steps are split over up
  to three gate tables (the two largest powers of two that fit, then the rest; an empty one is
  omitted), so the rows pad to at most about a quarter more than needed instead of nearly
  double. A gate rounds
  unless its quantized matrix is monomial: in practice H, T and RX/RY/RZ at generic angles
  round, while X, Y, Z, S, CNOT, CZ, CCNOT (and rotations such as RZ(π)) add no rows (see
  below). On an 8-core
  machine, a leaf at n = 16 with 64 rounding gates takes about 33 s and 11 GB to prove; a
  64-gate brickwork of RY and CNOT layers (32 rounding) takes 18 s and 6 GB, and 64 gates
  cycling H / CNOT / RY / T (48 rounding, split 32 + 16) take 27 s and 7 GB.

## Monomial gates

X, Y, Z, S, CNOT, CZ and CCNOT (and any rotation whose quantized matrix is monomial) map each
amplitude to one other times a unit phase, and their fixed-point outputs are exact. `build` folds them into a frame instead of giving them rows:
logical amplitude `k` is `i^phase[k]` times stored position `perm[k]`. A rounding gate reads
the stored positions its logical pairs map to, with the phases folded into its matrix entries
(exact), and the boundary table applies the final frame before the digest. The result is the
dense execution's bit for bit (a test checks random circuits); only the rows change.

## Security levels

The orchestrator's `security_level` sets the leaf's FRI query count: `leaf::build` takes a
`SecurityLevel` and uses `FriParams::leaf`. Every tier uses rate 1/4 and a 16-bit query PoW;
prove time and memory are set by the rate, so they are nearly the same at every tier
(n = 16 with 64 rounding gates, the worst case for 64 gates: 32–35 s), and the tier mainly
changes the leaf proof size.

Every recursion proof (layers and aggregation) uses `FriParams::RECURSION`; the public
constructors take no FRI parameters. A tree is therefore as sound as its leaves' tier, and the
recursion's own FRI parameters are the same at every tier. A layer's verifier still depends on
its child, so the first layer over a `low` leaf and over an `ultra` leaf are different
verifiers. Recursion proofs are roughly the same size at every tier.

| | FRI queries | `log_blowup · q + PoW` | Estimated bits | Binding term | Proof size (n = 16, 64 rounding gates, one gate table) |
|---|---:|---:|---:|---|---:|
| `low` leaf | 22 | 60 | 59 | FRI queries | 209 KB |
| `normal` leaf | 32 | 80 | 79 | FRI queries | 289 KB |
| `high` leaf | 37 | 90 | 89 | FRI queries | 332 KB |
| `ultra` (or empty) leaf | 42 | 100 | 95 | Field terms | 365 KB |
| Recursion layer / aggregation | 28 at rate 1/8 | 100 | 99 | FRI queries | 174–203 KB (first layer, low and ultra leaves, n = 4 and 16) |

Proof sizes vary by a few KB from proof to proof (postcard writes field elements as varints,
and their values follow the transcript; one 12-qubit circuit measured 320–328 KB across six
contexts), and each extra gate table adds about 20 KB, so a split leaf can be larger than a
one-table leaf with more rounding steps (48 steps, 32 + 16: 389 KB).

**Estimated bits** are conjectured soundness from p3-security 0.9.0-rc.2 (random-words regime,
128-bit collision-resistant commitments), for the largest leaves (n = 16, every gate rounding:
64 steps fill one 2^21-row gate table; 100 steps split 64 + 32 + 4, so the largest table is
still 2^21 rows but there are more columns and lookups). Fewer rounding gates only shorten the
trace and raise the field terms. The query phase comes out about a bit below the simple
`log_blowup · q + PoW` because of the rate's proximity margin. At `ultra` the binding terms are
the Goldilocks² ones that grow with the trace and the column count: the random combination
batching the opened columns (96.4 bits at 64 steps; 96.0 at 100 steps, 95.4 if the extra gate
tables' columns are counted generously) and the LogUp fingerprint (98.0 / 97.3, 28 lookups per gate row, widest message 16). The built-in config grinds none of those
challenges, so more queries would not raise the ceiling; a larger extension field would.
The column and constraint counts behind the estimate are approximate (±1 bit). Proven
(Johnson-bound) soundness is far lower (38–58 bits), as for FRI-based STARKs generally; the
tiers rest on the conjectured regime.

- **The tier is not in the statement.** It is part of the leaf's verifier, and a proof made at
  another tier fails it. Build the verifier from the authoritative tier (the dispatched
  `SubTask.security_level`), never from anything the prover claims.
- **Names** parse trimmed and case-insensitive, like v1; empty means `ultra`. Unlike v1, an
  unknown name is rejected rather than treated as `ultra`.
- **Not v1's ladder.** v1 leaves use 8 / 16 / 32 / 40 queries on another field (wqc-docs
  `spec/zk-STARK.md` §5.1), and the fee multiplier `num_queries / 16` assumes that ladder.
  Both are to be updated when the orchestrator adopts v2 leaves.

## Usage

```rust,ignore
use wqc_sv_stark::exec::Gate;
use wqc_sv_stark::recursion::{verify, Aggregation, Layer};
use wqc_sv_stark::{leaf, SecurityLevel};

let level = SecurityLevel::parse("normal").expect("known tier");
let gates = vec![Gate::h(0), Gate::cnot(0, 1)];
let bell = leaf::build(level, 2, gates)?;

// Leaf: prove under a context, verify against the expected statement.
let a = bell.prove([1, 2, 3, 4])?;
bell.verify(&a.proof, &a.statement)?;

// First recursion layer over leaves of this circuit; its proofs verify against the leaf
// statement with the layer's verifier.
let layer = Layer::over_leaf(&bell, &a)?;
let ra = layer.prove(&a.proof, &a.statement)?;
verify(&layer.verifier(), &ra.proof, &a.statement)?;

// 2-to-1 aggregation: the root verifies against left ‖ right.
let b = bell.prove([5, 6, 7, 8])?;
let rb = layer.prove(&b.proof, &b.statement)?;
let agg = Aggregation::new((layer.verifier(), &ra), (layer.verifier(), &rb))?;
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

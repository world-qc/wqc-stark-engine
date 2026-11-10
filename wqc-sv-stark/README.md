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
- **Statement.** `[context(4), digest(4)]`, eight Goldilocks elements and fixed (a sampling
  leaf appends the seed, shot count and counts digest; see [Sampling](#sampling)). The context
  binds the proof to its dispatch (below); the digest is computed in-circuit from the final
  state. Both are public values of the proof, so a proof verifies only against its own. The
  statement does not name the circuit: it is meaningful only together with that circuit's
  verifier.
- **Context.** `leaf::Dispatch { circuit_id, sub_task_id, node_id, slice_id }.context()`:
  SHA3-256 of `WQC_SV_CTX_V1` followed by each field as its byte length (`u32`
  little-endian, counting UTF-8 bytes, not characters) and its UTF-8 bytes, in that order;
  the 32 bytes split into four little-endian `u64` words, each reduced modulo the Goldilocks
  prime `2^64 − 2^32 + 1`. That keeps about 128 bits of collision resistance (the birthday
  bound on 256 bits; the reduction merges a 2^-32 fraction of each word's values). The tag's
  `V1` versions this encoding only, not the leaf format. Known-answer tests pin the encoding,
  including a reduced word and a non-ASCII field.
  - The fields are hashed exactly as the orchestrator signed them, with no normalization. Their
    canonical forms (hex case of `circuit_id`, the `node_id` notation, `slice_id` for an
    unsliced task) and their relation to v1's binding (`circuit_id`, `node_id`, `slice_id`,
    `output_hash`, NUL-separated) are for the v2 spec in wqc-docs to fix.
  - A verifier builds the expected statement from the dispatch it signed and the digest it
    expects, never from the prover's `LeafProof::statement`; `Leaf::verify_dispatch` does
    this.
  - The context differs per node, so a node cannot submit another node's proof, while the
    digest is the same for every honest node: a quorum compares `statement[4..]`, not whole
    statements.
  - Not included: the output payload (the digest is the result; the payload will be checked
    against it), the security tier (part of the verifier), and measurement data (a Born
    leaf's own statement).
- **Digest.** A Poseidon2 sponge (Goldilocks, width 8, rate 4) over the final amplitudes, two
  amplitudes per block, from the zero state; the digest is the first four state elements.
  The round constants are not the standard Goldilocks Poseidon2 ones: they are drawn from
  `SmallRng::seed_from_u64(7)` (rand pinned to `=0.10.3`) and fixed by a known-answer test.
- **Arithmetic.** Amplitudes are integers in units of 2^-28 (`S = 2^28`). Each gate output
  is `Σ m·a / S` rounded to nearest, ties up: the gate table proves `b·S + r = Σ m·a + S/2`
  with `r ∈ [0, S)` and `b ∈ [−2S, 2S)` range-checked. Both sides stay below 2^60 in
  magnitude, so the field equation is the integer one.
- **What the result is.** The final integer state vector of the fused circuit (see
  [Fusion](#fusion)) is the result: execution is integer-only and bit-exact on any hardware
  (CPU or GPU), and a float view is that vector divided by `S`. Gate matrices are rounded from
  `f64` once, at build, after fusion; the one platform-dependent step there would be the
  `sin`/`cos` of RX/RY/RZ, so they come from the pure-Rust `libm` (pinned to `=0.2.16`) and
  every party derives the same circuit. Known-answer tests pin a few quantized rotations and a
  fused product; the pins are what guarantee the rest.
- **Error.** Per gate (fused gates count once), the L2 distance from the ideal state grows by at most
  `(√(2^(n+1)) + 2√8) · 2^-29` (output rounding, plus matrix quantization). For n = 16 and
  1000 gates that bound is 6.8e-4; random circuits measure about 7e-6, since nearest rounding
  is unbiased and the error walks rather than drifts.

## Limits

- `1 ≤ n ≤ 16` qubits (`MAX_QUBITS`).
- At most `2^22` gate rows (`MAX_ROWS`): rounding steps × `2^(n−1)`, so 128 rounding steps at
  n = 16. `leaf::gate_rows(n, gates)` counts them without building the leaf (it is the work
  `W` a scheduler compares with what a node can prove); `build` rejects a circuit over the
  limit. Proving takes about 4.6 KB per gate row plus 0.3 GB, so a leaf at the limit needs
  about 20 GB. Building its verifier alone (`leaf::build_verifier`, see below) peaks at about
  370 bytes per gate row (1.45 GB at the limit) and keeps under 1 MB;
  `leaf::verifier_peak_bytes(n, rows, shots)` is an upper estimate of that peak, for a
  scheduler to size what it verifies to its memory.
- Gates: wqc-core's unitary gate set — H, X, Y, Z, S, T, CNOT, CZ, CCNOT, RX, RY, RZ — with the same
  matrices and phases as its dense engine (a test checks each gate against those formulas,
  global phase included, since it changes the digest). Rotation angles become fixed-point
  matrices. There is no public arbitrary-matrix gate; the protocol has none (the
  `CUSTOM_UNITARY` capability bit names the rotations).
- `build` rejects targets or controls outside `n`, repeated controls, and matrices that are
  not unitary up to rounding (which includes a NaN or infinite angle).
- The gate tables have `2^(n−1)` rows per rounding step. The rounding steps are split over up
  to three gate tables (the two largest powers of two that fit, then the rest; an empty one is
  omitted), so the rows pad to at most about a quarter more than needed instead of nearly
  double. A fused gate
  rounds unless its quantized matrix is monomial: in practice H, T and RX/RY/RZ at generic
  angles round, while X, Y, Z, S, CNOT, CZ, CCNOT (and rotations such as RZ(π)) add no rows
  (see below). On an 8-core machine, a leaf at n = 16 with 64 rounding steps takes about 33 s
  and 11 GB to prove; a 64-gate brickwork of RY and CNOT layers (32 steps) takes 19 s and 5.5
  GB, and 64 gates cycling H / CNOT / RY / T (20 steps after fusion, 16 + 4) take 13 s and
  3.5 GB.

## Monomial gates

X, Y, Z, S, CNOT, CZ and CCNOT (and any rotation whose quantized matrix is monomial) map each
amplitude to one other times a unit phase, and their fixed-point outputs are exact. `build` folds them into a frame instead of giving them rows:
logical amplitude `k` is `i^phase[k]` times stored position `perm[k]`. A rounding step reads
the stored positions its logical pairs map to, with the phases folded into its matrix entries
(exact), and the boundary table applies the final frame before the digest. The result is the
dense execution's bit for bit (a test checks random circuits); only the rows change.

## Fusion

`build` first rewrites the gate list by one fixed rule, and the result is defined on the
rewritten list. Each qubit keeps a pending product of the single-qubit gates applied to it
(rounding or monomial) since a multi-qubit gate last touched it. A gate with controls first
emits the pending products of the qubits it touches, as control or target, in ascending qubit
order, then itself; at the end the remaining products are emitted in ascending qubit order.
A product is computed in `f64` from the gates' unrounded matrices, each new gate multiplied
from the left: the run `G_1, …, G_L` (in circuit order) becomes `G_L · … · G_1`. Each step
`a · b` (`a` the new gate, `b` the product so far) is computed entry by entry as
`(a_r0·b_0c) + (a_r1·b_1c)` with complex products `(xr·yr − xi·yi, xr·yi + xi·yr)` (IEEE
basic operations, no fused multiply-add), and the final product is rounded once like any gate
matrix. `build` validates the fused gates as it does the given ones.

So a run of single-qubit gates costs at most one rounding step, and none if its product
rounds to a monomial matrix (H·H, H·Z·H, RZ(π/2)²). A lone gate is unchanged, but a
single-qubit gate is emitted where its run ends, not where it appears, so rounding steps on
different qubits may run in another order than written. A gate never moves past another gate
that touches its qubit: an RZ on a CNOT's control qubit stays on its side of the CNOT,
although the two commute. Changing the rule changes the result, so the rule is part of the
leaf format: before anything consumes these digests, the leaf format will be tied to a
capability bit or leaf version, and a new rule needs a new one.

## Sampling

`leaf::build_sampling(level, n, gates, sampling)` builds a `sample_counts` leaf: the same
circuit followed by terminal Z measurements (`Sampling { measures, cbits, shots }`, each
`Measure { qubit, cbit }`), and a proof also proves the counts of `shots` shots drawn from the
final state under a seed. The unitary part and its digest are unchanged; the sampling tables
read the final amplitudes from the boundary table, so one proof covers both.

- **Weights.** `p_b = re_b² + im_b²` of the final logical amplitudes (integers in units of
  2^-56), with running sums `C_b = p_0 + … + p_b` and total `T = C_{2^n−1}` (about 2^56; it
  is not exactly 2^56 because of rounding, and nothing is divided by it).
- **Draws.** Draw `j` is `u_j = r_j mod 2^57`, where `r_j` is word `j mod 4` of the leaf's
  Poseidon2 permutation of `[seed_lo, seed_hi, ⌊j/4⌋, 0, 0x50524631, 0, 0, 0]`, as a
  canonical integer below the Goldilocks prime `p`. The words below `2^57 − 2^32 + 1` occur
  equally often among field elements, and all of `[0, T)` lies below that, so an accepted draw
  is uniform on `[0, T)`.
- **Choice.** A draw with `u_j ≥ T` is rejected; otherwise it picks the basis state `b` with
  `C_{b−1} ≤ u_j < C_b`. Draws continue until `shots` are accepted, so each shot picks `b`
  with probability `p_b / T`. About half the draws are accepted; the leaf provides
  `2s + 14⌈√(2s)⌉ + 128` draws (rounded up to a multiple of four) for `s` shots, which run out
  with probability below 2^-115, and proving fails if they do.
- **Counts.** A shot of basis state `b` counts toward the classical register its measurements
  give it: bit `cbit` is the measured qubit's bit, a later measure into the same cbit wins,
  and unmeasured cbits are 0. The counts are a vector indexed by the register value
  (`max(2^cbits, 4)` entries), and their digest is a Poseidon2 sponge over that vector, four
  counts per block from the zero state, the first four state elements (`born::counts_digest`).
- **Statement.** `[context(4), digest(4), seed_lo, seed_hi, shots, counts_digest(4)]`
  (`SAMPLING_STATEMENT_LEN = 15`). The measurements and shot count are part of the circuit;
  the seed is not, so one verifier serves every seed. `Leaf::verify_sampling(proof, &dispatch,
  digest, seed, &counts)` builds the expected statement from the dispatch, the expected state
  digest, the dispatched seed and the reported counts. The statement holds only the counts'
  digest, which reduces each count mod p, so the reported counts must be canonical: a `u64`
  vector of `counts_len` entries, each at most `shots`, summing to `shots`.
  `verify_sampling` checks this; a caller building the statement with `sampling_statement`
  must check it too. Every honest node reports the same counts, so a quorum compares
  `statement[4..]` once each node's counts pass that check.
- **Not v1's sampling.** v1 draws `f64` values from `StdRng` (ChaCha12) against `f64`
  probabilities, which cannot be proved at reasonable cost. The same seed gives different
  counts here, from the same distribution.
- **Limits.** `1 ≤ shots ≤ 2^16`, `1 ≤ cbits ≤ 16`, every measure inside `n` and `cbits`.
- **Cost.** The sampling adds `2^n` weight rows, the draw rows, a quarter as many
  permutations, and `max(2^cbits, 4)/4` counts rows. On an 8-core machine, a leaf at n = 16
  with 64 rounding steps, all 16 qubits measured, proves in 35 s with 1024 shots and 42 s with
  2^16 shots (35 s without sampling); the proof grows by about 80–100 KB.

## Security levels

The orchestrator's `security_level` sets the leaf's FRI query count: `leaf::build` takes a
`SecurityLevel` and uses `FriParams::leaf`. Every tier uses rate 1/4 and a 16-bit query PoW;
prove time and memory are set by the rate, so they are nearly the same at every tier
(n = 16 with 64 rounding steps, the worst case for 64 gates: 32–35 s), and the tier mainly
changes the leaf proof size.

Every recursion proof (layers and aggregation) uses `FriParams::RECURSION`; the public
constructors take no FRI parameters. A tree is therefore as sound as its leaves' tier, and the
recursion's own FRI parameters are the same at every tier. A layer's verifier still depends on
its child, so the first layer over a `low` leaf and over an `ultra` leaf are different
verifiers. Recursion proofs are roughly the same size at every tier.

| | FRI queries | `log_blowup · q + PoW` | Estimated bits | Binding term | Proof size (n = 16, 64 rounding steps, one gate table) |
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
128-bit collision-resistant commitments), for the largest leaves `MAX_ROWS` allows (n = 16,
128 rounding steps in one 2^22-row gate table). Fewer rounding steps only shorten the trace and
raise the field terms. The query phase comes out about a bit below the simple
`log_blowup · q + PoW` because of the rate's proximity margin. At `ultra` the binding terms are
the Goldilocks² ones that grow with the trace and the column count: the random combination
batching the opened columns (95.4 bits at 2^22 rows, 94.4 if the columns are counted
generously; 96.4 at 64 steps in 2^21 rows) and the LogUp fingerprint (97.0 at 2^22 rows, 98.0
at 2^21; 28 lookups per gate row, widest message 16). The built-in config grinds none of those
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
use wqc_sv_stark::digest::terminal_digest;
use wqc_sv_stark::exec::{execute, Gate};
use wqc_sv_stark::recursion::{verify, Aggregation, Layer};
use wqc_sv_stark::{leaf, SecurityLevel};

let level = SecurityLevel::parse("normal").expect("known tier");
let gates = vec![Gate::h(0), Gate::cnot(0, 1)];
let bell = leaf::build(level, 2, gates.clone())?;

// The node proves under its dispatch's context.
let d1 = leaf::Dispatch {
    circuit_id: "circuit-id",
    sub_task_id: "sub-task-1",
    node_id: "node-a",
    slice_id: "0",
};
let a = bell.prove(d1.context())?;

// The verifier never trusts `a.statement`: it expects a digest (the quorum's, or here one
// recomputed from honest execution) and its own dispatch.
let digest = terminal_digest(&execute(2, &gates).1);
bell.verify_dispatch(&a.proof, &d1, digest)?;
let expected_a = leaf::statement(d1.context(), digest)?;

// First recursion layer over leaves of this circuit; its proofs verify against the leaf
// statement with the layer's verifier.
let layer = Layer::over_leaf(&bell, &a)?;
let ra = layer.prove(&a.proof, &a.statement)?;
verify(&layer.verifier(), &ra.proof, &expected_a)?;

// 2-to-1 aggregation: the root verifies against left ‖ right.
let d2 = leaf::Dispatch { sub_task_id: "sub-task-2", ..d1 };
let b = bell.prove(d2.context())?;
let rb = layer.prove(&b.proof, &b.statement)?;
let agg = Aggregation::new((layer.verifier(), &ra), (layer.verifier(), &rb))?;
let root = agg.prove(&ra, &rb)?;
let expected_root = [expected_a, leaf::statement(d2.context(), digest)?].concat();
verify(&agg.verifier(), &root.proof, &expected_root)?;
```

A sampling leaf proves with a seed and also returns the counts:

```rust,ignore
let s = Sampling { measures: vec![Measure { qubit: 0, cbit: 0 }, Measure { qubit: 1, cbit: 1 }], cbits: 2, shots: 1024 };
let bell = leaf::build_sampling(level, 2, gates.clone(), s)?;
let (p, counts) = bell.prove_sampling(d1.context(), seed)?;
bell.verify_sampling(&p.proof, &d1, digest, seed, &counts)?;
```

Recursion goes through Plonky3-recursion's trusted prepared owners: each layer keeps its
child's verifier, so the child relation (tables, AIRs, preprocessed commitment) is fixed by
that verifier rather than read from the proof.

### Wire format and the verifier to keep

`wire::parse_circuit` reads wqc-core's gate JSON (`[{"type":"H","params":0},
{"type":"RZ","params":[0,0.5]}, …]`, terminal `MEASURE`s last; no RESET or IF), and
`wire::parse_counts` / `wire::counts_json` convert counts to and from the canonical
`{"counts":{"01":3,…},"shots":N}` (Qiskit key order, zero counts omitted; `parse_counts`
accepts only the exact bytes `counts_json` writes). They are meant for both sides: the verifier
(through the FFI) uses them now, and wqc-core is to use them when it proves v2 leaves, so both
derive the same gates and counts. `serde_json` parses with `float_roundtrip`, so an angle is
the exact `f64` the orchestrator marshaled; once wqc-core depends on this crate, feature
unification turns it on for its parsing too. Proofs travel
as `leaf::encode_proof` / `decode_proof` (postcard, pinned).

A `LeafVerifier` is a leaf's verifier and sampling without the proving data, to keep (one per
circuit). `Leaf::leaf_verifier()` takes it from a built leaf; `leaf::build_verifier(level, n,
gates, sampling)` builds it without one, in less memory: a `VerifyCfg` (`verify_cfg`) prepares
the same circuit with a PCS that computes the preprocessed commitment 64 runs of LDE rows at a
time (each run a coset of a smaller subgroup, under its own subtree) and keeps no prover data,
and delegates everything verification uses to the leaf config's PCS. A test checks the
commitment against the leaf config's, and verifiers built either way accept the same proofs.
At n = 16 the peak falls from about 0.94 KB to 0.37 KB per gate row (2^22 rows: 3.7 to 1.45
GB); what remains is the framework's own copies of the preprocessed columns. The orchestrator
reaches it through `wqc-stark-ffi` (`wqc_sv_leaf_rows`, `wqc_sv_max_rows`, `wqc_sv_leaf_new` /
`wqc_sv_leaf_free`, `wqc_sv_verify_leaf`, `wqc_sv_verify_sampling_leaf`).

## Tests

Run in release:

```sh
cargo test -p wqc-sv-stark --release
```

Debug builds assert AIR constraints inside `prove`, so the forgery tests are ignored there.
The crate is outside the workspace's `default-members` (Plonky3-recursion builds slowly) and
has its own CI job.

//! The SNARK's relation: the verifier circuit of the wrap chain's top proof as data, a witness
//! for it, and [`check`], a reference for every constraint the SNARK enforces.
//!
//! The SNARK (wqc-snark-wrap: gnark, Groth16 over BN254) runs the top proof's verifier circuit
//! ([`crate::wrap::verifier_circuit`]) again. Every witness slot `w[i]` is a Goldilocks²
//! element (`x² = 7`), and each operation of the circuit becomes constraints:
//!
//! - `Const`: `w[out] = value`.
//! - `Public`: at the positions in [`SnarkCircuit::exposed`] (the top statement, i.e. the
//!   digest, and the top layer's preprocessed commitment), `w[out]` is the SNARK's public input:
//!   a base-field element, so `w[out].1 = 0`. Every other public input of the circuit (the top
//!   proof's commitments and openings) is private to the SNARK, and its slot is free.
//! - ALU: `add` `out = a + b`; `mul` `out = a·b`; `bool` `a·(a − 1) = 0` and `out = a`;
//!   `mul_add` `out = a·b + c`, and `w[inter] = a·b` when the fused product has a slot;
//!   `horner` `out = w[acc]·b + c − a`.
//! - Hints and private inputs: free. The circuit's soundness never relies on them, and
//!   Plonky3-recursion's AIRs leave them free too.
//! - `recompose/coeff`: `w[out] = (w[in0].0, w[in1].0)` and `w[in_i].1 = 0`.
//! - Poseidon2 rows, one stream per source table (MMCS, challenger) in table order, each stream
//!   starting a chain. A row's state `s` is 8 base elements, limb `l` being `s[2l..2l + 2]`;
//!   `o = Poseidon2(s)`. The row constraints are the Poseidon2 circuit AIR's
//!   (`p3-poseidon2-circuit-air`):
//!   - the direction bit is boolean, zero off Merkle rows, and `w[bit] = (bit, 0)` on them;
//!   - input `l` read from `w[idx]` equals limb `l` of `s`, or limb `(l + 2) mod 4` if the bit
//!     is set; output `l` (rate limbs 0 and 1) written to `w[idx]` equals limb `l` of `o`;
//!   - a sponge continuation (not `new_start`, not Merkle) takes limb `l` of the previous
//!     row's `o` for every limb read from no slot, and for the capacity limbs of a challenger
//!     row; `s[4]` adds the row's absorb length;
//!   - a Merkle continuation takes previous `o` limb `l < 2`, for each such limb read from no
//!     slot, into limb `l` if the bit is zero and limb `l + 2` if it is one;
//!   - a challenger chain start has capacity `(absorb length, 0, 0, 0)`.

use p3_circuit::ops::Poseidon2Trace;
use p3_circuit::tables::Traces;
use p3_circuit::{AluOpKind, Op, WitnessId};
use p3_field::{BasedVectorSpace, PrimeCharacteristicRing, PrimeField64};
use p3_symmetric::Permutation;
use serde::{Deserialize, Serialize};

use crate::wrap::{verifier_circuit, VerifierCircuit, Wrapped};
use crate::{Challenge, Error, F};

/// Base elements of a Poseidon2 state.
pub const WIDTH: usize = 8;

/// The operations of a top verifier circuit, as the SNARK reads them.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SnarkCircuit {
    pub witness_count: u32,
    /// Public-input positions the SNARK exposes, in order.
    pub exposed: Vec<u32>,
    /// `(out, value)`.
    pub consts: Vec<(u32, [u64; 2])>,
    /// `(out, position)`.
    pub publics: Vec<(u32, u32)>,
    pub alu: Vec<AluRow>,
    /// `([in0, in1], out)`.
    pub recompose: Vec<([u32; 2], u32)>,
    /// One stream per Poseidon2 source table.
    pub poseidon2: Vec<Vec<Poseidon2Row>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum AluKind {
    Add,
    Mul,
    Bool,
    MulAdd,
    Horner,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AluRow {
    pub kind: AluKind,
    pub a: u32,
    pub b: u32,
    pub c: Option<u32>,
    pub out: u32,
    /// `mul_add`: the fused product's slot, if any. `horner`: the accumulator.
    pub inter: Option<u32>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Poseidon2Row {
    pub new_start: bool,
    pub merkle: bool,
    pub challenger: bool,
    pub absorb: u8,
    /// Slot each input limb is read from.
    pub inputs: [Option<u32>; 4],
    /// Slot each rate output limb is written to.
    pub outputs: [Option<u32>; 2],
    /// Slot of the direction bit (Merkle rows).
    pub bit: Option<u32>,
}

/// One run of the circuit: every slot, and each Poseidon2 row's input state and direction bit.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SnarkWitness {
    pub w: Vec<[u64; 2]>,
    pub poseidon2_inputs: Vec<Vec<[u64; WIDTH]>>,
    pub poseidon2_bits: Vec<Vec<bool>>,
}

fn coords(v: &Challenge) -> [u64; 2] {
    let c: &[F] = v.as_basis_coefficients_slice();
    [c[0].as_canonical_u64(), c[1].as_canonical_u64()]
}

fn ext(v: [u64; 2]) -> Challenge {
    Challenge::from_basis_coefficients_fn(|i| F::from_u64(v[i]))
}

fn id(w: WitnessId) -> u32 {
    w.0
}

fn streams(traces: &Traces<Challenge>) -> Vec<&Poseidon2Trace<F>> {
    let mut ids: Vec<_> = traces.non_primitive_traces.keys().collect();
    ids.sort_by(|a, b| a.as_str().cmp(b.as_str()));
    ids.into_iter()
        .filter_map(|id| traces.non_primitive_trace::<Poseidon2Trace<F>>(id))
        .collect()
}

fn limbs<T: Clone>(v: &[T], n: usize) -> Result<Vec<T>, Error> {
    if v.len() != n {
        return Err(Error::Recursion(format!("{} limbs, expected {n}", v.len())));
    }
    Ok(v.to_vec())
}

impl SnarkCircuit {
    /// The circuit of `vc`; `traces` (any run of it) gives the Poseidon2 rows' static columns,
    /// which the circuit alone fixes.
    pub fn new(vc: &VerifierCircuit, traces: &Traces<Challenge>) -> Result<Self, Error> {
        let mut c = Self {
            witness_count: vc.circuit.witness_count,
            exposed: vc
                .table_publics
                .clone()
                .chain(vc.commitment.clone())
                .map(|p| p as u32)
                .collect(),
            consts: Vec::new(),
            publics: Vec::new(),
            alu: Vec::new(),
            recompose: Vec::new(),
            poseidon2: Vec::new(),
        };
        for op in &vc.circuit.ops {
            match op {
                Op::Const { out, val } => c.consts.push((id(*out), coords(val))),
                Op::Public { out, public_pos } => c.publics.push((id(*out), *public_pos as u32)),
                Op::Alu {
                    kind,
                    a,
                    b,
                    c: cc,
                    out,
                    intermediate_out,
                } => c.alu.push(AluRow {
                    kind: match kind {
                        AluOpKind::Add => AluKind::Add,
                        AluOpKind::Mul => AluKind::Mul,
                        AluOpKind::BoolCheck => AluKind::Bool,
                        AluOpKind::MulAdd => AluKind::MulAdd,
                        AluOpKind::HornerAcc => AluKind::Horner,
                    },
                    a: id(*a),
                    b: id(*b),
                    c: cc.map(id),
                    out: id(*out),
                    inter: intermediate_out.map(id),
                }),
                Op::Hint { .. } => {}
                Op::NonPrimitiveOpWithExecutor {
                    inputs,
                    outputs,
                    executor,
                    ..
                } => {
                    let ty = executor.op_type().as_str();
                    if ty == "recompose/coeff" {
                        let ins = limbs(&inputs[..], 1)?;
                        let ins = limbs(&ins[0], 2)?;
                        let out = limbs(&outputs[..], 1)?;
                        let out = limbs(&out[0], 1)?;
                        c.recompose.push(([id(ins[0]), id(ins[1])], id(out[0])));
                    } else if !ty.starts_with("poseidon2_perm/") {
                        return Err(Error::Recursion(format!("unsupported operation {ty}")));
                    }
                }
            }
        }
        for s in streams(traces) {
            let mut rows = Vec::with_capacity(s.operations.len());
            for r in &s.operations {
                let inputs = limbs(&r.in_ctl, 4)?;
                let input_idx = limbs(&r.input_indices, 4)?;
                let outputs = limbs(&r.out_ctl, 2)?;
                let output_idx = limbs(&r.output_indices, 2)?;
                rows.push(Poseidon2Row {
                    new_start: r.new_start,
                    merkle: r.merkle_path,
                    challenger: r.challenger || s.op_type.as_str().ends_with("_challenger"),
                    absorb: r.absorb_len as u8,
                    inputs: core::array::from_fn(|l| inputs[l].then_some(input_idx[l])),
                    outputs: core::array::from_fn(|l| outputs[l].then_some(output_idx[l])),
                    bit: r.merkle_path.then_some(r.mmcs_bit_idx),
                });
            }
            c.poseidon2.push(rows);
        }
        Ok(c)
    }
}

impl SnarkWitness {
    pub fn new(vc: &VerifierCircuit, traces: &Traces<Challenge>) -> Result<Self, Error> {
        let w = (0..vc.circuit.witness_count)
            .map(|i| {
                traces
                    .witness_trace
                    .get_value(WitnessId(i))
                    .map_or([0, 0], coords)
            })
            .collect();
        let mut poseidon2_inputs = Vec::new();
        let mut poseidon2_bits = Vec::new();
        for s in streams(traces) {
            let mut ins = Vec::with_capacity(s.operations.len());
            for r in &s.operations {
                let v = limbs(&r.input_values, WIDTH)?;
                ins.push(core::array::from_fn(|i| v[i].as_canonical_u64()));
            }
            poseidon2_inputs.push(ins);
            poseidon2_bits.push(s.operations.iter().map(|r| r.mmcs_bit).collect());
        }
        Ok(Self {
            w,
            poseidon2_inputs,
            poseidon2_bits,
        })
    }

    /// The SNARK's public inputs: the base value at each exposed position.
    pub fn exposed(&self, c: &SnarkCircuit) -> Vec<u64> {
        c.exposed
            .iter()
            .map(|&pos| {
                let (out, _) = c.publics.iter().find(|(_, p)| *p == pos).expect("exposed");
                self.w[*out as usize][0]
            })
            .collect()
    }
}

fn fail(m: String) -> Error {
    Error::Verify(m)
}

/// Checks every constraint the SNARK enforces (see the module docs) on `w` with public inputs
/// `exposed`.
pub fn check(c: &SnarkCircuit, w: &SnarkWitness, exposed: &[u64]) -> Result<(), Error> {
    let n = c.witness_count as usize;
    if w.w.len() != n {
        return Err(fail(format!("{} slots, expected {n}", w.w.len())));
    }
    let p = F::ORDER_U64;
    if w.w.iter().flatten().any(|&v| v >= p) {
        return Err(fail("a slot is not canonical".into()));
    }
    let at = |i: u32| ext(w.w[i as usize]);
    let eq = |what: &str, i: u32, v: Challenge| {
        if at(i) == v {
            Ok(())
        } else {
            Err(fail(format!("{what}: slot {i}")))
        }
    };
    for &(out, v) in &c.consts {
        eq("const", out, ext(v))?;
    }
    if exposed.len() != c.exposed.len() {
        return Err(fail("exposed input count".into()));
    }
    for (&pos, &v) in c.exposed.iter().zip(exposed) {
        for &(out, p2) in &c.publics {
            if p2 == pos {
                eq("public", out, ext([v, 0]))?;
            }
        }
    }
    for r in &c.alu {
        let (a, b) = (at(r.a), at(r.b));
        let cc = || r.c.map(at).ok_or_else(|| fail("alu without c".into()));
        match r.kind {
            AluKind::Add => eq("add", r.out, a + b)?,
            AluKind::Mul => eq("mul", r.out, a * b)?,
            AluKind::Bool => {
                if a * (a - Challenge::ONE) != Challenge::ZERO {
                    return Err(fail(format!("bool: slot {}", r.a)));
                }
                eq("bool out", r.out, a)?;
            }
            AluKind::MulAdd => {
                eq("mul_add", r.out, a * b + cc()?)?;
                if let Some(i) = r.inter {
                    eq("mul_add product", i, a * b)?;
                }
            }
            AluKind::Horner => {
                let acc = r
                    .inter
                    .ok_or_else(|| fail("horner without accumulator".into()))?;
                eq("horner", r.out, at(acc) * b + cc()? - a)?;
            }
        }
    }
    for &(ins, out) in &c.recompose {
        for i in ins {
            if w.w[i as usize][1] != 0 {
                return Err(fail(format!("recompose coefficient: slot {i}")));
            }
        }
        eq(
            "recompose",
            out,
            ext([w.w[ins[0] as usize][0], w.w[ins[1] as usize][0]]),
        )?;
    }
    let perm = p3_recursion::builtin_config::fixed_goldilocks_poseidon2_8();
    if w.poseidon2_inputs.len() != c.poseidon2.len() || w.poseidon2_bits.len() != c.poseidon2.len()
    {
        return Err(fail("poseidon2 stream count".into()));
    }
    for (si, rows) in c.poseidon2.iter().enumerate() {
        let (ins, bits) = (&w.poseidon2_inputs[si], &w.poseidon2_bits[si]);
        if ins.len() != rows.len() || bits.len() != rows.len() {
            return Err(fail(format!("poseidon2 stream {si} length")));
        }
        let mut prev: Option<[F; WIDTH]> = None;
        for (ri, r) in rows.iter().enumerate() {
            let here = |m: &str| fail(format!("poseidon2 {si}/{ri}: {m}"));
            let s: [F; WIDTH] = core::array::from_fn(|i| F::from_u64(ins[ri][i]));
            if ins[ri].iter().any(|&v| v >= p) {
                return Err(here("input not canonical"));
            }
            let mut o = s;
            perm.permute_mut(&mut o);
            let bit = bits[ri];
            let limb = |st: &[F; WIDTH], l: usize| {
                ext([
                    st[2 * l].as_canonical_u64(),
                    st[2 * l + 1].as_canonical_u64(),
                ])
            };
            if !r.merkle && bit {
                return Err(here("bit off a Merkle row"));
            }
            if r.merkle {
                let b = r.bit.ok_or_else(|| here("Merkle row without bit slot"))?;
                if w.w[b as usize] != [u64::from(bit), 0] {
                    return Err(here("bit slot"));
                }
            }
            for l in 0..4 {
                if let Some(i) = r.inputs[l] {
                    let src = if bit { (l + 2) % 4 } else { l };
                    if at(i) != limb(&s, src) {
                        return Err(here(&format!("input limb {l}")));
                    }
                }
            }
            for l in 0..2 {
                if let Some(i) = r.outputs[l] {
                    if at(i) != limb(&o, l) {
                        return Err(here(&format!("output limb {l}")));
                    }
                }
            }
            if let (false, Some(po)) = (r.new_start, prev) {
                if !r.merkle {
                    for l in 0..4 {
                        if (r.challenger && l >= 2) || r.inputs[l].is_none() {
                            let mut want = [po[2 * l], po[2 * l + 1]];
                            if l == 2 {
                                want[0] += F::from_u8(r.absorb);
                            }
                            if [s[2 * l], s[2 * l + 1]] != want {
                                return Err(here(&format!("sponge chain limb {l}")));
                            }
                        }
                    }
                } else {
                    for l in 0..2 {
                        if r.inputs[l].is_none() {
                            let dst = if bit { l + 2 } else { l };
                            if [s[2 * dst], s[2 * dst + 1]] != [po[2 * l], po[2 * l + 1]] {
                                return Err(here(&format!("Merkle chain limb {l}")));
                            }
                        }
                    }
                }
            }
            if r.challenger && r.new_start {
                let want = [F::from_u8(r.absorb), F::ZERO, F::ZERO, F::ZERO];
                if s[4..] != want {
                    return Err(here("challenger chain start"));
                }
            }
            if !r.new_start && prev.is_none() {
                return Err(here("stream does not start a chain"));
            }
            prev = Some(o);
        }
    }
    Ok(())
}

/// The SNARK's circuit and witness for a wrap top.
pub fn snark_inputs(top: &Wrapped) -> Result<(SnarkCircuit, SnarkWitness), Error> {
    let vc = verifier_circuit(&top.verifier, &top.proof)?;
    let traces = vc.run(&top.verifier, &top.proof)?;
    Ok((
        SnarkCircuit::new(&vc, &traces)?,
        SnarkWitness::new(&vc, &traces)?,
    ))
}

/// Round constants of the Poseidon2 permutation the recursion uses (Plonky3-recursion's
/// `fixed_goldilocks_poseidon2_8`: drawn from Xoshiro256++ seeded with 1, in this order).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Poseidon2Constants {
    pub initial: Vec<[u64; WIDTH]>,
    pub internal: Vec<u64>,
    pub terminal: Vec<[u64; WIDTH]>,
    pub diag: [u64; WIDTH],
}

pub fn poseidon2_constants() -> Poseidon2Constants {
    use rand::distr::StandardUniform;
    use rand::{RngExt, SeedableRng};
    let mut rng = rand::rngs::Xoshiro256PlusPlus::seed_from_u64(1);
    let mut rounds = |n: usize| -> Vec<[u64; WIDTH]> {
        (&mut rng)
            .sample_iter::<[F; WIDTH], _>(StandardUniform)
            .take(n)
            .map(|r| r.map(|v| v.as_canonical_u64()))
            .collect()
    };
    let initial = rounds(4);
    let terminal = rounds(4);
    let internal = (&mut rng)
        .sample_iter::<F, _>(StandardUniform)
        .take(22)
        .map(|v| v.as_canonical_u64())
        .collect();
    Poseidon2Constants {
        initial,
        internal,
        terminal,
        diag: p3_goldilocks::MATRIX_DIAG_8_GOLDILOCKS.map(|v| v.as_canonical_u64()),
    }
}

/// The permutation written out step by step, as the SNARK computes it: the external linear
/// layer applies `M4 = [[2,3,1,1],[1,2,3,1],[1,1,2,3],[3,1,1,2]]` to each half and adds the
/// two halves' sum to each; an external round adds constants, raises every element to the 7th
/// power and applies the layer; an internal round adds a constant to `s[0]`, raises it to the
/// 7th power, and sets `s[i] = diag[i]·s[i] + Σ s`. Order: layer, 4 external, 22 internal, 4
/// external.
pub fn poseidon2_reference(c: &Poseidon2Constants, state: &mut [F; WIDTH]) {
    fn m4(x: &mut [F]) {
        let [a, b, cc, d] = [x[0], x[1], x[2], x[3]];
        let two = F::TWO;
        let three = F::from_u8(3);
        x[0] = two * a + three * b + cc + d;
        x[1] = a + two * b + three * cc + d;
        x[2] = a + b + two * cc + three * d;
        x[3] = three * a + b + cc + two * d;
    }
    fn external(s: &mut [F; WIDTH]) {
        m4(&mut s[..4]);
        m4(&mut s[4..]);
        for i in 0..4 {
            let sum = s[i] + s[i + 4];
            s[i] += sum;
            s[i + 4] += sum;
        }
    }
    fn sbox(x: F) -> F {
        let x2 = x * x;
        let x3 = x2 * x;
        x3 * x3 * x
    }
    let full = |s: &mut [F; WIDTH], rc: &[u64; WIDTH]| {
        for i in 0..WIDTH {
            s[i] = sbox(s[i] + F::from_u64(rc[i]));
        }
        external(s);
    };
    external(state);
    for rc in &c.initial {
        full(state, rc);
    }
    for &rc in &c.internal {
        state[0] = sbox(state[0] + F::from_u64(rc));
        let sum: F = state.iter().copied().sum();
        for (v, &d) in state.iter_mut().zip(&c.diag) {
            *v = *v * F::from_u64(d) + sum;
        }
    }
    for rc in &c.terminal {
        full(state, rc);
    }
}

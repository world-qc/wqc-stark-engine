//! The JSON wqc-core and the orchestrator exchange, read the same way by the prover (wqc-core)
//! and the verifier (the orchestrator, through the FFI), so both derive the same circuit and
//! counts.
//!
//! - Circuit: wqc-core's gate list, `[{"type":"H","params":0}, {"type":"CNOT","params":[0,1]},
//!   {"type":"RZ","params":[0,0.5]}, …]`, optionally ending in terminal measurements
//!   `{"type":"MEASURE","params":{"qubit":0,"cbit":0}}`. [`parse_circuit`] reads only that
//!   form; [`parse_leaf`] also reads mid-circuit measurements, RESET and IF, rewriting them
//!   into unitary gates and terminal measurements (see there).
//! - Counts: `{"counts":{"01":3,…},"shots":N}`, keys of `cbits` characters in Qiskit order
//!   (cbit 0 rightmost), as wqc-core and the orchestrator marshal a `SampleResult`.

use std::collections::BTreeMap;

use serde::Deserialize;

use crate::born::{Measure, Sampling};
use crate::exec::Gate;
use crate::Error;

#[derive(Deserialize)]
struct MeasureParams {
    qubit: usize,
    cbit: usize,
}

/// wqc-core's `Gate`, as serde tags it.
#[derive(Deserialize)]
#[serde(tag = "type", content = "params")]
#[allow(clippy::upper_case_acronyms)]
enum WireGate {
    H(usize),
    X(usize),
    Y(usize),
    Z(usize),
    T(usize),
    S(usize),
    CNOT(usize, usize),
    CZ(usize, usize),
    RX(usize, f64),
    RY(usize, f64),
    RZ(usize, f64),
    CCNOT(usize, usize, usize),
    MEASURE(MeasureParams),
    RESET(usize),
    IF(IfParams),
}

#[derive(Deserialize)]
struct IfParams {
    cbit: usize,
    value: u8,
    gate: Box<WireGate>,
}

impl WireGate {
    /// The unitary gate, or `None` for MEASURE, RESET and IF.
    fn unitary(&self) -> Option<Gate> {
        Some(match *self {
            WireGate::H(t) => Gate::h(t),
            WireGate::X(t) => Gate::x(t),
            WireGate::Y(t) => Gate::y(t),
            WireGate::Z(t) => Gate::z(t),
            WireGate::T(t) => Gate::t(t),
            WireGate::S(t) => Gate::s(t),
            WireGate::CNOT(c, t) => Gate::cnot(c, t),
            WireGate::CZ(c, t) => Gate::cz(c, t),
            WireGate::RX(t, a) => Gate::rx(t, a),
            WireGate::RY(t, a) => Gate::ry(t, a),
            WireGate::RZ(t, a) => Gate::rz(t, a),
            WireGate::CCNOT(c1, c2, t) => Gate::ccnot(c1, c2, t),
            WireGate::MEASURE(_) | WireGate::RESET(_) | WireGate::IF(_) => return None,
        })
    }
}

/// A circuit read from the wire: the unitary gates and the terminal measurements.
#[derive(Clone, Debug)]
pub struct Circuit {
    pub gates: Vec<Gate>,
    pub measures: Vec<Measure>,
}

/// A circuit as a leaf proves it ([`parse_leaf`]): on `qubits` qubits, the register's plus one
/// ancilla per RESET that needs one.
#[derive(Clone, Debug)]
pub struct LeafCircuit {
    pub qubits: usize,
    pub gates: Vec<Gate>,
    pub measures: Vec<Measure>,
}

fn invalid(m: impl Into<String>) -> Error {
    Error::InvalidCircuit(m.into())
}

/// Reads a wqc-core gate list. Every MEASURE must come after every unitary gate. Wiring and
/// matrices are checked later, by [`crate::leaf::build`] and [`crate::leaf::gate_rows`].
pub fn parse_circuit(json: &str) -> Result<Circuit, Error> {
    let wire: Vec<WireGate> =
        serde_json::from_str(json).map_err(|e| invalid(format!("circuit JSON: {e}")))?;
    terminal(wire)
}

fn terminal(wire: Vec<WireGate>) -> Result<Circuit, Error> {
    let mut gates = Vec::new();
    let mut measures = Vec::new();
    for (k, g) in wire.into_iter().enumerate() {
        let gate = match g {
            WireGate::MEASURE(m) => {
                measures.push(Measure {
                    qubit: m.qubit,
                    cbit: m.cbit,
                });
                continue;
            }
            WireGate::RESET(_) | WireGate::IF(_) => {
                return Err(invalid(format!("gate {k}: RESET and IF need parse_leaf")))
            }
            _ if !measures.is_empty() => {
                return Err(invalid(format!(
                    "gate {k}: a unitary gate after a MEASURE needs parse_leaf"
                )))
            }
            g => g.unitary().expect("a unitary gate"),
        };
        gates.push(gate);
    }
    Ok(Circuit { gates, measures })
}

/// Reads a wqc-core gate list on `n` qubits as the circuit a leaf proves.
///
/// A circuit whose MEASUREs all come after its unitary gates, with no RESET or IF, is read as
/// [`parse_circuit`] reads it, on `n` qubits. Any other circuit (mid-circuit semantics) is
/// rewritten by deferring its measurements, which gives the same distribution of the classical
/// register:
///
/// - `MEASURE q → c` emits nothing; `c` now holds what `q` holds.
/// - `IF(c == v) U` emits `U` with one more control, the qubit holding `c`, between two X on
///   that qubit when `v == 0`. If `c` was never measured it is 0: `U` is emitted as is when
///   `v == 0`, and nothing when `v == 1`. `U` is a one-qubit gate, CNOT or CZ, so a controlled
///   `U` has at most two controls.
/// - `RESET q` emits nothing when `q` is fresh (no gate, MEASURE or IF has touched it since the
///   start or its last RESET), since it is still `|0⟩`. Otherwise it swaps `q` with a new
///   ancilla in `|0⟩` (`CNOT(q, a)`, `CNOT(a, q)`); `q` is `|0⟩` again and every cbit `q` held
///   is now held by `a`. No gate targets `a` again; it can only be the control an IF on one of
///   those cbits adds.
/// - At the end, each cbit that was measured is measured from the qubit that holds it, in cbit
///   order. Values that were overwritten or left on an ancilla are not measured.
///
/// Deferring is exact because, as wqc-core requires, no gate touches a measured qubit until it
/// is RESET: its value stays frozen in the Z basis, so measuring it later, or using it as a
/// quantum control, gives what measuring it then and controlling classically would. An
/// ancilla that is never measured is traced out, which is what RESET does to the old value.
///
/// It rejects a gate (or an IF's gate) on a measured qubit before its RESET, an IF value other
/// than 0 or 1, an IF whose gate is a MEASURE, RESET, IF or CCNOT, and qubits outside `n`.
/// Ancillas are numbered from `n`; [`crate::leaf::build`] bounds the total.
pub fn parse_leaf(json: &str, n: usize) -> Result<LeafCircuit, Error> {
    let wire: Vec<WireGate> =
        serde_json::from_str(json).map_err(|e| invalid(format!("circuit JSON: {e}")))?;
    if !is_dynamic(&wire) {
        let c = terminal(wire)?;
        return Ok(LeafCircuit {
            qubits: n,
            gates: c.gates,
            measures: c.measures,
        });
    }
    let mut d = Deferred {
        n,
        qubits: n,
        gates: Vec::new(),
        fresh: vec![true; n],
        measured: vec![false; n],
        holder: BTreeMap::new(),
    };
    for (k, g) in wire.iter().enumerate() {
        d.apply(g).map_err(|m| invalid(format!("gate {k}: {m}")))?;
    }
    let measures = d
        .holder
        .iter()
        .map(|(&cbit, &qubit)| Measure { qubit, cbit })
        .collect();
    Ok(LeafCircuit {
        qubits: d.qubits,
        gates: d.gates,
        measures,
    })
}

/// Whether the circuit has a RESET, an IF, or a unitary gate after a MEASURE.
fn is_dynamic(wire: &[WireGate]) -> bool {
    let mut measured = false;
    for g in wire {
        match g {
            WireGate::RESET(_) | WireGate::IF(_) => return true,
            WireGate::MEASURE(_) => measured = true,
            _ if measured => return true,
            _ => {}
        }
    }
    false
}

/// The state of [`parse_leaf`]'s rewriting.
struct Deferred {
    /// The register's qubits.
    n: usize,
    /// Register plus ancillas so far.
    qubits: usize,
    gates: Vec<Gate>,
    fresh: Vec<bool>,
    measured: Vec<bool>,
    /// cbit → the qubit (or ancilla) holding its last measurement.
    holder: BTreeMap<usize, usize>,
}

impl Deferred {
    fn qubit(&self, q: usize) -> Result<usize, String> {
        if q < self.n {
            Ok(q)
        } else {
            Err(format!("qubit {q} with {} qubits", self.n))
        }
    }

    /// Checks a unitary gate's qubits and marks them touched.
    fn touch(&mut self, g: &Gate) -> Result<(), String> {
        for &q in g.controls().iter().chain([g.target()].iter()) {
            let q = self.qubit(q)?;
            if self.measured[q] {
                return Err(format!(
                    "qubit {q} is used after its MEASURE without a RESET"
                ));
            }
            self.fresh[q] = false;
        }
        Ok(())
    }

    fn apply(&mut self, g: &WireGate) -> Result<(), String> {
        match g {
            WireGate::MEASURE(m) => {
                let q = self.qubit(m.qubit)?;
                self.fresh[q] = false;
                self.measured[q] = true;
                self.holder.insert(m.cbit, q);
            }
            WireGate::RESET(q) => {
                let q = self.qubit(*q)?;
                // Deliberately conservative: a qubit counts as used once anything names it,
                // even as a control that left it in |0⟩, so such a RESET still takes an
                // ancilla. Proving a qubit is still |0⟩ would need the state, and the rule is
                // part of the leaf format, so it stays this simple.
                if !self.fresh[q] {
                    let a = self.qubits;
                    self.qubits += 1;
                    self.gates.push(Gate::cnot(q, a));
                    self.gates.push(Gate::cnot(a, q));
                    for h in self.holder.values_mut() {
                        if *h == q {
                            *h = a;
                        }
                    }
                }
                self.fresh[q] = true;
                self.measured[q] = false;
            }
            WireGate::IF(p) => {
                if p.value > 1 {
                    return Err(format!("IF value {}", p.value));
                }
                let u = match p.gate.as_ref() {
                    WireGate::CCNOT(..) => {
                        return Err("an IF of CCNOT has no state-vector leaf".into())
                    }
                    other => other
                        .unitary()
                        .ok_or("an IF's gate must be a unitary gate")?,
                };
                self.touch(&u)?;
                match self.holder.get(&p.cbit).copied() {
                    None if p.value == 0 => self.gates.push(u),
                    None => {}
                    Some(h) => {
                        let mut cu = u;
                        cu.controls.push(h);
                        if p.value == 0 {
                            self.gates.push(Gate::x(h));
                            self.gates.push(cu);
                            self.gates.push(Gate::x(h));
                        } else {
                            self.gates.push(cu);
                        }
                    }
                }
            }
            other => {
                let u = other.unitary().expect("a unitary gate");
                self.touch(&u)?;
                self.gates.push(u);
            }
        }
        Ok(())
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct SampleResult {
    counts: BTreeMap<String, u64>,
    shots: u64,
}

/// Reads a `SampleResult` JSON into the counts vector of `sampling` (indexed by register
/// value, [`Sampling::counts_len`] entries): keys of exactly `cbits` characters `0` and `1`, no
/// zero counts, `shots` equal to the sampling's and to the sum of the counts. Only the exact
/// bytes [`counts_json`] writes are accepted (key order, no spaces, no duplicate keys), so one
/// counts vector has one JSON and one result hash. It errors if `sampling`'s `shots` or
/// `cbits` is out of range (as [`crate::leaf::build_sampling`] checks).
pub fn parse_counts(json: &str, sampling: &Sampling) -> Result<Vec<u64>, Error> {
    let bad = |m: String| Error::Verify(format!("counts JSON: {m}"));
    sampling.validate_counts()?;
    let r: SampleResult = serde_json::from_str(json).map_err(|e| bad(e.to_string()))?;
    let shots = u64::from(sampling.shots);
    if r.shots != shots {
        return Err(bad(format!("{} shots, expected {shots}", r.shots)));
    }
    let mut counts = vec![0u64; sampling.counts_len()];
    let mut sum = 0u64;
    for (key, &c) in &r.counts {
        if key.len() != sampling.cbits || !key.bytes().all(|b| b == b'0' || b == b'1') {
            return Err(bad(format!("key {key:?} is not {} bits", sampling.cbits)));
        }
        if c == 0 || c > shots {
            return Err(bad(format!("count {c} for {key}")));
        }
        // Qiskit order: the leftmost character is the highest cbit.
        let reg = usize::from_str_radix(key, 2).map_err(|e| bad(e.to_string()))?;
        counts[reg] = c;
        sum += c;
    }
    if sum != shots {
        return Err(bad(format!("counts add up to {sum}, expected {shots}")));
    }
    if counts_json(&counts, sampling.cbits) != json {
        return Err(bad("not in canonical form".into()));
    }
    Ok(counts)
}

/// The canonical `SampleResult` JSON of a counts vector: what wqc-core reports and
/// [`parse_counts`] accepts, byte for byte the orchestrator's marshaling (keys in order, no
/// spaces, zero counts omitted).
///
/// Every nonzero count must be at an index below `2^cbits` (a register of `cbits` bits).
pub fn counts_json(counts: &[u64], cbits: usize) -> String {
    debug_assert!(
        counts.iter().skip(1 << cbits).all(|&c| c == 0),
        "a nonzero count past 2^cbits"
    );
    let mut pairs = Vec::new();
    for (reg, &c) in counts.iter().enumerate() {
        if c > 0 {
            pairs.push(format!("\"{reg:0cbits$b}\":{c}"));
        }
    }
    let shots: u64 = counts.iter().sum();
    format!("{{\"counts\":{{{}}},\"shots\":{shots}}}", pairs.join(","))
}

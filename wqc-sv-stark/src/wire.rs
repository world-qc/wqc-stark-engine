//! The JSON wqc-core and the orchestrator exchange, read the same way by the prover (wqc-core)
//! and the verifier (the orchestrator, through the FFI), so both derive the same circuit and
//! counts.
//!
//! - Circuit: wqc-core's gate list, `[{"type":"H","params":0}, {"type":"CNOT","params":[0,1]},
//!   {"type":"RZ","params":[0,0.5]}, …]`, optionally ending in terminal measurements
//!   `{"type":"MEASURE","params":{"qubit":0,"cbit":0}}`. RESET, IF and mid-circuit
//!   measurements have no v2 leaf.
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
    RESET(serde::de::IgnoredAny),
    IF(serde::de::IgnoredAny),
}

/// A circuit read from the wire: the unitary gates and the terminal measurements.
#[derive(Clone, Debug)]
pub struct Circuit {
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
                return Err(invalid(format!(
                    "gate {k}: RESET and IF have no state-vector leaf"
                )))
            }
            _ if !measures.is_empty() => {
                return Err(invalid(format!(
                    "gate {k}: a unitary gate after a MEASURE has no state-vector leaf"
                )))
            }
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
        };
        gates.push(gate);
    }
    Ok(Circuit { gates, measures })
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

//! A circuit cut into segments: the cut positions, each segment's leaf, and the plan for where
//! to cut. One task's segments are leaves of one root; a segment leaf
//! ([`crate::leaf::build_segment`]) starts from the state the earlier segments reach.
//!
//! The circuit travels whole, with the cut positions and the segment's index, so every party
//! (the orchestrator, the node, the composer, a challenger) derives the same segments. Cuts are
//! indices into the circuit's unitary gates as [`parse_circuit`] reads them; only terminal
//! circuits (every MEASURE after every unitary gate) are cut.

use crate::born::{Measure, Sampling};
use crate::exec::{Gate, C};
use crate::leaf::{self, gate_rows, Leaf, LeafVerifier};
use crate::wire::parse_circuit;
use crate::{Error, SecurityLevel, MAX_QUBITS};

/// How far back from the circuit's end [`plan_tail`] looks for a cut, in gates. Any cut is
/// sound (every verifier computes the head), so the bound only trades a longer head for a
/// plan that stays linear in the circuit: each step fuses the tail again.
pub const TAIL_SCAN_GATES: usize = 1 << 13;

/// A terminal circuit cut into segments.
pub struct Segments {
    pub n: usize,
    pub segments: Vec<Vec<Gate>>,
    /// The circuit's terminal measurements: the last segment's, when the task samples.
    pub measures: Vec<Measure>,
}

impl Segments {
    /// Reads `circuit_json` (wqc-core's gate list) on `n` qubits and cuts it at `cuts`: strictly
    /// increasing, each between 1 and the gate count minus 1, so no segment is empty.
    pub fn parse(circuit_json: &str, n: usize, cuts: &[usize]) -> Result<Self, Error> {
        // Before anything allocates `2^n` amplitudes (`start`).
        if !(1..=MAX_QUBITS).contains(&n) {
            return Err(Error::InvalidCircuit(format!(
                "{n} qubits, supported 1..={MAX_QUBITS}"
            )));
        }
        let c = parse_circuit(circuit_json)?;
        if let Some(m) = c.measures.iter().find(|m| m.qubit >= n) {
            return Err(Error::InvalidCircuit(format!(
                "MEASURE of qubit {} with {n} qubits",
                m.qubit
            )));
        }
        Ok(Self {
            n,
            segments: split(c.gates, cuts)?,
            measures: c.measures,
        })
    }

    pub fn len(&self) -> usize {
        self.segments.len()
    }

    pub fn is_empty(&self) -> bool {
        self.segments.is_empty()
    }

    /// Fails unless `k` is the last segment, the tail: the only one a cut task proves
    /// ([`plan_tail`]).
    pub fn check_tail(&self, k: usize) -> Result<(), Error> {
        if k + 1 != self.len() {
            return Err(Error::InvalidCircuit(format!(
                "segment {k} of {}: only the last segment (the tail) is proved",
                self.len()
            )));
        }
        Ok(())
    }

    /// The state segment `k` starts from ([`leaf::segment_start`]).
    pub fn start(&self, k: usize) -> Result<Vec<C>, Error> {
        self.check(k)?;
        leaf::segment_start(self.n, &self.segments[..k])
    }

    /// Segment `k`'s sampling: only the last segment samples, and only when `shots > 0`
    /// (`classical_bit_count` bits); a segment before it, or `shots == 0`, has none. The last
    /// segment of a circuit with MEASUREs must sample.
    pub fn sampling(
        &self,
        k: usize,
        classical_bit_count: u32,
        shots: u64,
    ) -> Result<Option<Sampling>, Error> {
        self.check(k)?;
        let last = k + 1 == self.len();
        if !last {
            if shots > 0 {
                return Err(Error::InvalidCircuit(format!(
                    "segment {k} of {} has shots: only the last samples",
                    self.len()
                )));
            }
            return Ok(None);
        }
        if shots == 0 {
            if !self.measures.is_empty() {
                return Err(Error::InvalidCircuit(
                    "MEASURE in a circuit without shots".into(),
                ));
            }
            return Ok(None);
        }
        let shots =
            u32::try_from(shots).map_err(|_| Error::InvalidCircuit(format!("{shots} shots")))?;
        let sampling = Sampling {
            measures: self.measures.clone(),
            cbits: classical_bit_count as usize,
            shots,
        };
        sampling.validate(self.n)?;
        Ok(Some(sampling))
    }

    /// Segment `k`'s leaf, to prove or to verify a root over.
    pub fn leaf(
        &self,
        level: SecurityLevel,
        k: usize,
        classical_bit_count: u32,
        shots: u64,
    ) -> Result<Leaf, Error> {
        let sampling = self.sampling(k, classical_bit_count, shots)?;
        leaf::build_segment(
            level,
            self.n,
            self.segments[k].clone(),
            self.start(k)?,
            sampling,
        )
    }

    /// Segment `k`'s verifier, built in less memory ([`leaf::build_segment_verifier`]).
    pub fn verifier(
        &self,
        level: SecurityLevel,
        k: usize,
        classical_bit_count: u32,
        shots: u64,
    ) -> Result<LeafVerifier, Error> {
        let sampling = self.sampling(k, classical_bit_count, shots)?;
        leaf::build_segment_verifier(
            level,
            self.n,
            self.segments[k].clone(),
            Some(self.start(k)?),
            sampling,
        )
    }

    /// Segment `k`'s gate rows (`W`, [`gate_rows`]).
    pub fn rows(&self, k: usize) -> Result<usize, Error> {
        self.check(k)?;
        gate_rows(self.n, &self.segments[k])
    }

    fn check(&self, k: usize) -> Result<(), Error> {
        if k >= self.len() {
            return Err(Error::InvalidCircuit(format!(
                "segment {k} of {}",
                self.len()
            )));
        }
        Ok(())
    }
}

/// `gates` cut at `cuts` (see [`Segments::parse`]).
pub fn split(gates: Vec<Gate>, cuts: &[usize]) -> Result<Vec<Vec<Gate>>, Error> {
    let mut prev = 0;
    for &c in cuts {
        if c <= prev || c >= gates.len() {
            return Err(Error::InvalidCircuit(format!(
                "cut {c} after {prev} in {} gates",
                gates.len()
            )));
        }
        prev = c;
    }
    let mut out = Vec::with_capacity(cuts.len() + 1);
    let mut rest = gates;
    for &c in cuts.iter().rev() {
        out.push(rest.split_off(c));
    }
    out.push(rest);
    out.reverse();
    Ok(out)
}

/// Where to cut `gates` on `n` qubits so the part after the cut fits one leaf of at most
/// `max_rows` gate rows: the earliest cut whose tail fits, scanning back from the end one gate
/// at a time over at most [`TAIL_SCAN_GATES`] gates (fusion can lower the tail's rows as it
/// grows, so the earliest fitting start is kept). Returns `Some(0)` when the whole circuit
/// fits one leaf (no cut), `Some(c)` to prove gates `c..` from the state gates `..c` reach, or
/// `None` when no tail within the scan fits (the last gate alone is over `max_rows`).
///
/// Only the tail is proved: its leaf starts from the state the head reaches, which every
/// verifier computes itself ([`leaf::segment_start`]), so a proof of the head would add nothing
/// to what the tail's proof shows. The head's depth is bounded by that computation, not by a
/// leaf.
pub fn plan_tail(n: usize, gates: &[Gate], max_rows: usize) -> Result<Option<usize>, Error> {
    if gate_rows(n, gates)? <= max_rows {
        return Ok(Some(0));
    }
    let mut earliest = None;
    for c in (gates.len().saturating_sub(TAIL_SCAN_GATES)..gates.len()).rev() {
        if gate_rows(n, &gates[c..])? <= max_rows {
            earliest = Some(c);
        } else if earliest.is_some() {
            break;
        }
    }
    Ok(earliest)
}

#[cfg(test)]
mod tests {
    use super::*;

    const TWO: &str = r#"[{"type":"H","params":0},{"type":"CNOT","params":[0,1]},
        {"type":"RY","params":[1,0.7]},{"type":"T","params":0},
        {"type":"MEASURE","params":{"qubit":0,"cbit":0}},{"type":"MEASURE","params":{"qubit":1,"cbit":1}}]"#;

    #[test]
    fn cuts_split_the_unitary_gates() {
        let gates = parse_circuit(TWO).unwrap().gates;
        // `Gate` has no `PartialEq`; its debug form shows every field.
        let show = |v: &[Vec<Gate>]| format!("{v:?}");
        let segs = split(gates.clone(), &[2]).unwrap();
        assert_eq!(
            show(&segs),
            show(&[gates[..2].to_vec(), gates[2..].to_vec()])
        );
        assert_eq!(
            show(&split(gates.clone(), &[]).unwrap()),
            show(std::slice::from_ref(&gates))
        );
        for bad in [&[0][..], &[4], &[2, 2], &[3, 1]] {
            assert!(split(gates.clone(), bad).is_err(), "{bad:?}");
        }
        let s = Segments::parse(TWO, 2, &[2]).unwrap();
        assert_eq!((s.len(), s.measures.len()), (2, 2));
        assert!(
            Segments::parse(TWO, 1, &[2]).is_err(),
            "a MEASURE of qubit 1 on 1 qubit"
        );
        let mid = r#"[{"type":"MEASURE","params":{"qubit":0,"cbit":0}},{"type":"X","params":1}]"#;
        assert!(
            Segments::parse(mid, 2, &[]).is_err(),
            "mid-circuit circuits are not cut"
        );
    }

    #[test]
    fn only_the_last_segment_samples() {
        let s = Segments::parse(TWO, 2, &[2]).unwrap();
        assert!(s.sampling(0, 2, 0).unwrap().is_none());
        assert!(
            s.sampling(0, 2, 64).is_err(),
            "an earlier segment with shots"
        );
        assert_eq!(s.sampling(1, 2, 64).unwrap().unwrap().shots, 64);
        assert!(s.sampling(1, 2, 0).is_err(), "MEASURE without shots");
        assert!(s.sampling(2, 2, 64).is_err(), "no segment 2");
        assert_eq!(s.start(0).unwrap(), leaf::segment_start(2, &[]).unwrap());
        assert_eq!(
            s.start(1).unwrap(),
            leaf::segment_start(2, &s.segments[..1]).unwrap()
        );
    }

    #[test]
    fn plan_tail_cuts_where_the_tail_fits() {
        // Each RY is one rounding step of 2^(n−1) = 4 rows on 3 qubits; each CNOT folds.
        let gates: Vec<Gate> = (0..6)
            .flat_map(|k| {
                [
                    Gate::ry(k % 3, 0.3 + k as f64),
                    Gate::cnot(k % 3, (k + 1) % 3),
                ]
            })
            .collect();
        assert_eq!(gate_rows(3, &gates).unwrap(), 24);
        assert_eq!(plan_tail(3, &gates, 24).unwrap(), Some(0), "fits one leaf");
        let c = plan_tail(3, &gates, 8).unwrap().unwrap();
        assert_eq!(
            gate_rows(3, &gates[c..]).unwrap(),
            8,
            "the tail holds two steps"
        );
        assert!(
            gate_rows(3, &gates[c - 1..]).unwrap() > 8,
            "the earliest fitting cut"
        );
        assert_eq!(
            plan_tail(3, &gates, 2).unwrap(),
            Some(11),
            "only the last CNOT, which folds, fits"
        );
        assert_eq!(
            plan_tail(3, &gates[..11], 2).unwrap(),
            None,
            "the last gate is over the limit"
        );
    }

    #[test]
    fn plan_tail_scans_a_bounded_tail() {
        // Rounding steps, then more folding gates than the scan covers: the tail found is the
        // scanned window, all of it fitting, and the plan stays fast.
        let mut gates: Vec<Gate> = (0..32).map(|k| Gate::ry(k % 3, 0.3 + k as f64)).collect();
        gates.extend((0..TAIL_SCAN_GATES + 100).map(|k| Gate::x(k % 3)));
        let c = plan_tail(3, &gates, 8).unwrap().unwrap();
        assert_eq!(c, gates.len() - TAIL_SCAN_GATES);
        assert_eq!(gate_rows(3, &gates[c..]).unwrap(), 0);
    }

    #[test]
    fn parse_checks_the_qubit_count_and_the_tail() {
        for n in [0, MAX_QUBITS + 1, 40] {
            assert!(Segments::parse(TWO, n, &[2]).is_err(), "{n} qubits");
        }
        let s = Segments::parse(TWO, 2, &[2]).unwrap();
        assert!(s.check_tail(1).is_ok());
        assert!(s.check_tail(0).is_err() && s.check_tail(2).is_err());
    }
}

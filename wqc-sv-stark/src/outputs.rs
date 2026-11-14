//! `statevector_scalar` and `expectation` results from a published final state.
//!
//! A unitary leaf proves the final state's digest, not the values a task reports. The node
//! publishes the final integer state with its proof; a verifier checks that the state hashes
//! to the proved digest ([`check_state`]) and computes the values itself. Every party uses
//! these functions, so a value is bit-identical wherever it is computed.
//!
//! - State bytes: the `2^n` logical amplitudes in index order, each as `re` then `im`, `i64`
//!   little-endian, in units of `2^-28` ([`crate::exec::S`]): 16 bytes per amplitude, 1 MiB at
//!   n = 16.
//! - Values are rounded onto wqc-core's published grid (`1e-6`, half away from zero), as every
//!   `ComplexResult` is before it is hashed or compared.

use crate::digest::terminal_digest;
use crate::exec::{C, S};
use crate::{Error, MAX_QUBITS};

/// wqc-core's `AMPLITUDE_GRID`: published results are multiples of it.
pub const GRID: f64 = 1e-6;

/// `x` on the published grid: `round(x · 1e6) / 1e6`, half away from zero (Go `math.Round`).
pub fn snap(x: f64) -> f64 {
    (x * 1e6).round() / 1e6
}

/// The state's bytes (see the module docs).
pub fn encode_state(fin: &[C]) -> Vec<u8> {
    let mut out = Vec::with_capacity(fin.len() * 16);
    for &(re, im) in fin {
        out.extend_from_slice(&re.to_le_bytes());
        out.extend_from_slice(&im.to_le_bytes());
    }
    out
}

/// Reads a state of `n` qubits from its bytes; the length must be exactly `16 · 2^n`.
pub fn decode_state(bytes: &[u8], n: usize) -> Result<Vec<C>, Error> {
    if !(1..=MAX_QUBITS).contains(&n) {
        return Err(Error::Verify(format!(
            "{n} qubits, supported 1..={MAX_QUBITS}"
        )));
    }
    let want = 16usize << n;
    if bytes.len() != want {
        return Err(Error::Verify(format!(
            "state has {} bytes, {want} expected for {n} qubits",
            bytes.len()
        )));
    }
    let word = |k: usize| i64::from_le_bytes(bytes[k..k + 8].try_into().expect("8 bytes"));
    Ok((0..1usize << n)
        .map(|i| (word(16 * i), word(16 * i + 8)))
        .collect())
}

/// Reads the state and checks it hashes to `digest`, the digest the leaf proof binds.
pub fn check_state(bytes: &[u8], n: usize, digest: [u64; 4]) -> Result<Vec<C>, Error> {
    let fin = decode_state(bytes, n)?;
    if terminal_digest(&fin) != digest {
        return Err(Error::Verify(
            "state does not hash to the proved digest".into(),
        ));
    }
    Ok(fin)
}

/// `statevector_scalar`: the amplitude of `|0…0⟩`, on the published grid.
pub fn amplitude_zero(fin: &[C]) -> (f64, f64) {
    let (re, im) = fin[0];
    (snap(re as f64 / S as f64), snap(im as f64 / S as f64))
}

/// `⟨ψ|P|ψ⟩` for a Pauli string `P` over `n` qubits, in Qiskit order (the rightmost character
/// is qubit 0): with `P|i⟩ = phase_i |P(i)⟩`, the real part of
/// `Σ_i conj(ψ_{P(i)}) · phase_i · ψ_i`, as wqc-core's `pauli_string_expectation`. Summed
/// exactly in integers, then scaled once.
pub fn pauli_expectation(fin: &[C], n: usize, label: &str) -> Result<f64, Error> {
    let bytes = label.as_bytes();
    if bytes.len() != n || fin.len() != 1usize << n {
        return Err(Error::Verify(format!(
            "pauli label {label:?} on {n} qubits with {} amplitudes",
            fin.len()
        )));
    }
    let mut flip = 0usize;
    for (q, &ch) in bytes.iter().rev().enumerate() {
        match ch {
            b'I' | b'Z' => {}
            b'X' | b'Y' => flip |= 1 << q,
            _ => {
                return Err(Error::Verify(format!(
                    "invalid pauli character in {label:?}"
                )))
            }
        }
    }
    let mut sum: i128 = 0;
    for (i, &(ar, ai)) in fin.iter().enumerate() {
        // phase = i^k · (−1)^m for the bits of i, as core multiplies them in.
        let mut k = 0u32; // powers of i
        let mut neg = false;
        for (q, &ch) in bytes.iter().rev().enumerate() {
            let bit = (i >> q) & 1;
            match ch {
                b'Z' if bit == 1 => neg = !neg,
                // Y|0⟩ = i|1⟩, Y|1⟩ = −i|0⟩
                b'Y' => {
                    k += 1;
                    if bit == 1 {
                        neg = !neg;
                    }
                }
                _ => {}
            }
        }
        let (br, bi) = fin[i ^ flip];
        // conj(b) · a
        let (pr, pi) = (
            br as i128 * ar as i128 + bi as i128 * ai as i128,
            br as i128 * ai as i128 - bi as i128 * ar as i128,
        );
        // · i^k, real part only
        let re = match k % 4 {
            0 => pr,
            1 => -pi,
            2 => -pr,
            _ => pi,
        };
        sum += if neg { -re } else { re };
    }
    Ok(sum as f64 / (S as f64 * S as f64))
}

/// One term of an observable: a Pauli string and its complex coefficient.
#[derive(Clone, Debug, PartialEq, serde::Deserialize)]
pub struct PauliTerm {
    pub label: String,
    pub coeff: Coeff,
}

#[derive(Clone, Copy, Debug, PartialEq, serde::Deserialize)]
pub struct Coeff {
    pub real: f64,
    pub imag: f64,
}

/// `Σ coeff_k · ⟨ψ|P_k|ψ⟩` in term order, accumulated as wqc-core does, on the published grid.
pub fn observable(fin: &[C], n: usize, terms: &[PauliTerm]) -> Result<(f64, f64), Error> {
    if terms.is_empty() {
        return Err(Error::Verify("observable with no terms".into()));
    }
    let (mut real, mut imag) = (0.0f64, 0.0f64);
    for t in terms {
        let e = pauli_expectation(fin, n, &t.label)?;
        real += t.coeff.real * e;
        imag += t.coeff.imag * e;
    }
    Ok((snap(real), snap(imag)))
}

/// Reads an observable's terms from wqc-core's JSON (`[{"label":"ZZ","coeff":{"real":1,"imag":0}}]`).
pub fn parse_terms(json: &str) -> Result<Vec<PauliTerm>, Error> {
    serde_json::from_str(json).map_err(|e| Error::Verify(format!("observable terms JSON: {e}")))
}

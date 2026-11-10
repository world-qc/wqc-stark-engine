//! Terminal Z measurement and seeded sampling (`sample_counts`), defined in integers so the
//! leaf can prove it.
//!
//! - Weights: `p_b = re_b² + im_b²` of the final logical amplitudes (units of `S²`), and their
//!   running sums `C_b = p_0 + … + p_b`; the total `T = C_{2^n−1}` is about `2^56`.
//! - Draws: draw `j` is `u_j = r_j mod 2^57`, where `r_j` is word `j mod 4` of the Poseidon2
//!   permutation of `[seed_lo, seed_hi, j / 4, 0, PRF_TAG, 0, 0, 0]` (the leaf's Poseidon2), as a
//!   canonical `u64`.
//! - Choice: a draw with `u_j ≥ T` is rejected; otherwise it picks the basis state `b` with
//!   `C_{b−1} ≤ u_j < C_b`, whose outcome is the classical register the measurements give it.
//!   Draws continue until `shots` are accepted, so each shot picks `b` with probability `p_b / T`.
//! - Counts: one per classical register value; their digest is a Poseidon2 sponge over the
//!   counts (four per block, at least one block), like the state digest.

use std::borrow::Borrow;

use crate::digest::*;
use crate::exec::*;
use crate::F;
use p3_field::{PrimeCharacteristicRing, PrimeField64};

/// Draws are reduced to this many bits; `T` stays below `2^57`, so about half are accepted.
pub const U_BITS: u32 = 57;
/// Domain tag in the capacity of the sampling permutation's input.
pub const PRF_TAG: u64 = 0x5052_4631;
pub const MAX_SHOTS: u32 = 1 << 16;
pub const MAX_CBITS: usize = 16;

/// Measure `qubit` into classical bit `cbit` at the end of the circuit.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Measure {
    pub qubit: usize,
    pub cbit: usize,
}

/// A `sample_counts` request: the terminal measurements, the classical register size and the
/// number of shots.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Sampling {
    pub measures: Vec<Measure>,
    pub cbits: usize,
    pub shots: u32,
}

impl Sampling {
    pub(crate) fn validate(&self, n: usize) -> Result<(), crate::Error> {
        self.validate_counts()?;
        let bad = |m: String| Err(crate::Error::InvalidCircuit(m));
        if self.measures.is_empty() {
            return bad("sampling without a MEASURE".into());
        }
        for m in &self.measures {
            if m.qubit >= n || m.cbit >= self.cbits {
                return bad(format!(
                    "measure qubit {} into cbit {} with {n} qubits and {} cbits",
                    m.qubit, m.cbit, self.cbits
                ));
            }
        }
        Ok(())
    }

    /// The limits on `shots` and `cbits`, which bound the counts vector.
    pub(crate) fn validate_counts(&self) -> Result<(), crate::Error> {
        let bad = |m: String| Err(crate::Error::InvalidCircuit(m));
        if !(1..=MAX_SHOTS).contains(&self.shots) {
            return bad(format!("{} shots, supported 1..={MAX_SHOTS}", self.shots));
        }
        if !(1..=MAX_CBITS).contains(&self.cbits) {
            return bad(format!(
                "{} classical bits, supported 1..={MAX_CBITS}",
                self.cbits
            ));
        }
        Ok(())
    }

    /// The classical register a basis state measures to: bit `cbit` is the measured qubit's bit
    /// (a later measure into the same cbit wins); unmeasured cbits are 0.
    pub fn outcome(&self, basis: usize) -> usize {
        let mut reg = 0usize;
        for m in &self.measures {
            let bit = (basis >> m.qubit) & 1;
            reg = (reg & !(1 << m.cbit)) | (bit << m.cbit);
        }
        reg
    }

    /// Draw rows the leaf provides: `2s + 14⌈√(2s)⌉ + 128` for `s` shots, rounded up to a
    /// multiple of four. Each draw is accepted with probability about 1/2, so by Hoeffding the
    /// draws run out before `s` acceptances with probability below `2^-100`.
    pub fn draws(&self) -> usize {
        let two_s = 2 * self.shots as usize;
        let mut root = two_s.isqrt();
        if root * root < two_s {
            root += 1;
        }
        (two_s + 14 * root + 128).next_multiple_of(4)
    }

    /// Length of the counts vector: one per register value, at least one sponge block.
    pub fn counts_len(&self) -> usize {
        (1usize << self.cbits).max(RATE)
    }
}

/// The seed as two field elements (low and high 32 bits).
pub fn seed_words(seed: u64) -> [u64; 2] {
    [seed & 0xffff_ffff, seed >> 32]
}

pub(crate) fn prf_input(seed: u64, k: usize) -> [F; PW] {
    let [lo, hi] = seed_words(seed);
    let mut x = [F::ZERO; PW];
    x[0] = F::from_u64(lo);
    x[1] = F::from_u64(hi);
    x[2] = F::from_usize(k);
    x[RATE] = F::from_u64(PRF_TAG);
    x
}

pub(crate) fn permute(x: [F; PW]) -> [F; PW] {
    let tr = perm_trace(vec![x]);
    let cols: &P2Cols<F> = tr.values.as_slice().borrow();
    cols.ending_full_rounds[HALF - 1].post
}

/// One draw of the sampling loop, as the draw table records it.
#[derive(Clone, Debug, Default)]
pub struct Draw {
    pub r: u64,
    pub u: u64,
    /// The basis state picked, or `2^n` for a rejected draw.
    pub b: usize,
    pub lo: u64,
    pub hi: u64,
    pub accepted: bool,
    /// Whether the draw counts (fewer than `shots` accepted before it).
    pub live: bool,
    /// Draws accepted before this one.
    pub before: u64,
}

/// Everything the sampling proves, from the final logical state.
#[derive(Clone, Debug, Default)]
pub struct BornRun {
    /// Running sums before each basis state (`C_{b−1}`, `C_{−1} = 0`), then the total.
    pub cum: Vec<u64>,
    pub draws: Vec<Draw>,
    /// Hits per basis state (live accepted draws).
    pub hits: Vec<u64>,
    /// Live rejected draws.
    pub rejects: u64,
    pub counts: Vec<u64>,
    /// Inputs of the permutations: one per four draws.
    pub prf_in: Vec<[F; PW]>,
    pub prf_out: Vec<[F; PW]>,
}

/// Samples `sampling.shots` outcomes from the final logical state `fin` under `seed`.
pub fn sample(fin: &[C], sampling: &Sampling, seed: u64) -> Result<BornRun, crate::Error> {
    let dim = fin.len();
    let mut cum = Vec::with_capacity(dim + 1);
    let mut acc = 0u64;
    for &(re, im) in fin {
        cum.push(acc);
        acc += (re * re + im * im) as u64;
    }
    cum.push(acc);
    let total = acc;
    // Below 2^57 − 2^32 + 1, so that every accepted value is equally likely (see the module).
    if total > (1 << U_BITS) - (1 << 32) || total == 0 {
        return Err(crate::Error::Prove(format!(
            "state weight {total} out of range"
        )));
    }
    let n_draws = sampling.draws();
    let mut run = BornRun {
        hits: vec![0; dim],
        counts: vec![0; sampling.counts_len()],
        ..Default::default()
    };
    let mut accepted = 0u64;
    for k in 0..n_draws / 4 {
        let x = prf_input(seed, k);
        let y = permute(x);
        run.prf_in.push(x);
        run.prf_out.push(y);
        for &rf in &y[..4] {
            let r = rf.as_canonical_u64();
            let u = r & ((1 << U_BITS) - 1);
            let live = accepted < sampling.shots as u64;
            let mut d = Draw {
                r,
                u,
                live,
                before: accepted,
                ..Default::default()
            };
            if live {
                if u >= total {
                    d.b = dim;
                    d.lo = total;
                    d.hi = 1 << U_BITS;
                    run.rejects += 1;
                } else {
                    // The last b with C_{b−1} ≤ u; it has C_b > u, so p_b > 0.
                    let b = cum[..dim].partition_point(|&c| c <= u) - 1;
                    d.b = b;
                    d.lo = cum[b];
                    d.hi = cum[b + 1];
                    d.accepted = true;
                    run.hits[b] += 1;
                    run.counts[sampling.outcome(b)] += 1;
                    accepted += 1;
                }
            }
            run.draws.push(d);
        }
    }
    if accepted < sampling.shots as u64 {
        return Err(crate::Error::Prove(format!(
            "{accepted} of {} shots accepted in {n_draws} draws",
            sampling.shots
        )));
    }
    run.cum = cum;
    Ok(run)
}

/// Sponge over the counts (four per block into the rate, from the zero state): per-block
/// (input, output) states and the digest.
pub(crate) fn counts_sponge(counts: &[u64]) -> (Vec<[F; PW]>, Vec<[F; PW]>, [F; DIGEST_LEN]) {
    let mut ins = Vec::new();
    let mut outs = Vec::new();
    let mut st = [F::ZERO; PW];
    for block in counts.chunks(RATE) {
        for (c, &x) in block.iter().enumerate() {
            st[c] += F::from_u64(x);
        }
        let out = permute(st);
        ins.push(st);
        outs.push(out);
        st = out;
    }
    (ins, outs, [st[0], st[1], st[2], st[3]])
}

/// The counts digest a verifier recomputes from the published counts (one per classical
/// register value, padded with zeros to a nonzero multiple of four). Each count is reduced
/// mod p, so the digest does not bind counts at or above p: see [`crate::leaf::Leaf::verify_sampling`].
pub fn counts_digest(counts: &[u64]) -> [u64; DIGEST_LEN] {
    let mut v = counts.to_vec();
    v.resize(v.len().max(1).next_multiple_of(RATE), 0);
    counts_sponge(&v).2.map(|x| x.as_canonical_u64())
}

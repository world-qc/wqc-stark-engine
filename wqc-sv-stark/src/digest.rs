//! Poseidon2 sponge over the final state; the digest is the leaf's terminal commitment.

use std::borrow::Borrow;

use crate::exec::*;
use crate::F;
use p3_field::{PrimeCharacteristicRing, PrimeField64};
use p3_goldilocks::{
    GenericPoseidon2LinearLayersGoldilocks, GOLDILOCKS_POSEIDON2_HALF_FULL_ROUNDS,
    GOLDILOCKS_POSEIDON2_PARTIAL_ROUNDS_8,
};
use p3_matrix::dense::RowMajorMatrix;
use p3_poseidon2_air::{generate_trace_rows, Poseidon2Air, Poseidon2Cols, RoundConstants};

pub const DIGEST_LEN: usize = 4;

pub(crate) const PW: usize = 8;
pub(crate) const RATE: usize = 4;
pub(crate) const HALF: usize = GOLDILOCKS_POSEIDON2_HALF_FULL_ROUNDS;
pub(crate) const PARTIAL: usize = GOLDILOCKS_POSEIDON2_PARTIAL_ROUNDS_8;
pub(crate) const SBOX_DEG: u64 = 7;
pub(crate) const SBOX_REG: usize = 1;
pub(crate) type P2Air =
    Poseidon2Air<F, GenericPoseidon2LinearLayersGoldilocks, PW, SBOX_DEG, SBOX_REG, HALF, PARTIAL>;
pub(crate) type P2Cols<T> = Poseidon2Cols<T, PW, SBOX_DEG, SBOX_REG, HALF, PARTIAL>;

pub(crate) fn round_constants() -> RoundConstants<F, PW, HALF, PARTIAL> {
    use rand::SeedableRng;
    RoundConstants::from_rng(&mut rand::rngs::SmallRng::seed_from_u64(7))
}

pub(crate) fn perm_trace(inputs: Vec<[F; PW]>) -> RowMajorMatrix<F> {
    generate_trace_rows::<
        F,
        GenericPoseidon2LinearLayersGoldilocks,
        PW,
        SBOX_DEG,
        SBOX_REG,
        HALF,
        PARTIAL,
    >(inputs, &round_constants(), 0)
}

/// Sponge over the final state (2 amplitudes per block into the rate, from the zero state):
/// per-block (input, output) states and the digest.
pub fn sponge(fin: &[C]) -> (Vec<[F; PW]>, Vec<[F; PW]>, [F; DIGEST_LEN]) {
    let mut ins = Vec::new();
    let mut outs = Vec::new();
    let mut st = [F::ZERO; PW];
    for k in 0..fin.len() / 2 {
        let block = [
            fin[2 * k].0,
            fin[2 * k].1,
            fin[2 * k + 1].0,
            fin[2 * k + 1].1,
        ];
        for c in 0..RATE {
            st[c] += fi::<F>(block[c]);
        }
        let tr = perm_trace(vec![st]);
        let cols: &P2Cols<F> = tr.values.as_slice().borrow();
        let out = cols.ending_full_rounds[HALF - 1].post;
        ins.push(st);
        outs.push(out);
        st = out;
    }
    (ins, outs, [st[0], st[1], st[2], st[3]])
}

/// The digest a verifier recomputes from a published final state.
pub fn terminal_digest(fin: &[C]) -> [u64; DIGEST_LEN] {
    sponge(fin).2.map(|x| x.as_canonical_u64())
}

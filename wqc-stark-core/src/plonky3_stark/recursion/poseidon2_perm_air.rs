//! E5b: width-16 Poseidon2 permutation AIR over Mersenne31 (Plonky3 default RC tables).
//!
//! One uni-STARK proves a full Poseidon2 perm (23 round steps, 24 state rows). Intended to
//! replace Keccak-f bit sponges inside M4b Mmcs group STARKs.

#![allow(clippy::needless_range_loop)]

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_field::{Field, PrimeCharacteristicRing, PrimeField32};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_mersenne_31::{
    default_mersenne31_poseidon2_16, Mersenne31,
    MERSENNE31_POSEIDON2_RC_16_EXTERNAL_FINAL, MERSENNE31_POSEIDON2_RC_16_EXTERNAL_INITIAL,
    MERSENNE31_POSEIDON2_RC_16_INTERNAL,
};
use p3_symmetric::Permutation;
use p3_uni_stark::{prove, verify};

use crate::air::pad_air_matrix_for_uni_stark;
use crate::plonky3_stark::config::{devnet_circle_config, WqcStarkConfig};

use super::poseidon2_spike::POSEIDON2_WIDTH;

/// State columns `[0..WIDTH)`.
pub const POSEIDON2_PERM_STATE_COLS: usize = POSEIDON2_WIDTH;

/// Step-index bit decomposition columns `[WIDTH..WIDTH+STEP_BITS)`.
pub const POSEIDON2_STEP_BITS: usize = 5;

/// Active-row flag (0 on padded rows appended for uni-STARK height).
pub const POSEIDON2_LIVE_COL: usize = POSEIDON2_WIDTH + POSEIDON2_STEP_BITS;

/// Trace width: state + step selector bits + live flag.
pub const POSEIDON2_PERM_WIDTH: usize = POSEIDON2_LIVE_COL + 1;

/// Rows in a single perm trace (initial state + 23 round outputs).
pub const POSEIDON2_PERM_ROWS: usize = 24;

/// Round steps inside one permutation.
pub const POSEIDON2_PERM_STEPS: usize = POSEIDON2_PERM_ROWS - 1;

pub const POSEIDON2_STEP_COL: usize = POSEIDON2_WIDTH;

/// Public layout: `input[WIDTH] | output[WIDTH]`.
pub const POSEIDON2_PERM_NUM_PUBLIC: usize = POSEIDON2_WIDTH * 2;

#[derive(Copy, Clone, Debug)]
pub struct Poseidon2PermAir;

impl<F: Field> BaseAir<F> for Poseidon2PermAir {
    fn width(&self) -> usize {
        POSEIDON2_PERM_WIDTH
    }

    fn max_constraint_degree(&self) -> Option<usize> {
        None
    }

    fn num_public_values(&self) -> usize {
        POSEIDON2_PERM_NUM_PUBLIC
    }
}

fn bool_m31(b: bool) -> Mersenne31 {
    if b {
        Mersenne31::ONE
    } else {
        Mersenne31::ZERO
    }
}

fn step_bits_m31(step: usize) -> [Mersenne31; POSEIDON2_STEP_BITS] {
    core::array::from_fn(|i| bool_m31(((step >> i) & 1) == 1))
}

#[inline]
fn sbox5<R: PrimeCharacteristicRing>(x: R) -> R {
    let x2 = x.clone() * x.clone();
    x2.clone() * x2 * x
}

#[inline]
fn apply_mat4<R: PrimeCharacteristicRing>(x: &mut [R; 4]) {
    let t01 = x[0].clone() + x[1].clone();
    let t23 = x[2].clone() + x[3].clone();
    let t0123 = t01.clone() + t23.clone();
    let t01123 = t0123.clone() + x[1].clone();
    let t01233 = t0123 + x[3].clone();
    x[3] = t01233.clone() + x[0].clone().double();
    x[1] = t01123.clone() + x[2].clone().double();
    x[0] = t01123 + t01;
    x[2] = t01233 + t23;
}

fn mds_light<R: PrimeCharacteristicRing, const WIDTH: usize>(state: &mut [R; WIDTH]) {
    match WIDTH {
        16 => {
            for chunk_idx in 0..4 {
                let base = chunk_idx * 4;
                let mut arr = [
                    state[base].clone(),
                    state[base + 1].clone(),
                    state[base + 2].clone(),
                    state[base + 3].clone(),
                ];
                apply_mat4(&mut arr);
                state[base] = arr[0].clone();
                state[base + 1] = arr[1].clone();
                state[base + 2] = arr[2].clone();
                state[base + 3] = arr[3].clone();
            }
            let sums: [R; 4] =
                core::array::from_fn(|k| (0..WIDTH).step_by(4).map(|j| state[j + k].clone()).sum());
            for (i, elem) in state.iter_mut().enumerate() {
                *elem += sums[i % 4].clone();
            }
        }
        _ => panic!("unsupported width"),
    }
}

fn internal_linear<R: PrimeCharacteristicRing>(state: &mut [R; POSEIDON2_WIDTH]) {
    let part_sum: R = state[1..].iter().map(|r| r.clone()).sum();
    let full_sum = part_sum.clone() + state[0].clone();
    state[0] = part_sum - state[0].clone();
    state[1] = full_sum.clone() + state[1].clone();
    state[2] = full_sum.clone() + state[2].clone().double();
    const SHIFTS: [u64; 13] = [2, 3, 4, 5, 6, 7, 8, 10, 12, 13, 14, 15, 16];
    for (val, shift) in state[3..].iter_mut().zip(SHIFTS.iter()) {
        *val = full_sum.clone() + val.clone().mul_2exp_u64(*shift);
    }
}

fn external_round_native(state: &mut [Mersenne31; POSEIDON2_WIDTH], rc: &[Mersenne31; POSEIDON2_WIDTH]) {
    for i in 0..POSEIDON2_WIDTH {
        state[i] = sbox5(state[i] + rc[i]);
    }
    mds_light(state);
}

fn external_round<R: PrimeCharacteristicRing>(state: &mut [R; POSEIDON2_WIDTH], rc: &[R; POSEIDON2_WIDTH]) {
    for i in 0..POSEIDON2_WIDTH {
        state[i] = sbox5(state[i].clone() + rc[i].clone());
    }
    mds_light(state);
}

fn internal_round<R: PrimeCharacteristicRing>(state: &mut [R; POSEIDON2_WIDTH], rc: R) {
    state[0] = sbox5(state[0].clone() + rc);
    internal_linear(state);
}

fn step_bits_expr<AB: AirBuilder>(vars: &[AB::Var]) -> AB::Expr
where
    AB::F: PrimeCharacteristicRing,
{
    let mut acc = AB::Expr::ZERO;
    let mut pow = AB::Expr::ONE;
    let two = AB::Expr::TWO;
    for v in vars {
        acc += (*v).into() * pow.clone();
        pow *= two.clone();
    }
    acc
}

pub(crate) fn selector_for_step<AB: AirBuilder>(bits: &[AB::Var], step: usize) -> AB::Expr
where
    AB::F: PrimeCharacteristicRing,
{
    let mut sel = AB::Expr::ONE;
    for i in 0..POSEIDON2_STEP_BITS {
        let b: AB::Expr = bits[i].into();
        if (step >> i) & 1 == 1 {
            sel *= b;
        } else {
            sel *= AB::Expr::ONE - b;
        }
    }
    sel
}

pub(crate) fn constrain_external<AB: AirBuilder>(
    builder: &mut AB,
    curr: &[AB::Var; POSEIDON2_WIDTH],
    next: &[AB::Var; POSEIDON2_WIDTH],
    rc: &[Mersenne31; POSEIDON2_WIDTH],
    enable: AB::Expr,
) where
    AB::F: Field + PrimeCharacteristicRing,
{
    let mut after_sbox = [AB::Expr::ZERO; POSEIDON2_WIDTH];
    for i in 0..POSEIDON2_WIDTH {
        after_sbox[i] = sbox5(AB::Expr::from(curr[i]) + AB::F::from_u32(rc[i].as_canonical_u32()));
    }
    let mut expected = after_sbox;
    mds_light(&mut expected);
    for i in 0..POSEIDON2_WIDTH {
        builder.assert_zero(enable.clone() * (AB::Expr::from(next[i]) - expected[i].clone()));
    }
}

pub(crate) fn constrain_internal<AB: AirBuilder>(
    builder: &mut AB,
    curr: &[AB::Var; POSEIDON2_WIDTH],
    next: &[AB::Var; POSEIDON2_WIDTH],
    rc: Mersenne31,
    enable: AB::Expr,
) where
    AB::F: Field + PrimeCharacteristicRing,
{
    let mut expected = [AB::Expr::ZERO; POSEIDON2_WIDTH];
    for i in 0..POSEIDON2_WIDTH {
        expected[i] = AB::Expr::from(curr[i]);
    }
    expected[0] = sbox5(AB::Expr::from(curr[0]) + AB::F::from_u32(rc.as_canonical_u32()));
    internal_linear(&mut expected);
    for i in 0..POSEIDON2_WIDTH {
        builder.assert_zero(enable.clone() * (AB::Expr::from(next[i]) - expected[i].clone()));
    }
}

pub(crate) fn constrain_mds_only<AB: AirBuilder>(
    builder: &mut AB,
    curr: &[AB::Var; POSEIDON2_WIDTH],
    next: &[AB::Var; POSEIDON2_WIDTH],
    enable: AB::Expr,
) where
    AB::F: Field + PrimeCharacteristicRing,
{
    let mut expected = [AB::Expr::ZERO; POSEIDON2_WIDTH];
    for i in 0..POSEIDON2_WIDTH {
        expected[i] = AB::Expr::from(curr[i]);
    }
    mds_light(&mut expected);
    for i in 0..POSEIDON2_WIDTH {
        builder.assert_zero(enable.clone() * (AB::Expr::from(next[i]) - expected[i].clone()));
    }
}

impl<AB: AirBuilder> Air<AB> for Poseidon2PermAir
where
    AB::F: Field + PrimeCharacteristicRing,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.current_slice();
        let next = main.next_slice();
        let pv: Vec<AB::Expr> = builder
            .public_values()
            .iter()
            .map(|v| (*v).into())
            .collect();

        let curr_state: [AB::Var; POSEIDON2_WIDTH] =
            core::array::from_fn(|i| local[i]);
        let next_state: [AB::Var; POSEIDON2_WIDTH] =
            core::array::from_fn(|i| next[i]);
        let step_bits: [AB::Var; POSEIDON2_STEP_BITS] =
            core::array::from_fn(|i| local[POSEIDON2_STEP_COL + i]);
        let live_c: AB::Expr = local[POSEIDON2_LIVE_COL].into();
        let live_n: AB::Expr = next[POSEIDON2_LIVE_COL].into();

        builder.assert_bools(step_bits);
        builder.assert_bools([local[POSEIDON2_LIVE_COL]]);
        let is_tr = builder.is_transition();
        let both_live = live_c.clone() * live_n.clone();

        // Step index increments by one on in-segment transitions (not after the final round step).
        let step_c = step_bits_expr::<AB>(&step_bits);
        let step_bits_n: [AB::Var; POSEIDON2_STEP_BITS] =
            core::array::from_fn(|i| next[POSEIDON2_STEP_COL + i]);
        let step_n = step_bits_expr::<AB>(&step_bits_n);
        let not_last_step =
            AB::Expr::ONE - selector_for_step::<AB>(&step_bits, POSEIDON2_PERM_STEPS - 1);
        builder.assert_zero(
            is_tr.clone() * both_live.clone() * not_last_step
                * (step_n - step_c.clone() - AB::Expr::ONE),
        );
        builder.when_first_row().assert_zero(step_c.clone());
        builder.when_first_row().assert_zero(live_c.clone() - AB::Expr::ONE);

        // Bind first/last active states to public IO.
        let end_active = live_c.clone() * (AB::Expr::ONE - live_n.clone());
        for i in 0..POSEIDON2_WIDTH {
            builder
                .when_first_row()
                .assert_zero(AB::Expr::from(curr_state[i]) - pv[i].clone());
            builder
                .when(end_active.clone())
                .assert_zero(AB::Expr::from(curr_state[i]) - pv[POSEIDON2_WIDTH + i].clone());
        }

        // Padded / idle rows: copy state forward.
        let idle = AB::Expr::ONE - live_c.clone();
        for i in 0..POSEIDON2_WIDTH {
            builder.assert_zero(
                is_tr.clone() * idle.clone() * (AB::Expr::from(next_state[i]) - AB::Expr::from(curr_state[i])),
            );
        }

        for step in 0..POSEIDON2_PERM_STEPS {
            let sel = selector_for_step::<AB>(&step_bits, step);
            let enable = is_tr.clone() * both_live.clone() * sel;
            match step {
                0 => constrain_mds_only(builder, &curr_state, &next_state, enable),
                1..=4 => {
                    let rc = &MERSENNE31_POSEIDON2_RC_16_EXTERNAL_INITIAL[step - 1];
                    constrain_external(builder, &curr_state, &next_state, rc, enable);
                }
                5..=18 => {
                    let rc = MERSENNE31_POSEIDON2_RC_16_INTERNAL[step - 5];
                    constrain_internal(builder, &curr_state, &next_state, rc, enable);
                }
                19..=22 => {
                    let rc = &MERSENNE31_POSEIDON2_RC_16_EXTERNAL_FINAL[step - 19];
                    constrain_external(builder, &curr_state, &next_state, rc, enable);
                }
                _ => unreachable!(),
            }
        }
    }
}

/// Native round-step trace matching [`default_mersenne31_poseidon2_16`].
pub fn build_perm_trace(input: [Mersenne31; POSEIDON2_WIDTH]) -> RowMajorMatrix<Mersenne31> {
    let mut states = vec![input];
    let mut state = input;

    mds_light(&mut state);
    states.push(state);

    for rc in MERSENNE31_POSEIDON2_RC_16_EXTERNAL_INITIAL {
        external_round_native(&mut state, &rc);
        states.push(state);
    }
    for rc in MERSENNE31_POSEIDON2_RC_16_INTERNAL {
        internal_round(&mut state, rc);
        states.push(state);
    }
    for rc in MERSENNE31_POSEIDON2_RC_16_EXTERNAL_FINAL {
        external_round_native(&mut state, &rc);
        states.push(state);
    }

    assert_eq!(states.len(), POSEIDON2_PERM_ROWS);
    let mut values = Vec::with_capacity(POSEIDON2_PERM_ROWS * POSEIDON2_PERM_WIDTH);
    for (step, st) in states.iter().enumerate() {
        values.extend_from_slice(st);
        let bits = step_bits_m31(step.min(POSEIDON2_PERM_STEPS - 1));
        values.extend_from_slice(&bits);
        values.push(Mersenne31::ONE);
    }
    RowMajorMatrix::new(values, POSEIDON2_PERM_WIDTH)
}

fn zero_live_on_padded_rows(matrix: &mut RowMajorMatrix<Mersenne31>) {
    for r in POSEIDON2_PERM_ROWS..matrix.height() {
        matrix.values[r * POSEIDON2_PERM_WIDTH + POSEIDON2_LIVE_COL] = Mersenne31::ZERO;
    }
}

pub fn pad_poseidon_perm_matrix(input: [Mersenne31; POSEIDON2_WIDTH]) -> RowMajorMatrix<Mersenne31> {
    let mut matrix = pad_air_matrix_for_uni_stark(build_perm_trace(input));
    zero_live_on_padded_rows(&mut matrix);
    matrix
}

pub fn poseidon2_permute_native(input: [Mersenne31; POSEIDON2_WIDTH]) -> [Mersenne31; POSEIDON2_WIDTH] {
    let mut state = input;
    default_mersenne31_poseidon2_16().permute_mut(&mut state);
    state
}

fn build_public_values(
    input: &[Mersenne31; POSEIDON2_WIDTH],
    output: &[Mersenne31; POSEIDON2_WIDTH],
) -> Vec<Mersenne31> {
    let mut pv = Vec::with_capacity(POSEIDON2_PERM_NUM_PUBLIC);
    pv.extend_from_slice(input);
    pv.extend_from_slice(output);
    pv
}

pub fn generate_poseidon2_perm_proof(
    input: [Mersenne31; POSEIDON2_WIDTH],
) -> Result<Vec<u8>, String> {
    let output = poseidon2_permute_native(input);
    let matrix = pad_poseidon_perm_matrix(input);
    let pv = build_public_values(&input, &output);
    p3_air::check_constraints(&Poseidon2PermAir, &matrix, &pv);
    let config = devnet_circle_config();
    let proof = prove(&config, &Poseidon2PermAir, matrix, &pv);
    super::prove_workspace::encode_stark_and_drop(proof, "poseidon2 perm")
}

pub fn verify_poseidon2_perm_proof(
    input: [Mersenne31; POSEIDON2_WIDTH],
    stark: &[u8],
) -> bool {
    let output = poseidon2_permute_native(input);
    let pv = build_public_values(&input, &output);
    let proof: p3_uni_stark::Proof<WqcStarkConfig> = match postcard::from_bytes(stark) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("[Poseidon2Perm] postcard: {e}");
            return false;
        }
    };
    let config = devnet_circle_config();
    verify(&config, &Poseidon2PermAir, &proof, &pv).is_ok()
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_field::PrimeCharacteristicRing;

    #[test]
    fn native_trace_matches_default_perm() {
        let input = core::array::from_fn(|i| Mersenne31::from_u32((i as u32 + 1) * 17));
        let trace = build_perm_trace(input);
        assert_eq!(trace.height(), POSEIDON2_PERM_ROWS);
        let last = &trace.values[(POSEIDON2_PERM_ROWS - 1) * POSEIDON2_PERM_WIDTH
            ..POSEIDON2_PERM_ROWS * POSEIDON2_PERM_WIDTH];
        let got: [Mersenne31; POSEIDON2_WIDTH] =
            core::array::from_fn(|i| last[i]);
        assert_eq!(got, poseidon2_permute_native(input));
    }

    #[test]
    fn poseidon2_perm_proof_roundtrip() {
        let input = core::array::from_fn(|i| Mersenne31::from_u32(i as u32 + 42));
        let stark = generate_poseidon2_perm_proof(input).expect("prove");
        assert!(verify_poseidon2_perm_proof(input, &stark));
        assert!(!stark.is_empty());
    }

    #[test]
    fn poseidon2_perm_stark_smaller_than_keccak_compress() {
        use super::super::keccak256_air::prove_compress;
        use super::super::keccak_f_native::keccak256_compress;

        let input = core::array::from_fn(|i| Mersenne31::from_u32(i as u32 + 7));
        let poseidon_stark = generate_poseidon2_perm_proof(input).expect("poseidon prove");

        let left = [1u8; 32];
        let right = [2u8; 32];
        let digest = keccak256_compress(left, right);
        let keccak_proof = prove_compress(left, right).expect("keccak prove");
        assert_eq!(keccak_proof.digest, digest);

        eprintln!(
            "perm stark: poseidon={} vs keccak_compress={}",
            poseidon_stark.len(),
            keccak_proof.stark.len()
        );
        assert!(
            poseidon_stark.len() < keccak_proof.stark.len(),
            "poseidon {} not smaller than keccak {}",
            poseidon_stark.len(),
            keccak_proof.stark.len()
        );
    }
}

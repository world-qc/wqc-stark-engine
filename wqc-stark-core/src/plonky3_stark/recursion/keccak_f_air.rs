//! R3-M2.5b: bit-level Keccak-f[1600] round transition AIR helpers (Plonky3 0.6).
//!
//! Trace layout for a reusable single-permutation / sponge wrapper:
//! - columns `0..1600`: state bits (`lane * 64 + bit`, bit 0 = LSB)
//! - column `1600`: `live` flag
//!
//! Prover height sketch (one permutation): rows `0..23` live=1 (pre-round),
//! row 24 = post-final-round live=0, rows `25..31` copies with live=0.
//! Round index for live row `i` is `i` (single perm) or `i % 24` (multi-block).
//!
//! This module exports pure constraint helpers; sponge IO binding lives elsewhere.

#![allow(clippy::needless_range_loop)]

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_field::{Field, PrimeCharacteristicRing};
#[cfg(test)]
use p3_matrix::dense::RowMajorMatrix;
#[cfg(test)]
use p3_mersenne_31::Mersenne31;

use super::keccak_f_native::{bits_to_state, keccak_round, state_to_bits, KECCAK_STATE_BITS, RC};

/// Trace width: 1600 state bits + 1 `live` flag.
pub const KECCAK_F_WIDTH: usize = KECCAK_STATE_BITS + 1;

/// Column index of state bit `i` (`i` in `0..1600`).
#[inline]
#[allow(dead_code)]
pub const fn bit_col(i: usize) -> usize {
    i
}

/// Column index of the `live` flag (last column).
pub const LIVE_COL: usize = KECCAK_STATE_BITS;

/// ρ rotation offsets (tiny_keccak / FIPS 202 lane order, excluding lane 0).
const RHO: [u32; 24] = [
    1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14, 27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20, 44,
];

/// π lane permutation targets (tiny_keccak).
const PI: [usize; 24] = [
    10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4, 15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1,
];

#[inline]
fn bit_xor<AB: AirBuilder>(a: AB::Expr, b: AB::Expr) -> AB::Expr
where
    AB::F: PrimeCharacteristicRing,
{
    let two = AB::Expr::TWO;
    a.clone() + b.clone() - two * a * b
}

#[inline]
fn bit_and<AB: AirBuilder>(a: AB::Expr, b: AB::Expr) -> AB::Expr {
    a * b
}

#[inline]
fn bit_not<AB: AirBuilder>(a: AB::Expr) -> AB::Expr
where
    AB::F: PrimeCharacteristicRing,
{
    AB::Expr::ONE - a
}

/// Apply one Keccak-f round to a boolean state (witness oracle via native `keccak_round`).
pub fn apply_round_bits(curr: &[bool; KECCAK_STATE_BITS], rc: u64) -> [bool; KECCAK_STATE_BITS] {
    let mut state = bits_to_state(curr);
    keccak_round(&mut state, rc);
    state_to_bits(&state)
}

/// Build expected next-state bit expressions with symbolic RC bits (`rc_bits[b]` = bit b of RC).
pub fn keccak_round_bits_expr_with_rc<AB>(
    curr_bits: &[AB::Var],
    rc_bits: &[AB::Expr],
) -> Vec<AB::Expr>
where
    AB: AirBuilder,
    AB::F: Field + PrimeCharacteristicRing,
{
    assert_eq!(curr_bits.len(), KECCAK_STATE_BITS);
    assert_eq!(rc_bits.len(), 64);
    let a: Vec<AB::Expr> = curr_bits.iter().map(|v| (*v).into()).collect();

    // θ — column parity then mix
    let mut c = vec![vec![AB::Expr::ZERO; 64]; 5];
    for x in 0..5 {
        for b in 0..64 {
            let mut acc = AB::Expr::ZERO;
            for y in 0..5 {
                let lane = y * 5 + x;
                acc = bit_xor::<AB>(acc, a[lane * 64 + b].clone());
            }
            c[x][b] = acc;
        }
    }
    let mut after_theta = a.clone();
    for x in 0..5 {
        for b in 0..64 {
            let c_left = c[(x + 4) % 5][b].clone();
            // rotate_left(1): bit b ← bit (b−1) mod 64
            let c_right = c[(x + 1) % 5][(b + 63) % 64].clone();
            let d = bit_xor::<AB>(c_left, c_right);
            for y in 0..5 {
                let lane = y * 5 + x;
                let idx = lane * 64 + b;
                after_theta[idx] = bit_xor::<AB>(a[idx].clone(), d.clone());
            }
        }
    }

    // ρ and π — chain matching tiny_keccak
    let mut lanes: Vec<[AB::Expr; 64]> = (0..25)
        .map(|lane| core::array::from_fn(|b| after_theta[lane * 64 + b].clone()))
        .collect();
    let mut last = lanes[1].clone();
    for x in 0..24 {
        let dest = PI[x];
        let tmp = lanes[dest].clone();
        let rot = RHO[x] % 64;
        for b in 0..64 {
            let src = ((b as u32 + 64 - rot) % 64) as usize;
            lanes[dest][b] = last[src].clone();
        }
        last = tmp;
    }

    // χ — degree 3: a ⊕ ((¬b) ∧ c)
    let mut after_chi = lanes.clone();
    for y in 0..5 {
        let base = y * 5;
        let t0 = lanes[base].clone();
        let t1 = lanes[base + 1].clone();
        let t2 = lanes[base + 2].clone();
        let t3 = lanes[base + 3].clone();
        let t4 = lanes[base + 4].clone();
        let t = [&t0, &t1, &t2, &t3, &t4];
        for x in 0..5 {
            for b in 0..64 {
                let and_term = bit_and::<AB>(
                    bit_not::<AB>(t[(x + 1) % 5][b].clone()),
                    t[(x + 2) % 5][b].clone(),
                );
                after_chi[base + x][b] = bit_xor::<AB>(t[x][b].clone(), and_term);
            }
        }
    }

    // ι — XOR round constant into lane 0
    for b in 0..64 {
        after_chi[0][b] = bit_xor::<AB>(after_chi[0][b].clone(), rc_bits[b].clone());
    }

    let mut out = Vec::with_capacity(KECCAK_STATE_BITS);
    for lane in 0..25 {
        for b in 0..64 {
            out.push(after_chi[lane][b].clone());
        }
    }
    out
}

/// Build expected next-state with a constant round constant.
pub fn keccak_round_bits_expr<AB>(curr_bits: &[AB::Var], rc: u64) -> Vec<AB::Expr>
where
    AB: AirBuilder,
    AB::F: Field + PrimeCharacteristicRing,
{
    let rc_bits: Vec<AB::Expr> = (0..64)
        .map(|b| {
            if ((rc >> b) & 1) == 1 {
                AB::Expr::ONE
            } else {
                AB::Expr::ZERO
            }
        })
        .collect();
    keccak_round_bits_expr_with_rc::<AB>(curr_bits, &rc_bits)
}

/// When `enable = 1`, assert `next_bits = keccak_round(curr_bits, rc)` bit-wise.
pub fn constrain_keccak_round<AB: AirBuilder>(
    builder: &mut AB,
    curr_bits: &[AB::Var],
    next_bits: &[AB::Var],
    rc: u64,
    enable: AB::Expr,
) where
    AB::F: Field + PrimeCharacteristicRing,
{
    assert_eq!(curr_bits.len(), KECCAK_STATE_BITS);
    assert_eq!(next_bits.len(), KECCAK_STATE_BITS);
    let expected = keccak_round_bits_expr::<AB>(curr_bits, rc);
    for i in 0..KECCAK_STATE_BITS {
        let next_bit: AB::Expr = next_bits[i].into();
        builder.assert_zero(enable.clone() * (next_bit - expected[i].clone()));
    }
}

/// When `enable = 1`, assert next = round(curr) with symbolic RC bits.
pub fn constrain_keccak_round_with_rc<AB: AirBuilder>(
    builder: &mut AB,
    curr_bits: &[AB::Var],
    next_bits: &[AB::Var],
    rc_bits: &[AB::Expr],
    enable: AB::Expr,
) where
    AB::F: Field + PrimeCharacteristicRing,
{
    assert_eq!(curr_bits.len(), KECCAK_STATE_BITS);
    assert_eq!(next_bits.len(), KECCAK_STATE_BITS);
    let expected = keccak_round_bits_expr_with_rc::<AB>(curr_bits, rc_bits);
    for i in 0..KECCAK_STATE_BITS {
        let next_bit: AB::Expr = next_bits[i].into();
        builder.assert_zero(enable.clone() * (next_bit - expected[i].clone()));
    }
}

/// Low-level AIR for a single fixed-`rc` round transition (sponge selects `rc`).
///
/// `num_public_values = 0`; wrappers bind sponge IO. Degree 3 from χ.
#[derive(Copy, Clone, Debug)]
pub struct KeccakFRoundAir {
    pub rc: u64,
}

impl KeccakFRoundAir {
    pub const fn new(rc: u64) -> Self {
        Self { rc }
    }

    pub const fn round(round_idx: usize) -> Self {
        Self {
            rc: RC[round_idx % RC.len()],
        }
    }
}

impl<F: Field> BaseAir<F> for KeccakFRoundAir {
    fn width(&self) -> usize {
        KECCAK_F_WIDTH
    }

    fn max_constraint_degree(&self) -> Option<usize> {
        Some(3)
    }

    fn num_public_values(&self) -> usize {
        0
    }
}

impl<AB: AirBuilder> Air<AB> for KeccakFRoundAir
where
    AB::F: Field + PrimeCharacteristicRing,
{
    fn eval(&self, builder: &mut AB) {
        // Snapshot slices first (avoid holding borrows across asserts).
        let main = builder.main();
        let curr: Vec<AB::Var> = main.current_slice().to_vec();
        let next: Vec<AB::Var> = main.next_slice().to_vec();
        debug_assert_eq!(curr.len(), KECCAK_F_WIDTH);
        debug_assert_eq!(next.len(), KECCAK_F_WIDTH);

        let one = AB::Expr::ONE;

        // Booleanize all columns (state bits + live).
        for i in 0..KECCAK_F_WIDTH {
            let b: AB::Expr = curr[i].into();
            builder.assert_zero(b.clone() * (b - one.clone()));
        }

        // Transition with both rows live: next = keccak_round(curr, rc).
        // (Sponge last round may use enable = curr.live only via `constrain_keccak_round`.)
        let live_c: AB::Expr = curr[LIVE_COL].into();
        let live_n: AB::Expr = next[LIVE_COL].into();
        let enable = builder.is_transition() * live_c * live_n;
        constrain_keccak_round(
            builder,
            &curr[..KECCAK_STATE_BITS],
            &next[..KECCAK_STATE_BITS],
            self.rc,
            enable,
        );
    }
}

/// Build a 2-row trace for one enabled round transition (both rows `live = 1`).
#[cfg(test)]
pub fn build_one_round_matrix(
    pre_bits: &[bool; KECCAK_STATE_BITS],
    rc: u64,
) -> RowMajorMatrix<Mersenne31> {
    let post = apply_round_bits(pre_bits, rc);
    let mut values = Vec::with_capacity(2 * KECCAK_F_WIDTH);
    for &b in pre_bits.iter() {
        values.push(Mersenne31::from_bool(b));
    }
    values.push(Mersenne31::from_bool(true)); // live
    for &b in post.iter() {
        values.push(Mersenne31::from_bool(b));
    }
    values.push(Mersenne31::from_bool(true)); // live
    RowMajorMatrix::new(values, KECCAK_F_WIDTH)
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_field::PrimeCharacteristicRing;

    fn bits_from_u64_lanes(lanes: &[u64; 25]) -> [bool; KECCAK_STATE_BITS] {
        state_to_bits(lanes)
    }

    #[test]
    fn apply_round_bits_matches_native() {
        assert_eq!(bit_col(0), 0);
        assert_eq!(LIVE_COL, 1600);
        assert_eq!(KECCAK_F_WIDTH, 1601);
        assert_eq!(KeccakFRoundAir::round(0).rc, RC[0]);

        let mut state = [0u64; 25];
        state[0] = 0x0123_4567_89ab_cdef;
        state[1] = 0xfedc_ba98_7654_3210;
        state[7] = 0x1111_2222_3333_4444;
        let bits = bits_from_u64_lanes(&state);
        let rc = RC[0];
        let got = apply_round_bits(&bits, rc);
        keccak_round(&mut state, rc);
        assert_eq!(got, state_to_bits(&state));
    }

    #[test]
    fn one_round_air_constraints_hold() {
        let mut state = [0u64; 25];
        for i in 0..25 {
            state[i] = (i as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15) ^ 0xa5a5_a5a5_a5a5_a5a5;
        }
        let pre = bits_from_u64_lanes(&state);
        let rc = RC[3];
        let matrix = build_one_round_matrix(&pre, rc);
        let air = KeccakFRoundAir::new(rc);
        let pv: Vec<Mersenne31> = Vec::new();
        p3_air::check_constraints(&air, &matrix, &pv);
    }

    #[test]
    fn one_round_air_rejects_bad_next() {
        let pre = [false; KECCAK_STATE_BITS];
        let rc = RC[0];
        let mut matrix = build_one_round_matrix(&pre, rc);
        // Flip one post-state bit.
        let flip_idx = KECCAK_F_WIDTH;
        matrix.values[flip_idx] = Mersenne31::ONE - matrix.values[flip_idx];
        let air = KeccakFRoundAir::new(rc);
        let pv: Vec<Mersenne31> = Vec::new();
        let result = std::panic::catch_unwind(|| {
            p3_air::check_constraints(&air, &matrix, &pv);
        });
        assert!(
            result.is_err(),
            "tampered next state should fail constraints"
        );
    }
}

//! Native Circle FRI `fold_x` matching Plonky3 `p3-circle` (arity 2).
//!
//! Formula (log_arity = 1):
//! `t = x_twiddle(rev_bits(index)).inverse()`
//! `out = ((v0 + v1) + β · (v0 − v1) · t) / 2`

use p3_field::extension::ComplexExtendable;
use p3_field::{BasedVectorSpace, Field, PrimeCharacteristicRing};
use p3_mersenne_31::Mersenne31;
use p3_util::reverse_bits_len;

use crate::plonky3_stark::config::Challenge;

pub type Val = Mersenne31;

#[derive(Copy, Clone)]
struct CircPoint {
    x: Val,
    y: Val,
}

impl CircPoint {
    fn generator(log_n: usize) -> Self {
        let g = Val::circle_two_adic_generator(log_n);
        Self {
            x: g.real(),
            y: g.imag(),
        }
    }

    fn add(self, rhs: Self) -> Self {
        Self {
            x: self.x * rhs.x - self.y * rhs.y,
            y: self.x * rhs.y + self.y * rhs.x,
        }
    }

    fn mul_usize(self, mut n: usize) -> Self {
        let mut result = Self {
            x: Val::ONE,
            y: Val::ZERO,
        };
        let mut base = self;
        while n > 0 {
            if n & 1 == 1 {
                result = result.add(base);
            }
            base = base.add(base);
            n >>= 1;
        }
        result
    }
}

/// Twiddle inverse `t` for `fold_x_row` (same as p3-circle `nth_x_twiddle` + inverse).
pub fn fold_x_twiddle_inv(index: usize, log_folded_height: usize) -> Val {
    let log_arity = 1usize;
    let log_n = log_folded_height + log_arity + 1;
    // CircleDomain::standard(log_n): shift = generator(log_n+1), subgroup_gen = generator(log_n-1)
    let shift = CircPoint::generator(log_n + 1);
    let gen = CircPoint::generator(log_n - 1);
    let twiddle_index = reverse_bits_len(index, log_folded_height);
    let x = shift.add(gen.mul_usize(twiddle_index)).x;
    x.inverse()
}

/// Circle FRI arity-2 `fold_x_row`.
pub fn fold_x_row(
    index: usize,
    log_folded_height: usize,
    beta: Challenge,
    v0: Challenge,
    v1: Challenge,
) -> Challenge {
    let t = fold_x_twiddle_inv(index, log_folded_height);
    let t_ef = Challenge::from(t);
    let sum = v0 + v1;
    let diff = (v0 - v1) * t_ef;
    (sum + beta * diff).halve()
}

/// Pack a challenge into three M31 limbs (binomial basis).
pub fn challenge_to_limbs(c: Challenge) -> [Val; 3] {
    let s = c.as_basis_coefficients_slice();
    [s[0], s[1], s[2]]
}

pub fn limbs_to_challenge(limbs: [Val; 3]) -> Challenge {
    Challenge::from_basis_coefficients_iter(limbs.into_iter()).expect("D=3")
}

/// Solve for `v0` such that `fold_x_row(index, log_h, beta, v0, v1) == out`.
pub fn solve_v0_for_fold(
    index: usize,
    log_folded_height: usize,
    beta: Challenge,
    v1: Challenge,
    out: Challenge,
) -> Challenge {
    let t = Challenge::from(fold_x_twiddle_inv(index, log_folded_height));
    let one = Challenge::ONE;
    let coeff_v0 = one + beta * t;
    let coeff_v1 = one - beta * t;
    let numer = out.double() - v1 * coeff_v1;
    numer * coeff_v0.inverse()
}

/// Solve for `v1` such that `fold_x_row(index, log_h, beta, v0, v1) == out`.
pub fn solve_v1_for_fold(
    index: usize,
    log_folded_height: usize,
    beta: Challenge,
    v0: Challenge,
    out: Challenge,
) -> Challenge {
    let t = Challenge::from(fold_x_twiddle_inv(index, log_folded_height));
    let one = Challenge::ONE;
    let coeff_v0 = one + beta * t;
    let coeff_v1 = one - beta * t;
    let numer = out.double() - v0 * coeff_v0;
    numer * coeff_v1.inverse()
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_field::PrimeCharacteristicRing;
    use rand::{Rng, SeedableRng};

    #[test]
    fn fold_roundtrip_solve_v0() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(7);
        for log_h in [1usize, 2, 3] {
            for index in 0..(1 << log_h).min(8) {
                let beta = Challenge::new([
                    Val::from_u32(rng.gen()),
                    Val::from_u32(rng.gen()),
                    Val::from_u32(rng.gen()),
                ]);
                let v0 = Challenge::new([
                    Val::from_u32(rng.gen()),
                    Val::from_u32(rng.gen()),
                    Val::from_u32(rng.gen()),
                ]);
                let v1 = Challenge::new([
                    Val::from_u32(rng.gen()),
                    Val::from_u32(rng.gen()),
                    Val::from_u32(rng.gen()),
                ]);
                let out = fold_x_row(index, log_h, beta, v0, v1);
                let recovered = solve_v0_for_fold(index, log_h, beta, v1, out);
                assert_eq!(recovered, v0);
            }
        }
    }

    #[test]
    fn fold_roundtrip_solve_v1() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(9);
        for log_h in [1usize, 2, 3] {
            for index in 0..(1 << log_h).min(8) {
                let beta = Challenge::new([
                    Val::from_u32(rng.gen()),
                    Val::from_u32(rng.gen()),
                    Val::from_u32(rng.gen()),
                ]);
                let v0 = Challenge::new([
                    Val::from_u32(rng.gen()),
                    Val::from_u32(rng.gen()),
                    Val::from_u32(rng.gen()),
                ]);
                let v1 = Challenge::new([
                    Val::from_u32(rng.gen()),
                    Val::from_u32(rng.gen()),
                    Val::from_u32(rng.gen()),
                ]);
                let out = fold_x_row(index, log_h, beta, v0, v1);
                let recovered = solve_v1_for_fold(index, log_h, beta, v0, out);
                assert_eq!(recovered, v1);
            }
        }
    }

    #[test]
    fn limbs_roundtrip() {
        let c = Challenge::new([Val::from_u32(1), Val::from_u32(2), Val::from_u32(3)]);
        assert_eq!(limbs_to_challenge(challenge_to_limbs(c)), c);
    }
}

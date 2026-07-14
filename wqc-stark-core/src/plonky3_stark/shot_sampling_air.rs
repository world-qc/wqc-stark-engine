//! Plonky3 `Air` for per-shot MEASURE Bernoulli sampling (C2c extension).

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_field::{Field, PrimeCharacteristicRing};

use crate::air::shot_sampling::{SHOT_SAMPLING_GAP_BITS, SHOT_SAMPLING_SCALE};

/// Column layout: p0, p1, u, outcome, gap, gap_bits[0..GAP_BITS), is_pad.
pub const SHOT_SAMPLING_COL_P0: usize = 0;
pub const SHOT_SAMPLING_COL_P1: usize = 1;
pub const SHOT_SAMPLING_COL_U: usize = 2;
pub const SHOT_SAMPLING_COL_OUTCOME: usize = 3;
pub const SHOT_SAMPLING_COL_GAP: usize = 4;
pub const SHOT_SAMPLING_COL_GAP_BITS: usize = 5;
pub const SHOT_SAMPLING_COL_IS_PAD: usize = SHOT_SAMPLING_COL_GAP_BITS + SHOT_SAMPLING_GAP_BITS;

/// Width of one shot-sampling AIR row.
pub const SHOT_SAMPLING_AIR_WIDTH: usize = SHOT_SAMPLING_COL_IS_PAD + 1;

/// Multi-row Bernoulli sampling AIR (one logical MEASURE per non-pad row).
#[derive(Clone, Debug, Default)]
pub struct ShotSamplingAir;

impl ShotSamplingAir {
    pub fn width() -> usize {
        SHOT_SAMPLING_AIR_WIDTH
    }

    /// Host-side row accumulator (`ZERO` iff Bernoulli + bit-decomp constraints hold).
    pub fn evaluate_row_sum<FR>(&self, row: &[FR]) -> FR
    where
        FR: Field + PrimeCharacteristicRing + Copy,
    {
        debug_assert_eq!(row.len(), SHOT_SAMPLING_AIR_WIDTH);
        let is_pad = row[SHOT_SAMPLING_COL_IS_PAD];
        let active = FR::ONE - is_pad;

        let p0 = row[SHOT_SAMPLING_COL_P0];
        let p1 = row[SHOT_SAMPLING_COL_P1];
        let u = row[SHOT_SAMPLING_COL_U];
        let outcome = row[SHOT_SAMPLING_COL_OUTCOME];
        let gap = row[SHOT_SAMPLING_COL_GAP];
        let scale = FR::from_u32(SHOT_SAMPLING_SCALE);

        let mut acc = FR::ZERO;
        // is_pad ∈ {0,1}
        acc += is_pad * (is_pad - FR::ONE);
        // outcome ∈ {0,1}
        acc += active * outcome * (outcome - FR::ONE);

        // gap = Σ bit_i · 2^i
        let mut recomposed = FR::ZERO;
        let mut pow = FR::ONE;
        for i in 0..SHOT_SAMPLING_GAP_BITS {
            let bit = row[SHOT_SAMPLING_COL_GAP_BITS + i];
            acc += active * bit * (bit - FR::ONE);
            recomposed += bit * pow;
            pow = pow + pow;
        }
        acc += active * (gap - recomposed);

        // Bernoulli:
        // outcome=0 ⇒ u*(p0+p1) + gap + 1 = p0*SCALE
        // outcome=1 ⇒ u*(p0+p1) = p0*SCALE + gap
        let lhs = u * (p0 + p1);
        let rhs = p0 * scale;
        let zero_branch = rhs - lhs - gap - FR::ONE;
        let one_branch = lhs - rhs - gap;
        acc += active * (FR::ONE - outcome) * zero_branch;
        acc += active * outcome * one_branch;

        acc
    }
}

impl<F: Field> BaseAir<F> for ShotSamplingAir {
    fn width(&self) -> usize {
        ShotSamplingAir::width()
    }

    fn max_constraint_degree(&self) -> Option<usize> {
        // active * (1-outcome) * (u*(p0+p1) …) reaches degree 4.
        Some(6)
    }
}

impl<AB: AirBuilder> Air<AB> for ShotSamplingAir
where
    AB::F: Field,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let curr = main.current_slice();
        debug_assert_eq!(curr.len(), SHOT_SAMPLING_AIR_WIDTH);

        let is_pad: AB::Expr = curr[SHOT_SAMPLING_COL_IS_PAD].into();
        let active = AB::Expr::ONE - is_pad.clone();
        builder.assert_bool(curr[SHOT_SAMPLING_COL_IS_PAD]);

        let outcome = curr[SHOT_SAMPLING_COL_OUTCOME];
        builder.when(active.clone()).assert_bool(outcome);

        let p0: AB::Expr = curr[SHOT_SAMPLING_COL_P0].into();
        let p1: AB::Expr = curr[SHOT_SAMPLING_COL_P1].into();
        let u: AB::Expr = curr[SHOT_SAMPLING_COL_U].into();
        let outcome_e: AB::Expr = outcome.into();
        let gap: AB::Expr = curr[SHOT_SAMPLING_COL_GAP].into();
        let scale: AB::Expr = AB::F::from_u32(SHOT_SAMPLING_SCALE).into();

        let mut recomposed = AB::Expr::ZERO;
        let mut pow = AB::Expr::ONE;
        for i in 0..SHOT_SAMPLING_GAP_BITS {
            let bit = curr[SHOT_SAMPLING_COL_GAP_BITS + i];
            builder.when(active.clone()).assert_bool(bit);
            recomposed = recomposed + bit.into() * pow.clone();
            pow = pow.clone() + pow;
        }
        builder
            .when(active.clone())
            .assert_zero(gap.clone() - recomposed);

        let lhs = u * (p0.clone() + p1);
        let rhs = p0 * scale;
        let zero_branch = rhs.clone() - lhs.clone() - gap.clone() - AB::Expr::ONE;
        let one_branch = lhs - rhs - gap;
        builder
            .when(active.clone())
            .assert_zero((AB::Expr::ONE - outcome_e.clone()) * zero_branch);
        builder.when(active).assert_zero(outcome_e * one_branch);
    }
}

//! `RecursiveAggregationAir` — R3-M1 digest binding + R3-M2 AggregationAir statement columns.

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_field::{Field, PrimeCharacteristicRing};

use crate::plonky3_stark::aggregation_air::{AGG_LEFT_OK_COL, AGG_RIGHT_OK_COL, AGG_WIDTH};

/// M1 columns (0..132) + M2 AggregationAir natural rows / PCS commitments / pcs_ok.
pub const REC_AGG_WIDTH: usize = 330;

pub const REC_LEFT_OK_COL: usize = 64;
pub const REC_RIGHT_OK_COL: usize = 65;
pub const REC_LEFT_STARK_DIGEST_COL: usize = 66;
pub const REC_RIGHT_STARK_DIGEST_COL: usize = 98;
pub const REC_LEFT_KIND_COL: usize = 130;
pub const REC_RIGHT_KIND_COL: usize = 131;

pub const REC_LEFT_TRACE_COM_COL: usize = 132;
pub const REC_RIGHT_TRACE_COM_COL: usize = 164;
pub const REC_LEFT_AGG_ROW_COL: usize = 196;
pub const REC_RIGHT_AGG_ROW_COL: usize = 262;
pub const REC_LEFT_PCS_OK_COL: usize = 328;
pub const REC_RIGHT_PCS_OK_COL: usize = 329;

pub const REC_KIND_LEAF: u8 = 0;
pub const REC_KIND_AGG: u8 = 1;

/// Recursive aggregation AIR (R3-M1 + R3-M2 AggregationAir-sized PCS statement).
#[derive(Copy, Clone, Debug)]
pub struct RecursiveAggregationAir;

impl<F: Field> BaseAir<F> for RecursiveAggregationAir {
    fn width(&self) -> usize {
        REC_AGG_WIDTH
    }

    fn max_constraint_degree(&self) -> Option<usize> {
        Some(2)
    }
}

impl<AB: AirBuilder> Air<AB> for RecursiveAggregationAir
where
    AB::F: Field + PrimeCharacteristicRing,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let curr = main.current_slice();
        let next = main.next_slice();
        debug_assert_eq!(curr.len(), REC_AGG_WIDTH);
        debug_assert_eq!(next.len(), REC_AGG_WIDTH);

        let one = AB::Expr::ONE;
        let zero = AB::Expr::ZERO;

        builder
            .when_transition()
            .assert_zero(curr[REC_LEFT_OK_COL].into() - one.clone());
        builder
            .when_transition()
            .assert_zero(curr[REC_RIGHT_OK_COL].into() - one.clone());
        builder
            .when_transition()
            .assert_zero(curr[REC_LEFT_PCS_OK_COL].into() - one.clone());
        builder
            .when_transition()
            .assert_zero(curr[REC_RIGHT_PCS_OK_COL].into() - one.clone());

        let lk = curr[REC_LEFT_KIND_COL].into();
        let rk = curr[REC_RIGHT_KIND_COL].into();
        builder
            .when_transition()
            .assert_zero(lk.clone() * (lk.clone() - one.clone()));
        builder
            .when_transition()
            .assert_zero(rk.clone() * (rk.clone() - one.clone()));

        // kind=leaf ⇒ AggregationAir natural row + commitment are zero.
        let left_leaf = one.clone() - lk.clone();
        let right_leaf = one.clone() - rk.clone();
        for i in 0..32 {
            builder
                .when_transition()
                .assert_zero(left_leaf.clone() * curr[REC_LEFT_TRACE_COM_COL + i].into());
            builder
                .when_transition()
                .assert_zero(right_leaf.clone() * curr[REC_RIGHT_TRACE_COM_COL + i].into());
        }
        for i in 0..AGG_WIDTH {
            builder
                .when_transition()
                .assert_zero(left_leaf.clone() * curr[REC_LEFT_AGG_ROW_COL + i].into());
            builder
                .when_transition()
                .assert_zero(right_leaf.clone() * curr[REC_RIGHT_AGG_ROW_COL + i].into());
        }

        // kind=agg ⇒ AggregationAir OK flags on the natural row are 1.
        builder.when_transition().assert_zero(
            lk.clone() * (curr[REC_LEFT_AGG_ROW_COL + AGG_LEFT_OK_COL].into() - one.clone()),
        );
        builder
            .when_transition()
            .assert_zero(lk * (curr[REC_LEFT_AGG_ROW_COL + AGG_RIGHT_OK_COL].into() - one.clone()));
        builder.when_transition().assert_zero(
            rk.clone() * (curr[REC_RIGHT_AGG_ROW_COL + AGG_LEFT_OK_COL].into() - one.clone()),
        );
        builder.when_transition().assert_zero(
            rk * (curr[REC_RIGHT_AGG_ROW_COL + AGG_RIGHT_OK_COL].into() - one.clone()),
        );

        for col in 0..REC_AGG_WIDTH {
            if col == REC_LEFT_OK_COL
                || col == REC_RIGHT_OK_COL
                || col == REC_LEFT_PCS_OK_COL
                || col == REC_RIGHT_PCS_OK_COL
            {
                continue;
            }
            builder
                .when_transition()
                .assert_zero(next[col].into() - curr[col].into());
        }

        let _ = zero;
    }
}

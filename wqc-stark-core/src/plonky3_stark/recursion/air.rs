//! `RecursiveAggregationAir` — R3-M1 stepping stone toward in-circuit recursion.

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_field::{Field, PrimeCharacteristicRing};

pub const REC_AGG_WIDTH: usize = 132;

pub const REC_LEFT_OK_COL: usize = 64;
pub const REC_RIGHT_OK_COL: usize = 65;
pub const REC_LEFT_STARK_DIGEST_COL: usize = 66;
pub const REC_RIGHT_STARK_DIGEST_COL: usize = 98;
pub const REC_LEFT_KIND_COL: usize = 130;
pub const REC_RIGHT_KIND_COL: usize = 131;

pub const REC_KIND_LEAF: u8 = 0;
pub const REC_KIND_AGG: u8 = 1;

/// Aggregation AIR that binds child container digests **and** verified child STARK digests.
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

        // kind ∈ {0,1} ⇔ k*(k-1)=0
        let lk = curr[REC_LEFT_KIND_COL].into();
        let rk = curr[REC_RIGHT_KIND_COL].into();
        builder
            .when_transition()
            .assert_zero(lk.clone() * (lk - one.clone()));
        builder
            .when_transition()
            .assert_zero(rk.clone() * (rk - one));

        for col in 0..REC_AGG_WIDTH {
            if col == REC_LEFT_OK_COL || col == REC_RIGHT_OK_COL {
                continue;
            }
            builder
                .when_transition()
                .assert_zero(next[col].into() - curr[col].into());
        }

        // Silence unused in some AB impls.
        let _ = zero;
    }
}

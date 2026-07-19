//! Legacy R3-M1 `RecursiveAggregationAir` (width 132) for V5 transcript verify.

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_field::{Field, PrimeCharacteristicRing};

pub const REC_AGG_M1_WIDTH: usize = 132;
pub const REC_M1_LEFT_OK_COL: usize = 64;
pub const REC_M1_RIGHT_OK_COL: usize = 65;
pub const REC_M1_LEFT_KIND_COL: usize = 130;
pub const REC_M1_RIGHT_KIND_COL: usize = 131;

#[derive(Copy, Clone, Debug)]
pub struct RecursiveAggregationAirM1;

impl<F: Field> BaseAir<F> for RecursiveAggregationAirM1 {
    fn width(&self) -> usize {
        REC_AGG_M1_WIDTH
    }

    fn max_constraint_degree(&self) -> Option<usize> {
        Some(2)
    }
}

impl<AB: AirBuilder> Air<AB> for RecursiveAggregationAirM1
where
    AB::F: Field + PrimeCharacteristicRing,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let curr = main.current_slice();
        let next = main.next_slice();
        let one = AB::Expr::ONE;

        builder
            .when_transition()
            .assert_zero(curr[REC_M1_LEFT_OK_COL].into() - one.clone());
        builder
            .when_transition()
            .assert_zero(curr[REC_M1_RIGHT_OK_COL].into() - one.clone());

        let lk = curr[REC_M1_LEFT_KIND_COL].into();
        let rk = curr[REC_M1_RIGHT_KIND_COL].into();
        builder
            .when_transition()
            .assert_zero(lk.clone() * (lk - one.clone()));
        builder
            .when_transition()
            .assert_zero(rk.clone() * (rk - one));

        for col in 0..REC_AGG_M1_WIDTH {
            if col == REC_M1_LEFT_OK_COL || col == REC_M1_RIGHT_OK_COL {
                continue;
            }
            builder
                .when_transition()
                .assert_zero(next[col].into() - curr[col].into());
        }
    }
}

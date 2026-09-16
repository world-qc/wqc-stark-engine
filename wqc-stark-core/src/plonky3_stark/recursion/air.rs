//! `RecursiveAggregationAir` — R3-M1 digest binding + R3-M2 AggregationAir statement columns.

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_field::{Field, PrimeCharacteristicRing};

use crate::plonky3_stark::aggregation_air::{AGG_LEFT_OK_COL, AGG_RIGHT_OK_COL};

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

#[cfg(test)]
mod wrap_recagg_air_golden {
    use super::*;
    use crate::plonky3_stark::config::{Challenge, WqcStarkConfig};
    use crate::plonky3_stark::recursion::fri_fold_native::challenge_to_limbs;
    use p3_air::{Air, RowWindow};
    use p3_field::{PrimeCharacteristicRing, PrimeField32};
    use p3_matrix::dense::RowMajorMatrixView;
    use p3_matrix::stack::VerticalPair;
    use p3_mersenne_31::Mersenne31 as Val;
    use p3_uni_stark::VerifierConstraintFolder;

    fn fold_recagg(
        local: &[Challenge],
        next: &[Challenge],
        is_transition: Challenge,
        alpha: Challenge,
    ) -> Challenge {
        let main = VerticalPair::new(
            RowMajorMatrixView::new_row(local),
            RowMajorMatrixView::new_row(next),
        );
        let empty: &[Challenge] = &[];
        let preprocessed = VerticalPair::new(
            RowMajorMatrixView::new(empty, 0),
            RowMajorMatrixView::new(empty, 0),
        );
        let preprocessed_window = RowWindow::from_two_rows(empty, empty);
        let mut folder: VerifierConstraintFolder<'_, WqcStarkConfig> = VerifierConstraintFolder {
            main,
            preprocessed,
            preprocessed_window,
            periodic_values: &[],
            public_values: &[],
            is_first_row: Challenge::ZERO,
            is_last_row: Challenge::ZERO,
            is_transition,
            alpha,
            accumulator: Challenge::ZERO,
        };
        RecursiveAggregationAir.eval(&mut folder);
        folder.accumulator
    }

    #[test]
    fn emit_recagg_air_goldens() {
        let golden_path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../fixtures/e5b/wrap_recagg_air_golden.json"
        );
        let raw = std::fs::read_to_string(golden_path).expect("wrap_recagg_air_golden.json");
        let v: serde_json::Value = serde_json::from_str(&raw).expect("golden json");

        let mut local = vec![Challenge::ZERO; REC_AGG_WIDTH];
        for (i, item) in local.iter_mut().enumerate().take(REC_AGG_WIDTH) {
            *item = Challenge::new([
                Val::from_u32(((i * 17 + 3) % 251) as u32),
                Val::ZERO,
                Val::ZERO,
            ]);
        }
        local[REC_LEFT_OK_COL] = Challenge::ONE;
        local[REC_RIGHT_OK_COL] = Challenge::ONE;
        local[REC_LEFT_PCS_OK_COL] = Challenge::ONE;
        local[REC_RIGHT_PCS_OK_COL] = Challenge::ONE;
        local[REC_LEFT_KIND_COL] = Challenge::ZERO;
        local[REC_RIGHT_KIND_COL] = Challenge::ONE;
        local[REC_RIGHT_AGG_ROW_COL + AGG_LEFT_OK_COL] = Challenge::ONE;
        local[REC_RIGHT_AGG_ROW_COL + AGG_RIGHT_OK_COL] = Challenge::ONE;

        let mut next = local.clone();
        next[0] = Challenge::new([Val::from_u32(9), Val::ZERO, Val::ZERO]);

        let alpha = Challenge::new([Val::from_u32(9), Val::from_u32(2), Val::from_u32(3)]);
        let is_trans = Challenge::ONE;
        let inv_van = Challenge::new([Val::from_u32(3), Val::from_u32(4), Val::from_u32(5)]);
        let folded = fold_recagg(&local, &next, is_trans, alpha);
        let quot = folded * inv_van;
        let folded_l = challenge_to_limbs(folded);
        let quot_l = challenge_to_limbs(quot);

        let want_folded: Vec<u32> = v["folded"]
            .as_array()
            .unwrap()
            .iter()
            .map(|x| x.as_u64().unwrap() as u32)
            .collect();
        let want_quot: Vec<u32> = v["quotient"]
            .as_array()
            .unwrap()
            .iter()
            .map(|x| x.as_u64().unwrap() as u32)
            .collect();
        for i in 0..3 {
            assert_eq!(folded_l[i].as_canonical_u32(), want_folded[i]);
            assert_eq!(quot_l[i].as_canonical_u32(), want_quot[i]);
        }
    }
}

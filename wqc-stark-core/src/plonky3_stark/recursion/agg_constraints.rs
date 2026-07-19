//! Native AggregationAir constraint check — precursor for R3-M2 in-circuit gadgets.

use p3_field::PrimeCharacteristicRing;
use p3_mersenne_31::Mersenne31;

use crate::plonky3_stark::aggregation_air::{
    AggregationAir, AGG_LEFT_OK_COL, AGG_RIGHT_OK_COL, AGG_WIDTH,
};

/// Returns true when a 2-row AggregationAir matrix satisfies the R2 transition constraints.
pub fn aggregation_air_constraints_hold(row0: &[Mersenne31], row1: &[Mersenne31]) -> bool {
    if row0.len() != AGG_WIDTH || row1.len() != AGG_WIDTH {
        return false;
    }
    let one = Mersenne31::ONE;
    if row0[AGG_LEFT_OK_COL] != one || row0[AGG_RIGHT_OK_COL] != one {
        return false;
    }
    if row1[AGG_LEFT_OK_COL] != one || row1[AGG_RIGHT_OK_COL] != one {
        return false;
    }
    for col in 0..64 {
        if row0[col] != row1[col] {
            return false;
        }
    }
    let _ = AggregationAir;
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_field::PrimeCharacteristicRing;

    #[test]
    fn honest_agg_rows_pass() {
        let mut row = vec![Mersenne31::ZERO; AGG_WIDTH];
        for i in 0..64 {
            row[i] = Mersenne31::from_u32(i as u32);
        }
        row[AGG_LEFT_OK_COL] = Mersenne31::ONE;
        row[AGG_RIGHT_OK_COL] = Mersenne31::ONE;
        assert!(aggregation_air_constraints_hold(&row, &row));
    }

    #[test]
    fn bad_ok_flag_fails() {
        let row = vec![Mersenne31::ZERO; AGG_WIDTH];
        assert!(!aggregation_air_constraints_hold(&row, &row));
    }
}

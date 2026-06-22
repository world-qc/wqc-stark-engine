//! Plonky3 `Air` for proof-tree aggregation (R2).
//!
//! Binds SHA3-256 digests of two verified child proofs and attests that both
//! children passed native verification at compose time. This is the devnet R2
//! stepping stone toward full in-circuit STARK recursion (R3).

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_field::{Field, PrimeCharacteristicRing};

pub const AGG_WIDTH: usize = 66;
/// Columns `0..32`: left child digest bytes, `32..64`: right digest, `64..66`: verify flags.
pub const AGG_LEFT_HASH_COL: usize = 0;
pub const AGG_RIGHT_HASH_COL: usize = 32;
pub const AGG_LEFT_OK_COL: usize = 64;
pub const AGG_RIGHT_OK_COL: usize = 65;

/// Aggregation AIR used when pairing two child proofs in the proof tree.
#[derive(Copy, Clone, Debug)]
pub struct AggregationAir;

impl<F: Field> BaseAir<F> for AggregationAir {
    fn width(&self) -> usize {
        AGG_WIDTH
    }

    fn max_constraint_degree(&self) -> Option<usize> {
        Some(2)
    }
}

impl<AB: AirBuilder> Air<AB> for AggregationAir
where
    AB::F: Field,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let curr = main.current_slice();
        let next = main.next_slice();
        debug_assert_eq!(curr.len(), AGG_WIDTH);
        debug_assert_eq!(next.len(), AGG_WIDTH);

        let one = AB::Expr::ONE;

        // Both children must have been verified before proving.
        builder
            .when_transition()
            .assert_zero(curr[AGG_LEFT_OK_COL].into() - one.clone());
        builder
            .when_transition()
            .assert_zero(curr[AGG_RIGHT_OK_COL].into() - one);

        // Digest bytes are stable across the active aggregation row(s).
        for col in 0..64 {
            builder
                .when_transition()
                .assert_zero(next[col].into() - curr[col].into());
        }
    }
}

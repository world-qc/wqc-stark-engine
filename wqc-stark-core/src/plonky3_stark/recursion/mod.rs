//! R3-M1: recursive aggregation (child STARK digest binding).
//!
//! See `doc/R3_RECURSION.md`. Full FRI-in-circuit verification is M2+.

mod agg_constraints;
mod air;
mod child_binding;
mod context;
mod prove;
mod transcript_v5;

pub use agg_constraints::aggregation_air_constraints_hold;
pub use air::{
    RecursiveAggregationAir, REC_AGG_WIDTH, REC_KIND_AGG, REC_KIND_LEAF, REC_LEFT_KIND_COL,
    REC_LEFT_OK_COL, REC_LEFT_STARK_DIGEST_COL, REC_RIGHT_KIND_COL, REC_RIGHT_OK_COL,
    REC_RIGHT_STARK_DIGEST_COL,
};
pub use child_binding::{child_stark_binding, ChildStarkBinding, STARK_DIGEST_LEN};
pub use context::RecursiveAggregationContext;
pub use prove::{generate_recursive_aggregation_proof, verify_recursive_aggregation_proof};
pub use transcript_v5::{
    append_rec_tail, has_rec_tail, split_rec_tail, V5_REC_AGG_INNER_MARKER, V5_REC_TAIL_MARKER,
};

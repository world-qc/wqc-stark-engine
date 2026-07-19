//! R3-M1 / R3-M2 recursive aggregation.
//!
//! See `doc/R3_RECURSION.md`. Full FRI-in-circuit fold verification remains M2.5+.

mod agg_constraints;
mod air;
mod air_m1;
mod child_binding;
mod context;
mod opening_cert;
mod prove;
mod transcript_v5;
mod transcript_v6;

pub use agg_constraints::aggregation_air_constraints_hold;
pub use air::{
    RecursiveAggregationAir, REC_AGG_WIDTH, REC_KIND_AGG, REC_KIND_LEAF, REC_LEFT_KIND_COL,
    REC_LEFT_OK_COL, REC_LEFT_STARK_DIGEST_COL, REC_RIGHT_KIND_COL, REC_RIGHT_OK_COL,
    REC_RIGHT_STARK_DIGEST_COL,
};
pub use child_binding::{child_stark_binding, ChildStarkBinding, STARK_DIGEST_LEN};
pub use context::RecursiveAggregationContext;
pub use opening_cert::{
    build_agg_pcs_certificate, child_aggregation_transcript, parse_agg_v4_header,
    parse_agg_v4_header_any, verify_agg_pcs_certificate, AggPcsCertificate,
};
pub use prove::{
    append_rec_tail, generate_recursive_aggregation_proof, has_rec_tail, split_rec_tail,
    verify_recursive_aggregation_proof,
};
pub use transcript_v5::{V5_REC_AGG_INNER_MARKER, V5_REC_TAIL_MARKER};
pub use transcript_v6::{V6_REC_AGG_INNER_MARKER, V6_REC_TAIL_MARKER};

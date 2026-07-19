//! Shared context for R3 recursive aggregation (M1 + M2).

use crate::aggregation::CHILD_HASH_LEN;

use super::child_binding::STARK_DIGEST_LEN;
use super::opening_cert::AggPcsCertificate;

/// Public binding for an R3 recursive aggregation STARK.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecursiveAggregationContext<'a> {
    pub parent_task_id: &'a str,
    pub compose_label: &'a str,
    pub manifest_root_hash: &'a str,
    pub left_child_hash: [u8; CHILD_HASH_LEN],
    pub right_child_hash: [u8; CHILD_HASH_LEN],
    pub left_stark_digest: [u8; STARK_DIGEST_LEN],
    pub right_stark_digest: [u8; STARK_DIGEST_LEN],
    pub left_kind: u8,
    pub right_kind: u8,
    /// R3-M2: AggregationAir PCS certificates when `*_kind == AGG`.
    pub left_agg_cert: Option<AggPcsCertificate>,
    pub right_agg_cert: Option<AggPcsCertificate>,
}

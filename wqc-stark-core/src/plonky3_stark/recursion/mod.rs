//! R3 recursive aggregation (M1–M3e).
//!
//! Protocol: `wqc-docs/spec/zk-STARK.md` §8. Module map: crate README.

mod agg_constraints;
mod air;
mod air_m1;
mod child_binding;
mod context;
mod deep_ro_air;
mod deep_ro_bind;
mod deep_ro_leaf_trace_air;
mod deep_ro_native;
mod deep_ro_trace_air;
mod ef_limbs;
mod fri_fold_air;
mod fri_fold_bind;
mod fri_fold_native;
mod fri_fs_replay;
mod fri_mmcs;
mod fri_mmcs_bind;
mod fri_mmcs_group_m4b;
mod fri_mmcs_m4c;
mod fri_mmcs_path;
mod fri_mmcs_path_m4a;
mod fri_ood;
mod fri_ro;
mod keccak256_air;
mod keccak_f_air;
mod keccak_f_native;
mod keccak_merkle_air;
mod leaf_pcs_cert;
mod merkle_keccak;
mod ood_air;
mod ood_bind;
mod ood_fold;
mod ood_leaf_fold;
mod ood_native;
mod opening_cert;
mod pcs_geom;
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
pub use deep_ro_air::{generate_deep_ro_proof, verify_deep_ro_proof, DeepRoAir, DeepRoStepProof};
pub use deep_ro_bind::{
    bind_deep_ro_bundle_to_proof, bind_deep_ro_leaf_bundle_to_proof, bind_deep_ro_to_fold_y,
    bind_deep_ro_trace_to_fold_y, deep_ro_bundle_from_agg_proof, deep_ro_bundle_from_leaf_proof,
    deep_ro_quot_from_agg_proof, deep_ro_quot_query0_from_agg_proof, deep_ro_trace_from_agg_proof,
    deep_ro_trace_query0_from_agg_proof, AggDeepRoBundle, LeafDeepRoBundle, AGG_DEEP_RO_MAX,
    AGG_DEEP_RO_TRACE_MAX,
};
pub use deep_ro_leaf_trace_air::{
    generate_deep_ro_leaf_trace_proof, verify_deep_ro_leaf_trace_proof, DeepRoLeafTraceAir,
    DeepRoLeafTraceStepProof,
};
pub use deep_ro_trace_air::{
    generate_deep_ro_trace_proof, verify_deep_ro_trace_proof, DeepRoTraceAir, DeepRoTraceStepProof,
};
pub use fri_fold_air::{
    generate_fri_fold_proof, generate_fri_fold_y_proof, verify_fri_fold_proof,
    verify_fri_fold_y_proof, FriFoldAir, FriFoldStepProof,
};
pub use fri_fold_bind::{
    bind_fri_fold_bundle_to_proof, bind_fri_fold_bundle_to_proof_width,
    covers_all_devnet_fri_queries, fri_fold_bundle_from_agg_proof, fri_fold_bundle_from_proof,
    fri_fold_steps_from_agg_proof, AggFriFoldBundle, AGG_FRI_PROVEN_QUERIES,
    LEAF_FRI_PROVEN_QUERIES,
};
pub use fri_fs_replay::{replay_agg_fri_challenges, replay_fri_challenges, AggFriChallenges};
pub use fri_mmcs::verify_agg_fri_openings;
pub use fri_mmcs_bind::{
    bind_fri_chal_mmcs_bundle, bind_fri_mmcs_bundle_to_proof, bind_fri_mmcs_bundle_to_proof_width,
    bind_fri_val_mmcs_bundle, fri_chal_mmcs_bundle_from_agg_proof, fri_mmcs_bundle_from_agg_proof,
    fri_mmcs_bundle_from_agg_proof_drop_nested, fri_mmcs_bundle_from_proof,
    fri_mmcs_bundle_from_proof_drop_nested, fri_val_mmcs_bundle_from_agg_proof, AggFriMmcsBundle,
    FriChalBatchPathProof, FriChalMmcsQueryProof, FriValMmcsQueryProof,
};
pub use fri_mmcs_group_m4b::{
    generate_keccak_group_fold_proof, verify_keccak_group_fold_proof, KeccakGroupFoldProof,
    MmcsGroupPathAir, MmcsPathStatement,
};
pub use fri_mmcs_m4c::{LeafMmcsFoldGroups, LEAF_MMCS_FOLD_V};
pub use fri_mmcs_path::{
    generate_fri_mmcs_path_proof, generate_fri_mmcs_path_proof_drop_nested,
    verify_fri_mmcs_path_proof, FriMmcsFoldAir, FriMmcsPathProof, FRI_MMCS_MAX_DEPTH,
};
pub use fri_mmcs_path_m4a::{
    generate_fri_mmcs_batched_path_proof, verify_fri_mmcs_batched_path_proof,
    FriMmcsBatchedPathProof, MmcsBatchedPathAir,
};
pub use fri_ood::{verify_agg_ood, verify_leaf_ood, verify_ood_for_air};
pub use keccak256_air::{
    prove_compress, prove_keccak256, prove_lde_leaf, verify_compress_digest, verify_keccak256,
    verify_lde_leaf_digest, Keccak256SpongeAir, Keccak256StarkProof,
};
pub use keccak_f_air::{apply_round_bits, KeccakFRoundAir, KECCAK_F_WIDTH};
pub use keccak_f_native::{keccak256, keccak256_compress, keccak256_lde_leaf};
pub use keccak_merkle_air::{
    generate_keccak_merkle_path_proof, verify_keccak_merkle_path_proof, KeccakMerklePathProof,
    MerkleFoldAir, MERKLE_FOLD_DEPTH,
};
pub use leaf_pcs_cert::{
    build_encoded_leaf_pcs_bundle_from_child, build_leaf_pcs_bundle_from_child,
    build_leaf_pcs_certificate, leaf_bundle_stark_sizes, leaf_bundle_stmt_digest,
    leaf_pcs_stark_sizes, leaf_stmt_digest, verify_leaf_pcs_bundle, verify_leaf_pcs_certificate,
    LeafPcsBundle, LeafPcsCertificate, LeafPcsStarkSizes,
};
pub use merkle_keccak::{
    compress_digests, hash_lde_leaf, verify_agg_merkle_path, AGG_LDE_MERKLE_DEPTH,
};
pub use ood_air::{
    generate_ood_proof, verify_ood_proof, OodAirKind, OodCheckAir, OodStepProof,
    OOD_MAX_TRACE_WIDTH,
};
pub use ood_bind::{
    bind_leaf_ood_to_proof, bind_ood_to_proof, verify_agg_ood_step, verify_leaf_ood_step,
    verify_ood_step_bound,
};
pub use ood_native::{
    extract_agg_ood_witness, extract_leaf_ood_witness, generate_agg_ood_proof,
    generate_leaf_ood_proof, generate_ood_proof_from_witness, ood_kind_for_leaf, OodWitness,
};
pub use opening_cert::{
    build_agg_pcs_certificate, child_aggregation_transcript, parse_agg_v4_header,
    parse_agg_v4_header_any, verify_agg_pcs_certificate, AggPcsCertificate,
};
pub use pcs_geom::{
    born_distribution_width, born_num_outcomes_from_width, born_recursion_outcomes_ok,
    validate_born_recursion_outcomes, validate_born_recursion_width, LeafKind, PcsGeom,
    BORN_RECURSION_MAX_OUTCOMES, BORN_RECURSION_MAX_TRACE_WIDTH, LEAF_DEEP_RO_MAX_WIDTH,
    SHOT_TRACE_WIDTH, TRAJ_MARGINAL_TRACE_WIDTH, UNITARY_TRACE_WIDTH,
};
pub use prove::{
    append_rec_tail, generate_recursive_aggregation_proof, has_rec_tail, split_rec_tail,
    verify_recursive_aggregation_proof,
};
pub use transcript_v5::{V5_REC_AGG_INNER_MARKER, V5_REC_TAIL_MARKER};
pub use transcript_v6::{
    decode_leaf_bundle, decode_leaf_pcs_bundle_bytes, encode_leaf_bundle,
    encode_leaf_pcs_bundle_bytes, V6_REC_AGG_INNER_MARKER, V6_REC_TAIL_MARKER,
};
#[cfg(test)]
pub use transcript_v6::{decode_rec_agg_proof_owned_v6, diagnose_decode_rec_agg_v6};

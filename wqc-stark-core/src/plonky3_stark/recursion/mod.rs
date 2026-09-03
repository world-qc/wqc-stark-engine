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
mod fri_fold_group;
mod fri_fold_m4c;
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
mod mmcs_group_fold;
mod merkle_poseidon2;
mod ood_air;
mod ood_bind;
mod ood_fold;
mod ood_leaf_fold;
mod ood_native;
mod opening_cert;
mod pcs_geom;
mod pcs_memory;
mod poseidon2_spike;
mod poseidon2_perm_air;
mod poseidon2_group_m4b;
mod poseidon_merkle_migration;
mod prove;
mod prove_workspace;
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
    fri_fold_step_limbs_x, fri_fold_step_limbs_y, generate_fri_fold_proof,
    generate_fri_fold_y_proof, verify_fri_fold_proof, verify_fri_fold_x_native,
    verify_fri_fold_y_native, verify_fri_fold_y_proof, FriFoldAir, FriFoldStepProof,
};
pub use fri_fold_bind::{
    bind_fri_fold_bundle_to_proof, bind_fri_fold_bundle_to_proof_width,
    covers_all_devnet_fri_queries, fri_fold_bundle_from_agg_proof, fri_fold_bundle_from_proof,
    fri_fold_steps_from_agg_proof, AggFriFoldBundle, AGG_FRI_PROVEN_QUERIES,
    LEAF_FRI_PROVEN_QUERIES, MAX_FRI_PROVEN_QUERIES,
};
pub use fri_fold_group::{
    generate_fri_fold_group_proof, generate_fri_fold_group_proof_with_queries,
    verify_fri_fold_group_proof, FriFoldGroupAir, FriFoldGroupProof, FRI_FOLD_GROUP_MAX_STEPS,
    FRI_FOLD_KIND_X, FRI_FOLD_KIND_Y,
};
pub use fri_fold_m4c::{
    apply_leaf_fri_fold_m4c_folds, apply_leaf_fri_fold_m4c_folds_with_queries,
    bind_fri_fold_with_groups, LeafFriFoldGroups, LEAF_FRI_FOLD_V,
};
pub use fri_fs_replay::{
    circle_config_matching_proof, fri_queries_from_proof, replay_agg_fri_challenges,
    replay_fri_challenges, AggFriChallenges,
};
pub use fri_mmcs::verify_agg_fri_openings;
pub use fri_mmcs_bind::{
    bind_fri_chal_mmcs_bundle, bind_fri_mmcs_bundle_to_proof, bind_fri_mmcs_bundle_to_proof_width,
    bind_fri_val_mmcs_bundle, fri_chal_mmcs_bundle_from_agg_proof, fri_mmcs_bundle_from_agg_proof,
    fri_mmcs_bundle_from_agg_proof_drop_nested, fri_mmcs_bundle_from_proof,
    fri_mmcs_bundle_from_proof_drop_nested, fri_val_mmcs_bundle_from_agg_proof, AggFriMmcsBundle,
    FriChalBatchPathProof, FriChalMmcsQueryProof, FriValMmcsQueryProof,
};
pub use fri_mmcs_group_m4b::{
    generate_keccak_group_fold_proof, generate_keccak_group_fold_proof_with_queries,
    verify_keccak_group_fold_proof, KeccakGroupFoldProof, MmcsGroupPathAir, MmcsPathStatement,
};
pub use fri_mmcs_m4c::{
    apply_leaf_mmcs_m4c_folds, benchmark_poseidon_mmcs_groups, collect_leaf_mmcs_group_statements,
    bind_leaf_mmcs_with_groups, chal_mmcs_sibling_wire_bytes, hydrate_chal_mmcs_siblings_from_proof,
    hydrate_val_mmcs_siblings_from_proof, mmcs_sibling_strip_enabled,
    strip_chal_mmcs_siblings_for_groups, strip_val_mmcs_siblings_for_groups,
    val_mmcs_sibling_wire_bytes, LeafMmcsFoldGroups, LeafMmcsGroupStatements,
    PCS_STRIP_MMCS_SIBLINGS_ENV, PoseidonMmcsBenchmarkReport, LEAF_MMCS_FOLD_V, LEAF_MMCS_FOLD_V4,
};
pub use fri_mmcs_path::{
    generate_fri_mmcs_path_proof, generate_fri_mmcs_path_proof_drop_nested,
    verify_fri_mmcs_path_proof, FriMmcsPathProof, FRI_MMCS_MAX_DEPTH,
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
    benchmark_poseidon_mmcs_from_child, build_encoded_leaf_pcs_bundle_from_child,
    build_leaf_pcs_bundle_from_child, build_leaf_pcs_certificate, leaf_bundle_stark_sizes,
    leaf_bundle_stmt_digest, leaf_pcs_stark_sizes, leaf_stmt_digest, verify_leaf_pcs_bundle,
    verify_leaf_pcs_certificate, LeafPcsBundle, LeafPcsCertificate, LeafPcsStarkSizes,
};
pub use mmcs_group_fold::{
    mmcs_group_hash_kind, poseidon_group_width_supported, MmcsGroupFoldProof, MmcsGroupHashKind,
    MMCS_GROUP_HASH_KECCAK, MMCS_GROUP_HASH_POSEIDON, PCS_MMCS_HASH_ENV,
};
pub use merkle_keccak::{
    compress_digests, hash_lde_leaf, hash_val_leaf, verify_agg_merkle_path, AGG_LDE_MERKLE_DEPTH,
};
pub use merkle_poseidon2::{
    compress_digests_poseidon, hash_val_leaf_poseidon, merkle_root_from_path_poseidon,
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
pub use poseidon2_perm_air::{
    generate_poseidon2_perm_proof, verify_poseidon2_perm_proof, Poseidon2PermAir,
    POSEIDON2_PERM_ROWS, POSEIDON2_PERM_WIDTH,
};
pub use poseidon2_group_m4b::{
    generate_poseidon_group_fold_proof, generate_poseidon_group_fold_proof_with_queries,
    verify_poseidon_group_fold_proof, PoseidonGroupFoldProof, PoseidonMmcsGroupPathAir,
};
pub use poseidon_merkle_migration::{
    mmcs_merkle_mode, poseidon_group_spike_active, poseidon_native_mmcs_active, MmcsMerkleMode,
};
pub use pcs_memory::{
    budget_bytes_from_env, estimate_pcs_peak_bytes, plan_pcs_memory, PcsMemoryPlan,
    PcsMemoryPolicy, PCS_MEMORY_ERR_PREFIX,
};
pub use prove::{
    append_rec_tail, generate_recursive_aggregation_proof, has_rec_tail, split_rec_tail,
    verify_recursive_aggregation_proof,
};
pub use transcript_v5::{V5_REC_AGG_INNER_MARKER, V5_REC_TAIL_MARKER};
pub use transcript_v6::{
    decode_leaf_bundle, decode_leaf_pcs_bundle_bytes, encode_leaf_bundle,
    encode_leaf_pcs_bundle_bytes, parse_rec_agg_sides_v6, RecAggSidesV6, V6_REC_AGG_INNER_MARKER,
    V6_REC_TAIL_MARKER,
};
#[cfg(test)]
pub use transcript_v6::{decode_rec_agg_proof_owned_v6, diagnose_decode_rec_agg_v6};

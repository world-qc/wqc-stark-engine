//! R3 recursive aggregation (M1–M3b2).
//!
//! See `doc/R3_RECURSION.md`.

mod agg_constraints;
mod air;
mod air_m1;
mod child_binding;
mod context;
mod fri_fold_air;
mod fri_fold_bind;
mod fri_fold_native;
mod fri_fs_replay;
mod fri_ro;
mod keccak256_air;
mod keccak_f_air;
mod keccak_f_native;
mod keccak_merkle_air;
mod merkle_keccak;
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
pub use fri_fold_air::{
    generate_fri_fold_proof, generate_fri_fold_y_proof, verify_fri_fold_proof,
    verify_fri_fold_y_proof, FriFoldAir, FriFoldStepProof,
};
pub use fri_fold_bind::{
    fri_fold_bundle_from_agg_proof, fri_fold_steps_from_agg_proof, AggFriFoldBundle,
    AGG_FRI_PROVEN_QUERIES,
};
pub use fri_fs_replay::{replay_agg_fri_challenges, AggFriChallenges};
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
pub use merkle_keccak::{
    compress_digests, hash_lde_leaf, verify_agg_merkle_path, AGG_LDE_MERKLE_DEPTH,
};
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

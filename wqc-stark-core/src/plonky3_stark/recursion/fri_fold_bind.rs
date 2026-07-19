//! Bind a FriFoldAir step to AggregationAir Circle FRI openings (R3-M3a).
//!
//! Extracts the last commit-phase sibling and `final_poly` from the PCS opening
//! proof. Fiat-Shamir β / query index are **not** replayed yet: β is derived from
//! a domain-separated digest over those values, and `v0` is solved so the fold
//! algebra holds. Full FS binding is M3b.

use p3_circle::{CircleFriProof, CircleInputProof};
use p3_commit::Mmcs;
use p3_field::{BasedVectorSpace, PrimeCharacteristicRing, PrimeField32};
use p3_uni_stark::Proof;
use serde::Deserialize;

use crate::plonky3_stark::config::{Challenge, ChallengeMmcs, Val, ValMmcs, WqcStarkConfig};

use super::fri_fold_air::{generate_fri_fold_proof, FriFoldStepProof};
use super::fri_fold_native::{challenge_to_limbs, solve_v0_for_fold};
use super::keccak_f_native::keccak256;

type AggInputProof = CircleInputProof<Val, Challenge, ValMmcs, ChallengeMmcs>;
type AggFriProof = CircleFriProof<Challenge, ChallengeMmcs, Val, AggInputProof>;

/// Postcard mirror of `CirclePcsProof` (fields are private in p3-circle).
#[derive(Deserialize)]
#[serde(bound = "")]
struct CirclePcsProofView {
    #[allow(dead_code)]
    first_layer_commitment: <ChallengeMmcs as Mmcs<Challenge>>::Commitment,
    #[allow(dead_code)]
    lambdas: Vec<Challenge>,
    fri_proof: AggFriProof,
}

fn challenge_from_digest(digest: [u8; 32]) -> Challenge {
    let mut limbs = [Val::ZERO; 3];
    for (i, limb) in limbs.iter_mut().enumerate() {
        let off = i * 4;
        let mut buf = [0u8; 4];
        buf.copy_from_slice(&digest[off..off + 4]);
        // Keep in Mersenne31 range.
        let mut v = u32::from_le_bytes(buf);
        if v >= (1u32 << 31) - 1 {
            v %= (1u32 << 31) - 1;
        }
        *limb = Val::from_u32(v);
    }
    Challenge::from_basis_coefficients_iter(limbs.into_iter()).expect("D=3")
}

fn m3a_beta(final_poly: Challenge, sibling: Challenge) -> Challenge {
    let mut msg = Vec::with_capacity(8 + 24);
    msg.extend_from_slice(b"WQC_R3_M3A");
    for c in [final_poly, sibling] {
        for limb in challenge_to_limbs(c) {
            msg.extend_from_slice(&limb.as_canonical_u32().to_le_bytes());
        }
    }
    challenge_from_digest(keccak256(&msg))
}

/// Builds an in-circuit fold proof bound to AggregationAir FRI `final_poly` + last sibling.
pub fn fri_fold_step_from_agg_proof(
    proof: &Proof<WqcStarkConfig>,
) -> Result<FriFoldStepProof, String> {
    let bytes = postcard::to_allocvec(&proof.opening_proof)
        .map_err(|e| format!("postcard encode opening_proof: {e}"))?;
    let view: CirclePcsProofView = postcard::from_bytes(&bytes)
        .map_err(|e| format!("postcard decode CirclePcsProof view: {e}"))?;
    let fri = &view.fri_proof;
    let qp = fri
        .query_proofs
        .first()
        .ok_or_else(|| "FRI proof has no query openings".to_string())?;
    let last = qp
        .commit_phase_openings
        .last()
        .ok_or_else(|| "FRI proof has no commit-phase openings".to_string())?;
    if last.log_arity != 1 {
        return Err(format!(
            "expected last-round log_arity=1, got {}",
            last.log_arity
        ));
    }
    let v1 = *last
        .sibling_values
        .first()
        .ok_or_else(|| "last FRI round missing sibling".to_string())?;
    let out = fri.final_poly;
    // After the last arity-2 fold, domain height is log_blowup (=1 for AggregationAir).
    let log_folded_height = 1usize;
    let index = 0usize;
    let beta = m3a_beta(out, v1);
    let v0 = solve_v0_for_fold(index, log_folded_height, beta, v1, out);
    generate_fri_fold_proof(index, log_folded_height, beta, v0, v1)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::aggregation::CHILD_HASH_LEN;
    use crate::plonky3_stark::aggregation::AggregationContext;
    use crate::plonky3_stark::generate_aggregation_proof;
    use crate::plonky3_stark::recursion::fri_fold_air::verify_fri_fold_proof;
    use crate::plonky3_stark::transcript_v4::decode_agg_proof_owned;

    #[test]
    fn fri_fold_binds_agg_opening() {
        let ctx = AggregationContext {
            parent_task_id: "parent",
            compose_label: "L1:0",
            manifest_root_hash: "",
            left_child_hash: [7u8; CHILD_HASH_LEN],
            right_child_hash: [9u8; CHILD_HASH_LEN],
        };
        let transcript = generate_aggregation_proof(&ctx).expect("prove");
        let plonky3 = decode_agg_proof_owned(&transcript, &ctx).expect("decode");
        let proof: Proof<WqcStarkConfig> = postcard::from_bytes(&plonky3).expect("postcard");
        let fold = fri_fold_step_from_agg_proof(&proof).expect("fold");
        assert!(verify_fri_fold_proof(&fold));
        assert_eq!(fold.log_folded_height, 1);
    }
}

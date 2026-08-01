//! Host OOD constraint check for AggregationAir / leaf AIRs (R3-M3b4 / M3e).
//!
//! Mirrors the uni-STARK verifier's `recompose_quotient_from_chunks` +
//! `verify_constraints` without invoking Circle PCS / FRI.

use p3_air::{Air, BaseAir};
use p3_commit::{Pcs, PolynomialSpace};
use p3_field::{BasedVectorSpace, Field};
use p3_uni_stark::{
    get_log_num_quotient_chunks, recompose_quotient_from_chunks, verify_constraints, AirLayout,
    Proof, StarkGenericConfig, SymbolicAirBuilder, VerifierConstraintFolder,
};

use crate::plonky3_stark::aggregation_air::AggregationAir;
use crate::plonky3_stark::config::{devnet_circle_config, Challenge, Val, WqcStarkConfig};

use super::fri_fs_replay::replay_fri_challenges;

/// Verifies AIR constraints at ζ against the claimed quotient opening for any uni-STARK.
pub fn verify_ood_for_air<A>(proof: &Proof<WqcStarkConfig>, air: &A) -> Result<(), String>
where
    A: BaseAir<Val>
        + Air<SymbolicAirBuilder<Val>>
        + for<'a> Air<VerifierConstraintFolder<'a, WqcStarkConfig>>,
{
    let width = <A as BaseAir<Val>>::width(air);
    let chal = replay_fri_challenges(proof, width)?;
    let config = devnet_circle_config();
    let pcs = config.pcs();

    let degree = 1usize << proof.degree_bits;
    let init_trace_domain = <crate::plonky3_stark::config::Pcs as Pcs<
        Challenge,
        crate::plonky3_stark::config::Challenger,
    >>::natural_domain_for_degree(pcs, degree);

    if init_trace_domain
        .vanishing_poly_at_point(chal.zeta)
        .is_zero()
    {
        return Err("OOD point ζ lies on the trace domain".into());
    }

    let layout = AirLayout {
        preprocessed_width: 0,
        main_width: width,
        num_public_values: air.num_public_values(),
        num_periodic_columns: 0,
        ..Default::default()
    };
    let log_num_quotient_chunks = get_log_num_quotient_chunks::<Val, A>(air, layout, 0);
    let num_quotient_chunks = 1usize << log_num_quotient_chunks;
    if proof.opened_values.quotient_chunks.len() != num_quotient_chunks {
        return Err(format!(
            "quotient chunk count {} != expected {}",
            proof.opened_values.quotient_chunks.len(),
            num_quotient_chunks
        ));
    }
    if proof
        .opened_values
        .quotient_chunks
        .iter()
        .any(|c| c.len() != <Challenge as BasedVectorSpace<Val>>::DIMENSION)
    {
        return Err("quotient chunk width != Challenge::DIMENSION".into());
    }

    let quotient_domain_size = 1usize << (proof.degree_bits + log_num_quotient_chunks);
    let quotient_domain = init_trace_domain.create_disjoint_domain(quotient_domain_size);
    let quotient_chunks_domains = quotient_domain.split_domains(num_quotient_chunks);

    let quotient = recompose_quotient_from_chunks::<WqcStarkConfig>(
        &quotient_chunks_domains,
        &proof.opened_values.quotient_chunks,
        chal.zeta,
    );

    let trace_next = proof
        .opened_values
        .trace_next
        .as_ref()
        .ok_or_else(|| "missing trace_next openings".to_string())?;

    verify_constraints::<WqcStarkConfig, A, ()>(
        air,
        &proof.opened_values.trace_local,
        trace_next,
        None,
        None,
        &[],
        &[],
        init_trace_domain,
        chal.zeta,
        chal.constraint_alpha,
        quotient,
    )
    .map_err(|e| format!("AIR OOD mismatch: {e:?}"))
}

/// Verifies AggregationAir constraints at ζ against the claimed quotient opening.
pub fn verify_agg_ood(proof: &Proof<WqcStarkConfig>) -> Result<(), String> {
    verify_ood_for_air(proof, &AggregationAir).map_err(|e| {
        if e.starts_with("AIR OOD") {
            e.replacen("AIR OOD", "AggregationAir OOD", 1)
        } else {
            e
        }
    })
}

/// Leaf OOD helper: same as [`verify_ood_for_air`].
pub fn verify_leaf_ood<A>(proof: &Proof<WqcStarkConfig>, air: &A) -> Result<(), String>
where
    A: BaseAir<Val>
        + Air<SymbolicAirBuilder<Val>>
        + for<'a> Air<VerifierConstraintFolder<'a, WqcStarkConfig>>,
{
    verify_ood_for_air(proof, air)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::aggregation::CHILD_HASH_LEN;
    use crate::plonky3_stark::aggregation::AggregationContext;
    use crate::plonky3_stark::generate_aggregation_proof;
    use crate::plonky3_stark::quantum_air::QuantumExecutionAir;
    use crate::plonky3_stark::transcript_v4::decode_agg_proof_owned;
    use crate::plonky3_stark::{decode_proof_v2_plonky3_bytes, generate_plonky3_proof};
    use crate::transcript::StarkContext;

    #[test]
    fn honest_aggregation_ood_passes() {
        let ctx = AggregationContext {
            parent_task_id: "parent",
            compose_label: "L1:0",
            manifest_root_hash: "",
            left_child_hash: [11u8; CHILD_HASH_LEN],
            right_child_hash: [13u8; CHILD_HASH_LEN],
            security_level: "",
        };
        let transcript = generate_aggregation_proof(&ctx).expect("prove");
        let plonky3 = decode_agg_proof_owned(&transcript, &ctx).expect("decode");
        let proof: Proof<WqcStarkConfig> = postcard::from_bytes(&plonky3).expect("postcard");
        verify_agg_ood(&proof).expect("ood");
    }

    #[test]
    fn honest_unitary_leaf_ood_passes() {
        let ctx = StarkContext {
            circuit_id: "c",
            sub_task_id: "sub-ood",
            node_id: "n1",
            slice_id: "0",
            output_hash: "out",
            terminal_statevector_digest: "",
            measurement_spec_hash: "",
            security_level: "",
        };
        let trace = crate::trace_spec::idle_qubit0_trace();
        let transcript = generate_plonky3_proof(&ctx, &trace).expect("prove");
        let plonky3 = decode_proof_v2_plonky3_bytes(&transcript, &ctx).expect("decode");
        let proof: Proof<WqcStarkConfig> = postcard::from_bytes(&plonky3).expect("postcard");
        verify_leaf_ood(&proof, &QuantumExecutionAir).expect("leaf ood");
    }
}

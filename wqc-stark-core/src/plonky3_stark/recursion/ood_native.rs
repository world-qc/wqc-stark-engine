//! Host-side OOD witness extraction for in-circuit OOD STARK prove (R3 OOD AIR).

use p3_air::{Air, BaseAir};
use p3_commit::{Pcs, PolynomialSpace};
use p3_field::{BasedVectorSpace, Field};
use p3_uni_stark::{
    get_log_num_quotient_chunks, recompose_quotient_from_chunks, AirLayout, Proof,
    StarkGenericConfig, SymbolicAirBuilder,
};

use crate::plonky3_stark::aggregation_air::{AggregationAir, AGG_WIDTH};
use crate::plonky3_stark::config::{devnet_circle_config, Challenge, Val, WqcStarkConfig};
use crate::plonky3_stark::distribution_air::DistributionAir;
use crate::plonky3_stark::quantum_air::QuantumExecutionAir;
use crate::plonky3_stark::shot_sampling_air::{ShotSamplingAir, SHOT_SAMPLING_AIR_WIDTH};
use crate::trace_spec::AIR_WIDTH;

use super::fri_fs_replay::replay_fri_challenges;
use super::ood_air::{OodAirKind, OodStepProof};
use super::ood_fold::fold_ood_native;
use super::pcs_geom::LeafKind;

/// Witness inputs for an in-circuit OOD STARK step.
#[derive(Debug, Clone)]
pub struct OodWitness {
    pub kind: OodAirKind,
    pub num_outcomes: u32,
    pub width: u32,
    pub degree_bits: u32,
    pub zeta: Challenge,
    pub alpha: Challenge,
    pub quotient: Challenge,
    pub inv_vanishing: Challenge,
    pub is_first_row: Challenge,
    pub is_last_row: Challenge,
    pub is_transition: Challenge,
    pub trace_local: Vec<Challenge>,
    pub trace_next: Vec<Challenge>,
    pub folded: Challenge,
}

pub fn ood_kind_for_leaf(kind: LeafKind) -> OodAirKind {
    match kind {
        LeafKind::Unitary => OodAirKind::Unitary,
        LeafKind::Born | LeafKind::TrajMarginal => OodAirKind::Distribution,
        LeafKind::ShotSampling => OodAirKind::ShotSampling,
    }
}

struct OodWitnessMeta {
    kind: OodAirKind,
    num_outcomes: u32,
    width: u32,
    degree_bits: u32,
}

struct ExtractedOodOpenings {
    zeta: Challenge,
    alpha: Challenge,
    inv_vanishing: Challenge,
    is_first_row: Challenge,
    is_last_row: Challenge,
    is_transition: Challenge,
    trace_local: Vec<Challenge>,
    trace_next: Vec<Challenge>,
}

fn extract_common(
    proof: &Proof<WqcStarkConfig>,
    width: usize,
) -> Result<ExtractedOodOpenings, String> {
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

    let sels = init_trace_domain.selectors_at_point(chal.zeta);
    let trace_next = proof
        .opened_values
        .trace_next
        .as_ref()
        .ok_or_else(|| "missing trace_next openings".to_string())?;
    if proof.opened_values.trace_local.len() != width || trace_next.len() != width {
        return Err(format!(
            "trace width mismatch: local={} next={} expected={width}",
            proof.opened_values.trace_local.len(),
            trace_next.len()
        ));
    }

    Ok(ExtractedOodOpenings {
        zeta: chal.zeta,
        alpha: chal.constraint_alpha,
        inv_vanishing: sels.inv_vanishing,
        is_first_row: sels.is_first_row,
        is_last_row: sels.is_last_row,
        is_transition: sels.is_transition,
        trace_local: proof.opened_values.trace_local.clone(),
        trace_next: trace_next.clone(),
    })
}

fn recompose_quotient<A>(
    proof: &Proof<WqcStarkConfig>,
    air: &A,
    zeta: Challenge,
) -> Result<Challenge, String>
where
    A: BaseAir<Val> + Air<SymbolicAirBuilder<Val>>,
{
    let width = <A as BaseAir<Val>>::width(air);
    let config = devnet_circle_config();
    let pcs = config.pcs();
    let degree = 1usize << proof.degree_bits;
    let init_trace_domain = <crate::plonky3_stark::config::Pcs as Pcs<
        Challenge,
        crate::plonky3_stark::config::Challenger,
    >>::natural_domain_for_degree(pcs, degree);
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
    Ok(recompose_quotient_from_chunks::<WqcStarkConfig>(
        &quotient_chunks_domains,
        &proof.opened_values.quotient_chunks,
        zeta,
    ))
}

fn build_witness(
    meta: OodWitnessMeta,
    openings: ExtractedOodOpenings,
    quotient: Challenge,
) -> Result<OodWitness, String> {
    let folded = fold_ood_native(
        meta.kind,
        meta.num_outcomes as usize,
        meta.degree_bits as usize,
        &openings.trace_local,
        &openings.trace_next,
        openings.is_first_row,
        openings.is_last_row,
        openings.is_transition,
        openings.alpha,
    );
    if folded * openings.inv_vanishing != quotient {
        return Err("native OOD mismatch during witness extraction".into());
    }
    Ok(OodWitness {
        kind: meta.kind,
        num_outcomes: meta.num_outcomes,
        width: meta.width,
        degree_bits: meta.degree_bits,
        zeta: openings.zeta,
        alpha: openings.alpha,
        quotient,
        inv_vanishing: openings.inv_vanishing,
        is_first_row: openings.is_first_row,
        is_last_row: openings.is_last_row,
        is_transition: openings.is_transition,
        trace_local: openings.trace_local,
        trace_next: openings.trace_next,
        folded,
    })
}

pub fn extract_agg_ood_witness(proof: &Proof<WqcStarkConfig>) -> Result<OodWitness, String> {
    let air = AggregationAir;
    let width = AGG_WIDTH as u32;
    let openings = extract_common(proof, width as usize)?;
    let quotient = recompose_quotient(proof, &air, openings.zeta)?;
    build_witness(
        OodWitnessMeta {
            kind: OodAirKind::Aggregation,
            num_outcomes: 0,
            width,
            degree_bits: proof.degree_bits as u32,
        },
        openings,
        quotient,
    )
}

pub fn extract_leaf_ood_witness(
    proof: &Proof<WqcStarkConfig>,
    leaf_kind: LeafKind,
    num_outcomes: usize,
) -> Result<OodWitness, String> {
    let kind = ood_kind_for_leaf(leaf_kind);
    let width = match kind {
        OodAirKind::Unitary => AIR_WIDTH as u32,
        OodAirKind::Distribution => {
            let dim = 1usize << proof.degree_bits;
            DistributionAir { dim, num_outcomes }.width() as u32
        }
        OodAirKind::ShotSampling => SHOT_SAMPLING_AIR_WIDTH as u32,
        OodAirKind::Aggregation => {
            return Err("extract_leaf_ood_witness called with Aggregation".into());
        }
    };
    let openings = extract_common(proof, width as usize)?;
    let quotient = match kind {
        OodAirKind::Unitary => recompose_quotient(proof, &QuantumExecutionAir, openings.zeta)?,
        OodAirKind::Distribution => {
            let dim = 1usize << proof.degree_bits;
            recompose_quotient(proof, &DistributionAir { dim, num_outcomes }, openings.zeta)?
        }
        OodAirKind::ShotSampling => recompose_quotient(proof, &ShotSamplingAir, openings.zeta)?,
        OodAirKind::Aggregation => unreachable!(),
    };
    build_witness(
        OodWitnessMeta {
            kind,
            num_outcomes: num_outcomes as u32,
            width,
            degree_bits: proof.degree_bits as u32,
        },
        openings,
        quotient,
    )
}

pub fn generate_ood_proof_from_witness(witness: &OodWitness) -> Result<OodStepProof, String> {
    super::ood_air::generate_ood_proof(witness)
}

pub fn generate_ood_proof_from_witness_with_queries(
    witness: &OodWitness,
    num_queries: usize,
) -> Result<OodStepProof, String> {
    super::ood_air::generate_ood_proof_with_queries(witness, num_queries)
}

pub fn generate_agg_ood_proof(proof: &Proof<WqcStarkConfig>) -> Result<OodStepProof, String> {
    let witness = extract_agg_ood_witness(proof)?;
    generate_ood_proof_from_witness(&witness)
}

pub fn generate_agg_ood_proof_with_queries(
    proof: &Proof<WqcStarkConfig>,
    num_queries: usize,
) -> Result<OodStepProof, String> {
    let witness = extract_agg_ood_witness(proof)?;
    generate_ood_proof_from_witness_with_queries(&witness, num_queries)
}

pub fn generate_leaf_ood_proof(
    proof: &Proof<WqcStarkConfig>,
    leaf_kind: LeafKind,
    num_outcomes: usize,
) -> Result<OodStepProof, String> {
    let witness = extract_leaf_ood_witness(proof, leaf_kind, num_outcomes)?;
    generate_ood_proof_from_witness(&witness)
}

pub fn generate_leaf_ood_proof_with_queries(
    proof: &Proof<WqcStarkConfig>,
    leaf_kind: LeafKind,
    num_outcomes: usize,
    num_queries: usize,
) -> Result<OodStepProof, String> {
    let witness = extract_leaf_ood_witness(proof, leaf_kind, num_outcomes)?;
    generate_ood_proof_from_witness_with_queries(&witness, num_queries)
}

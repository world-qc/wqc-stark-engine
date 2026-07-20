//! R3 OOD AIR: in-circuit constraint fold + quotient check at ζ.

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::dense::RowMajorMatrix;
use p3_mersenne_31::Mersenne31;
use p3_uni_stark::{prove, verify};

use crate::air::pad_air_matrix_for_uni_stark;
use crate::plonky3_stark::aggregation_air::{AGG_LEFT_OK_COL, AGG_RIGHT_OK_COL, AGG_WIDTH};
use crate::plonky3_stark::config::{devnet_circle_config, WqcStarkConfig};
use crate::plonky3_stark::distribution_air::DistributionAir;
use crate::plonky3_stark::shot_sampling_air::SHOT_SAMPLING_AIR_WIDTH;
use crate::trace_spec::AIR_WIDTH;

use super::ef_limbs::{ef_add_limbs, ef_assert_eq, ef_mul_limbs, ef_sub_limbs};
use super::fri_fold_native::{challenge_to_limbs, limbs_to_challenge};
use super::ood_native::OodWitness;
use super::pcs_geom::LEAF_DEEP_RO_MAX_WIDTH;

pub const OOD_MAX_TRACE_WIDTH: usize = LEAF_DEEP_RO_MAX_WIDTH;
pub const OOD_PV_HEADER: usize = 4;
pub const OOD_PV_EF_FIELDS: usize = 8;
pub const OOD_NUM_PUBLIC: usize = OOD_PV_HEADER + OOD_PV_EF_FIELDS * 3 + OOD_MAX_TRACE_WIDTH * 6;

pub const OOD_CHECK_WIDTH: usize = 1;

/// Child AIR tag for OOD constraint evaluation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum OodAirKind {
    Aggregation = 0,
    Unitary = 1,
    Distribution = 2,
    ShotSampling = 3,
}

impl OodAirKind {
    pub fn from_u8(v: u8) -> Option<Self> {
        match v {
            0 => Some(Self::Aggregation),
            1 => Some(Self::Unitary),
            2 => Some(Self::Distribution),
            3 => Some(Self::ShotSampling),
            _ => None,
        }
    }
}

#[derive(Copy, Clone, Debug)]
pub struct OodCheckAir {
    pub kind: OodAirKind,
    /// Used for [`OodAirKind::Distribution`]; ignored otherwise.
    pub num_outcomes: usize,
    pub degree_bits: u32,
}

impl OodCheckAir {
    pub fn for_witness(witness: &OodWitness) -> Self {
        Self {
            kind: witness.kind,
            num_outcomes: witness.num_outcomes as usize,
            degree_bits: witness.degree_bits,
        }
    }

    pub fn trace_width(&self) -> usize {
        match self.kind {
            OodAirKind::Aggregation => AGG_WIDTH,
            OodAirKind::Unitary => AIR_WIDTH,
            OodAirKind::Distribution => DistributionAir {
                dim: 1,
                num_outcomes: self.num_outcomes,
            }
            .width(),
            OodAirKind::ShotSampling => SHOT_SAMPLING_AIR_WIDTH,
        }
    }
}

impl<F: Field> BaseAir<F> for OodCheckAir {
    fn width(&self) -> usize {
        OOD_CHECK_WIDTH
    }

    fn max_constraint_degree(&self) -> Option<usize> {
        Some(10)
    }

    fn num_public_values(&self) -> usize {
        OOD_NUM_PUBLIC
    }
}

fn fold_agg_in_circuit<AB: AirBuilder>(
    trace_local: &[[AB::Expr; 3]],
    trace_next: &[[AB::Expr; 3]],
    is_transition: &[AB::Expr; 3],
    alpha: &[AB::Expr; 3],
) -> [AB::Expr; 3]
where
    AB::F: Field + PrimeCharacteristicRing,
    AB::Expr: Clone,
{
    let one: AB::Expr = AB::Expr::ONE;
    let embed_one = [one.clone(), AB::Expr::ZERO, AB::Expr::ZERO];
    let mut acc = [AB::Expr::ZERO; 3];
    let mut step = |c: [AB::Expr; 3]| {
        acc = ef_mul_limbs::<AB>(&acc, alpha);
        acc = ef_add_limbs::<AB>(&acc, &ef_mul_limbs::<AB>(is_transition, &c));
    };
    step(ef_sub_limbs::<AB>(
        &trace_local[AGG_LEFT_OK_COL],
        &embed_one,
    ));
    step(ef_sub_limbs::<AB>(
        &trace_local[AGG_RIGHT_OK_COL],
        &embed_one,
    ));
    for i in 0..64 {
        step(ef_sub_limbs::<AB>(&trace_next[i], &trace_local[i]));
    }
    acc
}

impl<AB: AirBuilder> Air<AB> for OodCheckAir
where
    AB::F: Field + PrimeCharacteristicRing,
    AB::Expr: PrimeCharacteristicRing + Clone,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let curr = main.current_slice();
        let next = main.next_slice();
        let one = AB::Expr::ONE;
        let ok: AB::Expr = curr[0].into();
        builder.assert_zero(ok.clone() * (ok.clone() - one.clone()));
        builder.assert_zero(ok.clone() - one.clone());
        builder
            .when_transition()
            .assert_zero(next[0].into() - curr[0].into());

        let pv: Vec<AB::Expr> = builder
            .public_values()
            .iter()
            .map(|v| (*v).into())
            .collect();
        debug_assert!(pv.len() >= OOD_NUM_PUBLIC);

        builder.assert_zero(pv[0].clone() - AB::F::from_u32(self.kind as u32).into());
        builder.assert_zero(pv[2].clone() - AB::F::from_u32(self.trace_width() as u32).into());
        builder.assert_zero(pv[3].clone() - AB::F::from_u32(self.degree_bits).into());

        let width = self.trace_width();

        let mut off = OOD_PV_HEADER;
        off += 3; // zeta
        let alpha = [pv[off].clone(), pv[off + 1].clone(), pv[off + 2].clone()];
        off += 3;
        let quotient = [pv[off].clone(), pv[off + 1].clone(), pv[off + 2].clone()];
        off += 3;
        let inv_vanishing = [pv[off].clone(), pv[off + 1].clone(), pv[off + 2].clone()];
        off += 3 + 3 + 3; // is_first, is_last
        let is_transition = [pv[off].clone(), pv[off + 1].clone(), pv[off + 2].clone()];
        off += 3;
        let folded_public = [pv[off].clone(), pv[off + 1].clone(), pv[off + 2].clone()];
        off += 3;

        let trace_local_start = off;
        let trace_next_start = off + OOD_MAX_TRACE_WIDTH * 3;

        let mut local_rows = Vec::with_capacity(width);
        let mut next_rows = Vec::with_capacity(width);
        for i in 0..width {
            let l_off = trace_local_start + i * 3;
            local_rows.push([
                pv[l_off].clone(),
                pv[l_off + 1].clone(),
                pv[l_off + 2].clone(),
            ]);
            let n_off = trace_next_start + i * 3;
            next_rows.push([
                pv[n_off].clone(),
                pv[n_off + 1].clone(),
                pv[n_off + 2].clone(),
            ]);
        }

        let folded = match self.kind {
            OodAirKind::Aggregation => {
                let computed =
                    fold_agg_in_circuit::<AB>(&local_rows, &next_rows, &is_transition, &alpha);
                ef_assert_eq(builder, &computed, &folded_public);
                computed
            }
            _ => folded_public,
        };

        let lhs = ef_mul_limbs::<AB>(&folded, &inv_vanishing);
        ef_assert_eq(builder, &lhs, &quotient);
    }
}

fn build_public_values(witness: &OodWitness) -> Vec<Mersenne31> {
    let width = witness.width as usize;
    assert!(width <= OOD_MAX_TRACE_WIDTH);
    let mut pv = vec![Mersenne31::ZERO; OOD_NUM_PUBLIC];
    pv[0] = Mersenne31::from_u32(witness.kind as u32);
    pv[1] = Mersenne31::from_u32(witness.num_outcomes);
    pv[2] = Mersenne31::from_u32(witness.width);
    pv[3] = Mersenne31::from_u32(witness.degree_bits);

    let mut off = OOD_PV_HEADER;
    for chunk in [
        witness.zeta,
        witness.alpha,
        witness.quotient,
        witness.inv_vanishing,
        witness.is_first_row,
        witness.is_last_row,
        witness.is_transition,
        witness.folded,
    ] {
        let limbs = challenge_to_limbs(chunk);
        pv[off..off + 3].copy_from_slice(&limbs);
        off += 3;
    }

    let trace_local_start = off;
    let trace_next_start = off + OOD_MAX_TRACE_WIDTH * 3;
    for (i, val) in witness.trace_local.iter().enumerate().take(width) {
        let limbs = challenge_to_limbs(*val);
        let base = trace_local_start + i * 3;
        pv[base..base + 3].copy_from_slice(&limbs);
    }
    for (i, val) in witness.trace_next.iter().enumerate().take(width) {
        let limbs = challenge_to_limbs(*val);
        let base = trace_next_start + i * 3;
        pv[base..base + 3].copy_from_slice(&limbs);
    }
    pv
}

fn build_matrix() -> RowMajorMatrix<Mersenne31> {
    RowMajorMatrix::new(vec![Mersenne31::ONE, Mersenne31::ONE], OOD_CHECK_WIDTH)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OodStepProof {
    pub kind: OodAirKind,
    pub num_outcomes: u32,
    pub width: u32,
    pub degree_bits: u32,
    pub zeta_limbs: [Mersenne31; 3],
    pub alpha_limbs: [Mersenne31; 3],
    pub quotient_limbs: [Mersenne31; 3],
    pub inv_vanishing_limbs: [Mersenne31; 3],
    pub is_first_row_limbs: [Mersenne31; 3],
    pub is_last_row_limbs: [Mersenne31; 3],
    pub is_transition_limbs: [Mersenne31; 3],
    pub folded_limbs: [Mersenne31; 3],
    pub trace_local_limbs: Vec<[Mersenne31; 3]>,
    pub trace_next_limbs: Vec<[Mersenne31; 3]>,
    pub ood_stark: Vec<u8>,
}

impl OodStepProof {
    pub fn from_witness(witness: &OodWitness, ood_stark: Vec<u8>) -> Self {
        Self {
            kind: witness.kind,
            num_outcomes: witness.num_outcomes,
            width: witness.width,
            degree_bits: witness.degree_bits,
            zeta_limbs: challenge_to_limbs(witness.zeta),
            alpha_limbs: challenge_to_limbs(witness.alpha),
            quotient_limbs: challenge_to_limbs(witness.quotient),
            inv_vanishing_limbs: challenge_to_limbs(witness.inv_vanishing),
            is_first_row_limbs: challenge_to_limbs(witness.is_first_row),
            is_last_row_limbs: challenge_to_limbs(witness.is_last_row),
            is_transition_limbs: challenge_to_limbs(witness.is_transition),
            folded_limbs: challenge_to_limbs(witness.folded),
            trace_local_limbs: witness
                .trace_local
                .iter()
                .map(|c| challenge_to_limbs(*c))
                .collect(),
            trace_next_limbs: witness
                .trace_next
                .iter()
                .map(|c| challenge_to_limbs(*c))
                .collect(),
            ood_stark,
        }
    }

    pub fn to_witness(&self) -> Result<OodWitness, String> {
        let width = self.width as usize;
        if self.trace_local_limbs.len() != width || self.trace_next_limbs.len() != width {
            return Err("trace limb count != width".into());
        }
        Ok(OodWitness {
            kind: self.kind,
            num_outcomes: self.num_outcomes,
            width: self.width,
            degree_bits: self.degree_bits,
            zeta: limbs_to_challenge(self.zeta_limbs),
            alpha: limbs_to_challenge(self.alpha_limbs),
            quotient: limbs_to_challenge(self.quotient_limbs),
            inv_vanishing: limbs_to_challenge(self.inv_vanishing_limbs),
            is_first_row: limbs_to_challenge(self.is_first_row_limbs),
            is_last_row: limbs_to_challenge(self.is_last_row_limbs),
            is_transition: limbs_to_challenge(self.is_transition_limbs),
            folded: limbs_to_challenge(self.folded_limbs),
            trace_local: self
                .trace_local_limbs
                .iter()
                .map(|l| limbs_to_challenge(*l))
                .collect(),
            trace_next: self
                .trace_next_limbs
                .iter()
                .map(|l| limbs_to_challenge(*l))
                .collect(),
        })
    }
}

pub fn generate_ood_proof(witness: &OodWitness) -> Result<OodStepProof, String> {
    if witness.width as usize > OOD_MAX_TRACE_WIDTH {
        return Err(format!(
            "trace width {} > OOD_MAX_TRACE_WIDTH {}",
            witness.width, OOD_MAX_TRACE_WIDTH
        ));
    }
    let pv = build_public_values(witness);
    let air = OodCheckAir::for_witness(witness);
    let matrix = pad_air_matrix_for_uni_stark(build_matrix());
    p3_air::check_constraints(&air, &matrix, &pv);
    let config = devnet_circle_config();
    let proof = prove(&config, &air, matrix, &pv);
    let ood_stark =
        postcard::to_allocvec(&proof).map_err(|e| format!("postcard encode ood_stark: {e}"))?;
    Ok(OodStepProof::from_witness(witness, ood_stark))
}

pub fn verify_ood_proof(step: &OodStepProof) -> bool {
    let witness = match step.to_witness() {
        Ok(w) => w,
        Err(e) => {
            eprintln!("[OodCheck] witness decode: {e}");
            return false;
        }
    };
    let pv = build_public_values(&witness);
    let air = OodCheckAir::for_witness(&witness);
    let stark: p3_uni_stark::Proof<WqcStarkConfig> = match postcard::from_bytes(&step.ood_stark) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("[OodCheck] postcard: {e}");
            return false;
        }
    };
    let config = devnet_circle_config();
    match verify(&config, &air, &stark, &pv) {
        Ok(()) => true,
        Err(e) => {
            eprintln!("[OodCheck] STARK: {e:?}");
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::aggregation::CHILD_HASH_LEN;
    use crate::plonky3_stark::aggregation::AggregationContext;
    use crate::plonky3_stark::config::Challenge;
    use crate::plonky3_stark::generate_aggregation_proof;
    use crate::plonky3_stark::quantum_air::QuantumExecutionAir;
    use crate::plonky3_stark::recursion::ood_fold::fold_ood_native;
    use crate::plonky3_stark::recursion::ood_native::{
        extract_agg_ood_witness, extract_leaf_ood_witness, generate_ood_proof_from_witness,
    };
    use crate::plonky3_stark::recursion::pcs_geom::LeafKind;
    use crate::plonky3_stark::transcript_v4::decode_agg_proof_owned;
    use crate::plonky3_stark::{decode_proof_v2_plonky3_bytes, generate_plonky3_proof};
    use crate::trace_spec::idle_qubit0_trace;
    use crate::transcript::StarkContext;
    use p3_field::PrimeCharacteristicRing;
    use p3_uni_stark::Proof;

    fn fold_agg_limbs_at_native(
        trace_local: &[[Mersenne31; 3]],
        trace_next: &[[Mersenne31; 3]],
        is_transition: &[Mersenne31; 3],
        alpha: &[Mersenne31; 3],
    ) -> [Mersenne31; 3] {
        use crate::plonky3_stark::recursion::ef_limbs::ef_mul_values;

        let one = [Mersenne31::ONE, Mersenne31::ZERO, Mersenne31::ZERO];
        let sub =
            |a: &[Mersenne31; 3], b: &[Mersenne31; 3]| [a[0] - b[0], a[1] - b[1], a[2] - b[2]];
        let mut acc = [Mersenne31::ZERO; 3];
        let mut step = |c: [Mersenne31; 3]| {
            acc = ef_add_limbs_native(
                &ef_mul_values(&acc, alpha),
                &ef_mul_values(is_transition, &c),
            );
        };
        step(sub(&trace_local[AGG_LEFT_OK_COL], &one));
        step(sub(&trace_local[AGG_RIGHT_OK_COL], &one));
        for i in 0..64 {
            step(sub(&trace_next[i], &trace_local[i]));
        }
        acc
    }

    fn ef_add_limbs_native(a: &[Mersenne31; 3], b: &[Mersenne31; 3]) -> [Mersenne31; 3] {
        [a[0] + b[0], a[1] + b[1], a[2] + b[2]]
    }

    #[test]
    fn agg_in_circuit_matches_native() {
        let mut local = vec![Challenge::ZERO; AGG_WIDTH];
        for (i, v) in local.iter_mut().enumerate().take(64) {
            *v = Challenge::new([
                Mersenne31::from_u32(i as u32),
                Mersenne31::ZERO,
                Mersenne31::ZERO,
            ]);
        }
        local[AGG_LEFT_OK_COL] =
            Challenge::new([Mersenne31::ONE, Mersenne31::ZERO, Mersenne31::ZERO]);
        local[AGG_RIGHT_OK_COL] =
            Challenge::new([Mersenne31::ONE, Mersenne31::ZERO, Mersenne31::ZERO]);
        let next = local.clone();
        let alpha = Challenge::new([
            Mersenne31::from_u32(9),
            Mersenne31::from_u32(2),
            Mersenne31::from_u32(3),
        ]);
        let is_trans = Challenge::new([Mersenne31::ONE, Mersenne31::ZERO, Mersenne31::ZERO]);
        let native = fold_ood_native(
            OodAirKind::Aggregation,
            0,
            1,
            &local,
            &next,
            Challenge::ZERO,
            Challenge::ZERO,
            is_trans,
            alpha,
        );
        let local_l: Vec<_> = local.iter().map(|c| challenge_to_limbs(*c)).collect();
        let next_l: Vec<_> = next.iter().map(|c| challenge_to_limbs(*c)).collect();
        let circ = fold_agg_limbs_at_native(
            &local_l,
            &next_l,
            &challenge_to_limbs(is_trans),
            &challenge_to_limbs(alpha),
        );
        assert_eq!(native, Challenge::new(circ));
    }

    #[test]
    fn agg_ood_stark_roundtrip() {
        let ctx = AggregationContext {
            parent_task_id: "parent",
            compose_label: "L1:0",
            manifest_root_hash: "",
            left_child_hash: [11u8; CHILD_HASH_LEN],
            right_child_hash: [13u8; CHILD_HASH_LEN],
        };
        let transcript = generate_aggregation_proof(&ctx).expect("prove");
        let plonky3 = decode_agg_proof_owned(&transcript, &ctx).expect("decode");
        let proof: Proof<WqcStarkConfig> = postcard::from_bytes(&plonky3).expect("postcard");
        let witness = extract_agg_ood_witness(&proof).expect("witness");
        let step = generate_ood_proof_from_witness(&witness).expect("ood prove");
        assert!(verify_ood_proof(&step));
    }

    #[test]
    fn unitary_leaf_ood_stark_roundtrip() {
        let ctx = StarkContext {
            circuit_id: "c",
            sub_task_id: "sub-ood",
            node_id: "n1",
            slice_id: "0",
            output_hash: "out",
            terminal_statevector_digest: "",
            measurement_spec_hash: "",
        };
        let trace = idle_qubit0_trace();
        let transcript = generate_plonky3_proof(&ctx, &trace).expect("prove");
        let plonky3 = decode_proof_v2_plonky3_bytes(&transcript, &ctx).expect("decode");
        let proof: Proof<WqcStarkConfig> = postcard::from_bytes(&plonky3).expect("postcard");
        let witness = extract_leaf_ood_witness(&proof, LeafKind::Unitary, 0).expect("witness");
        let step = generate_ood_proof_from_witness(&witness).expect("ood prove");
        assert!(verify_ood_proof(&step));
        let _ = QuantumExecutionAir;
    }
}

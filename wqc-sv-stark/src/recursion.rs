//! Recursion backend for leaf proofs, written against Plonky3-recursion's public API.
//!
//! The stock FRI backend only knows its built-in tables, so it cannot rebuild a leaf's custom
//! tables when verifying a leaf proof. The input side builds the verifier circuit for a proof that carries our custom NPO table
//! (`verify_p3_batch_proof_circuit` takes the table provers as an argument). The output side —
//! the tables the verifier circuit itself needs (Poseidon2 challenger, recompose) — is
//! delegated to the stock FRI backend.

use p3_circuit::ops::Poseidon2Config;
use p3_circuit::{CircuitBuilder, CircuitRunner, NonPrimitiveOpId};
use p3_circuit_prover::common::{NpoAirBuilder, NpoPreprocessor};
use p3_circuit_prover::TableProver;
use p3_lookup::logup::LogUpGadget;
use p3_recursion::prelude::*;
use p3_recursion::verifier::verify_p3_batch_proof_circuit;
use p3_recursion::{
    replay_recursion_input_transcript, FriRecursionBackend, FriRecursionBackendForExt,
    FriRecursionConfig, VerificationError,
};
use p3_recursion::{BatchStarkVerifierInputsBuilder, PcsRecursionBackend, VerifierCircuitResult};

use crate::npo::{SvProver, SvTable};
use crate::Cfg;

pub type Inner = FriRecursionBackendForExt<2, 8, 4, Poseidon2Config>;
type Builder = BatchStarkVerifierInputsBuilder<
    Cfg,
    <Cfg as FriRecursionConfig>::Commitment,
    <Cfg as FriRecursionConfig>::OpeningProof,
>;

pub struct WqcBackend {
    inner: Inner,
    /// Statement schema of input proofs that export one.
    statement: Option<p3_circuit::StatementSchema>,
}

impl Default for WqcBackend {
    fn default() -> Self {
        Self {
            inner: FriRecursionBackend::<8, 4, _>::new(Poseidon2Config::GOLDILOCKS_D2_W8)
                .for_extension_degree::<2>(),
            statement: None,
        }
    }
}

impl WqcBackend {
    pub fn with_statement(schema: p3_circuit::StatementSchema) -> Self {
        Self {
            statement: Some(schema),
            ..Self::default()
        }
    }
}

/// Table provers for the input proof's non-primitive tables, in manifest order.
fn input_provers(
    prev: &RecursionInput<'_, Cfg, BatchOnly>,
    statement: &Option<p3_circuit::StatementSchema>,
) -> Result<Vec<Box<dyn TableProver<Cfg>>>, VerificationError> {
    let RecursionInput::BatchStark { proof, .. } = prev else {
        return Err(VerificationError::InvalidProofShape(
            "WqcBackend takes batch inputs".into(),
        ));
    };
    proof
        .non_primitives
        .iter()
        .map(|entry| {
            if let (true, Some(schema)) = (
                entry.op_type == p3_circuit::ops::NpoTypeId::statement(),
                statement,
            ) {
                Ok(
                    Box::new(p3_circuit_prover::StatementProver::<1>::new(schema.clone()))
                        as Box<dyn TableProver<Cfg>>,
                )
            } else if let Some(t) = SvTable::from_op(&entry.op_type) {
                Ok(Box::new(SvProver(t)) as Box<dyn TableProver<Cfg>>)
            } else {
                Err(VerificationError::InvalidProofShape(format!(
                    "unknown input table {}",
                    entry.op_type.as_str()
                )))
            }
        })
        .collect()
}

pub struct WqcVerifierResult {
    builder: Builder,
    op_ids: Vec<NonPrimitiveOpId>,
}

impl VerifierCircuitResult<Cfg, BatchOnly> for WqcVerifierResult {
    fn pack_public_inputs(
        &self,
        prev: &RecursionInput<'_, Cfg, BatchOnly>,
    ) -> Result<Vec<EFx>, VerificationError> {
        let RecursionInput::BatchStark {
            proof,
            common_data,
            table_public_inputs,
        } = prev
        else {
            return Err(VerificationError::InvalidProofShape(
                "batch input expected".into(),
            ));
        };
        Ok(self
            .builder
            .pack_values(table_public_inputs, &proof.proof, common_data)
            .0)
    }
    fn pack_private_inputs(
        &self,
        prev: &RecursionInput<'_, Cfg, BatchOnly>,
    ) -> Result<Vec<EFx>, VerificationError> {
        let RecursionInput::BatchStark {
            proof,
            common_data,
            table_public_inputs,
        } = prev
        else {
            return Err(VerificationError::InvalidProofShape(
                "batch input expected".into(),
            ));
        };
        Ok(self
            .builder
            .pack_values(table_public_inputs, &proof.proof, common_data)
            .1)
    }
    fn op_ids(&self) -> &[NonPrimitiveOpId] {
        &self.op_ids
    }
}

/// The recursion layer's challenge field (Goldilocks²).
pub type EFx = <Cfg as p3_uni_stark::StarkGenericConfig>::Challenge;

impl PcsRecursionBackend<Cfg, BatchOnly, 2> for WqcBackend {
    type VerifierResult = WqcVerifierResult;

    fn prepare_circuit(
        &self,
        config: &Cfg,
        circuit: &mut CircuitBuilder<EFx>,
    ) -> Result<(), VerificationError> {
        config.prepare_circuit_for_verification(circuit)
    }

    fn build_verifier_circuit(
        &self,
        prev: &RecursionInput<'_, Cfg, BatchOnly>,
        config: &Cfg,
        circuit: &mut CircuitBuilder<EFx>,
    ) -> Result<Self::VerifierResult, VerificationError> {
        let RecursionInput::BatchStark {
            proof, common_data, ..
        } = prev
        else {
            return Err(VerificationError::InvalidProofShape(
                "batch input expected".into(),
            ));
        };
        let provers = input_provers(prev, &self.statement)?;
        let (builder, op_ids) = verify_p3_batch_proof_circuit::<
            Cfg,
            <Cfg as FriRecursionConfig>::Commitment,
            <Cfg as FriRecursionConfig>::InputProof,
            <Cfg as FriRecursionConfig>::OpeningProof,
            _,
            _,
            8,
            4,
            1,
        >(
            config,
            circuit,
            proof,
            config.pcs_verifier_params(),
            common_data,
            &LogUpGadget::new(),
            Poseidon2Config::GOLDILOCKS_D2_W8,
            &provers,
        )?;
        Ok(WqcVerifierResult { builder, op_ids })
    }

    fn set_private_data(
        &self,
        config: &Cfg,
        runner: &mut CircuitRunner<'_, EFx>,
        op_ids: &[NonPrimitiveOpId],
        prev: &RecursionInput<'_, Cfg, BatchOnly>,
    ) -> Result<(), &'static str> {
        let provers = input_provers(prev, &self.statement).map_err(|_| "unknown input table")?;
        let transcript = replay_recursion_input_transcript(config, prev, &provers)
            .map_err(|_| "transcript replay failed")?;
        Cfg::with_fri_opening_proof(prev, move |opening| {
            Cfg::set_fri_private_data(config, runner, op_ids, opening, transcript)
        })
    }

    // Output side: the verifier circuit's own tables, as the stock backend registers them.
    fn non_primitive_preprocessors(
        &self,
    ) -> Vec<Box<dyn NpoPreprocessor<p3_batch_stark::Val<Cfg>>>> {
        <Inner as PcsRecursionBackend<Cfg, BatchOnly, 2>>::non_primitive_preprocessors(&self.inner)
    }
    fn non_primitive_provers(&self, ext_degree: usize) -> Vec<Box<dyn TableProver<Cfg>>> {
        <Inner as PcsRecursionBackend<Cfg, BatchOnly, 2>>::non_primitive_provers(
            &self.inner,
            ext_degree,
        )
    }
    fn non_primitive_air_builders(&self) -> Vec<Box<dyn NpoAirBuilder<Cfg, 2>>> {
        <Inner as PcsRecursionBackend<Cfg, BatchOnly, 2>>::non_primitive_air_builders(&self.inner)
    }
}

/// Recursion input for a leaf proof, with the trusted common data of the prepared leaf.
pub fn leaf_input<'a>(
    proof: &'a p3_circuit_prover::batch_stark_prover::BatchStarkProof<Cfg>,
    common: &'a p3_batch_stark::CommonData<Cfg>,
) -> RecursionInput<'a, Cfg, BatchOnly> {
    let mut table_public_inputs = vec![Vec::new(); p3_circuit_prover::NUM_PRIMITIVE_TABLES];
    table_public_inputs.extend(proof.non_primitives.iter().map(|e| e.public_values.clone()));
    RecursionInput::BatchStark {
        proof,
        common_data: common,
        table_public_inputs,
    }
}

/// The stock backend, for layers whose inputs carry only built-in tables.
pub fn stock_backend() -> Inner {
    FriRecursionBackend::<8, 4, _>::new(Poseidon2Config::GOLDILOCKS_D2_W8)
        .for_extension_degree::<2>()
}

//! Recursion over leaf proofs through Plonky3-recursion's trusted prepared owners.
//!
//! A trusted owner keeps the child's [`CircuitVerifier`], so the child relation — tables,
//! AIRs and preprocessed commitment, hence the circuit — is fixed by the verifier and never
//! read from the proof. The child statement is supplied by the caller and becomes the
//! statement of the recursion proof: a layer over a leaf verifies against the leaf's
//! `[context, digest]`, and a 2-to-1 aggregation against `left ‖ right`.
//!
//! Every recursion proof uses [`FriParams::RECURSION`], whatever the leaves' tier; the public
//! constructors take no FRI parameters. A layer's verifier still depends on its child (the leaf
//! circuit and tier, or the layer below).
//!
//! The stock FRI backend suffices: the trusted path rebuilds the child's tables, the leaf's
//! custom ones included, from the retained verifier.

use p3_circuit::ops::Poseidon2Config;
use p3_circuit_prover::batch_stark_prover::{BatchStarkProof, CircuitVerifier};
use p3_recursion::prelude::*;
use p3_recursion::{FriRecursionBackend, FriRecursionBackendForExt};

use crate::leaf::{Leaf, LeafProof};
use crate::{Cfg, Error, FriParams, F};

pub type Backend = FriRecursionBackendForExt<2, 8, 4, Poseidon2Config>;
type Owner = TrustedPreparedLayer<'static, Cfg, Cfg, BatchOnly, Backend, 2>;
type AggOwner =
    TrustedPreparedAggregation<'static, 'static, Cfg, Cfg, BatchOnly, BatchOnly, Backend, 2>;

pub fn backend() -> Backend {
    FriRecursionBackend::<8, 4, _>::new(Poseidon2Config::GOLDILOCKS_D2_W8)
        .for_extension_degree::<2>()
}

pub(crate) fn params(fri: FriParams) -> ProveNextLayerParams {
    ProveNextLayerParams {
        table_packing: p3_circuit_prover::batch_stark_prover::TablePacking::new(1, 4)
            .with_min_trace_height(fri.min_trace_height()),
        ..ProveNextLayerParams::default()
    }
}

fn rec(e: VerificationError) -> Error {
    Error::Recursion(format!("{e:?}"))
}

/// A recursion proof and the statement it verifies against.
pub struct RecursionProof {
    pub proof: BatchStarkProof<Cfg>,
    pub statement: Vec<F>,
}

/// A prepared recursion layer over one child relation; reusable for every proof of that child.
pub struct Layer {
    owner: Owner,
}

impl Layer {
    /// A layer over leaf proofs of `leaf`. `sample` fixes the allocation shape; any proof of
    /// the same circuit fits.
    pub fn over_leaf(leaf: &Leaf, sample: &LeafProof) -> Result<Self, Error> {
        Self::over_leaf_with(leaf, sample, FriParams::RECURSION)
    }

    /// A layer over proofs of another layer (or aggregation) with verifier `child`.
    pub fn over_layer(child: CircuitVerifier<Cfg>, sample: &RecursionProof) -> Result<Self, Error> {
        Self::over_layer_with(child, sample, FriParams::RECURSION)
    }

    /// The wrap chain's top layer over `child` (see [`crate::wrap`]): [`FriParams::WRAP`].
    pub fn over_layer_wrap(
        child: CircuitVerifier<Cfg>,
        sample: &RecursionProof,
    ) -> Result<Self, Error> {
        Self::over_layer_with(child, sample, FriParams::WRAP)
    }

    pub(crate) fn over_leaf_with(
        leaf: &Leaf,
        sample: &LeafProof,
        fri: FriParams,
    ) -> Result<Self, Error> {
        Self::over(leaf.verifier(), &sample.proof, &sample.statement, fri)
    }

    pub(crate) fn over_layer_with(
        child: CircuitVerifier<Cfg>,
        sample: &RecursionProof,
        fri: FriParams,
    ) -> Result<Self, Error> {
        Self::over(child, &sample.proof, &sample.statement, fri)
    }

    fn over(
        child: CircuitVerifier<Cfg>,
        proof: &BatchStarkProof<Cfg>,
        statement: &[F],
        fri: FriParams,
    ) -> Result<Self, Error> {
        let source = TrustedPreparedSource::BatchStark {
            verifier: child,
            proof,
            statement,
        };
        let owner = Owner::new(source, fri.config(), backend(), params(fri)).map_err(rec)?;
        Ok(Self { owner })
    }

    pub fn prove(
        &self,
        proof: &BatchStarkProof<Cfg>,
        statement: &[F],
    ) -> Result<RecursionProof, Error> {
        let out = self
            .owner
            .prove(TrustedPreparedInput::BatchStark { proof, statement })
            .map_err(rec)?;
        Ok(RecursionProof {
            proof: out.0,
            statement: statement.to_vec(),
        })
    }

    /// The verifier of this layer's proofs (their statement is the child's).
    pub fn verifier(&self) -> CircuitVerifier<Cfg> {
        self.owner.verifier()
    }
}

/// A prepared 2-to-1 aggregation over two child relations.
pub struct Aggregation {
    owner: AggOwner,
}

impl Aggregation {
    pub fn new(
        left: (CircuitVerifier<Cfg>, &RecursionProof),
        right: (CircuitVerifier<Cfg>, &RecursionProof),
    ) -> Result<Self, Error> {
        Self::new_with(left, right, FriParams::RECURSION)
    }

    pub(crate) fn new_with(
        left: (CircuitVerifier<Cfg>, &RecursionProof),
        right: (CircuitVerifier<Cfg>, &RecursionProof),
        fri: FriParams,
    ) -> Result<Self, Error> {
        let left_src = TrustedPreparedSource::BatchStark {
            verifier: left.0,
            proof: &left.1.proof,
            statement: &left.1.statement,
        };
        let right_src = TrustedPreparedSource::BatchStark {
            verifier: right.0,
            proof: &right.1.proof,
            statement: &right.1.statement,
        };
        let owner = AggOwner::new(left_src, right_src, fri.config(), backend(), params(fri))
            .map_err(rec)?;
        Ok(Self { owner })
    }

    /// Aggregates two child proofs; the result verifies against `left ‖ right`.
    pub fn prove(
        &self,
        left: &RecursionProof,
        right: &RecursionProof,
    ) -> Result<RecursionProof, Error> {
        let out = self
            .owner
            .prove(
                TrustedPreparedInput::BatchStark {
                    proof: &left.proof,
                    statement: &left.statement,
                },
                TrustedPreparedInput::BatchStark {
                    proof: &right.proof,
                    statement: &right.statement,
                },
            )
            .map_err(rec)?;
        let statement = left
            .statement
            .iter()
            .chain(&right.statement)
            .copied()
            .collect();
        Ok(RecursionProof {
            proof: out.0,
            statement,
        })
    }

    pub fn verifier(&self) -> CircuitVerifier<Cfg> {
        self.owner.verifier()
    }
}

/// Verifies a recursion proof with its layer's verifier and the expected statement.
pub fn verify(
    verifier: &CircuitVerifier<Cfg>,
    proof: &BatchStarkProof<Cfg>,
    statement: &[F],
) -> Result<(), Error> {
    verifier
        .verify(proof, statement)
        .map_err(|e| Error::Verify(format!("{e:?}")))
}

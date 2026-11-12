//! A task's v2 root: one recursion [`Layer`] over each leaf, then 2-to-1 [`Aggregation`]s level
//! by level, pairing neighbours and carrying an odd last node up unchanged. The root verifies
//! against the leaves' statements concatenated in leaf order (the carried node stays last, so
//! the order survives every level).
//!
//! Nothing beyond the leaf statements is bound: a task's manifest is matched against them by
//! the verifier, outside the proof.
//!
//! A verifier rebuilds every layer and aggregation from the leaves' circuits; the intermediate
//! proofs a [`RootProof`] carries only fix each level's allocation shape, and each is verified
//! against the verifier its children give before it is used.

use p3_circuit_prover::batch_stark_prover::CircuitVerifier;
use serde::{Deserialize, Serialize};

use crate::leaf::{decode_proof, encode_proof, verifier_peak_bytes, Leaf, LeafProof};
use crate::recursion::{verify, Aggregation, Layer, RecursionProof};
use crate::{Cfg, Error, FriParams, F};

/// Every recursion proof of a root ([`encode_proof`] bytes): the layers, one per leaf in leaf
/// order, then the aggregations level by level. The last is the root; a single leaf's root is
/// its layer.
#[derive(Serialize, Deserialize)]
pub struct RootProof {
    pub proofs: Vec<Vec<u8>>,
}

/// The root's bytes on the wire (postcard).
pub fn encode_root(root: &RootProof) -> Vec<u8> {
    postcard::to_allocvec(root).expect("a root serializes")
}

/// Reads [`encode_root`]'s bytes; trailing bytes are an error.
pub fn decode_root(bytes: &[u8]) -> Result<RootProof, Error> {
    match postcard::take_from_bytes(bytes) {
        Ok((root, [])) => Ok(root),
        Ok((_, rest)) => Err(Error::Verify(format!(
            "{} trailing bytes after the root",
            rest.len()
        ))),
        Err(e) => Err(Error::Verify(format!("root bytes: {e}"))),
    }
}

/// The statement a root over leaves with `statements` verifies against.
pub fn root_statement(statements: &[Vec<F>]) -> Vec<F> {
    statements.concat()
}

/// Proves the root over `leaves`, each a prepared leaf and its proof with the statement the
/// proof carries. Returns the root and its statement.
pub fn prove_root(leaves: &[(&Leaf, &LeafProof)]) -> Result<(RootProof, Vec<F>), Error> {
    prove_root_with(leaves, FriParams::RECURSION)
}

/// Verifies `root` over `leaves`: each a prepared leaf and one of its proofs, with the
/// statement the verifier expects of that leaf.
///
/// # Security
///
/// Only the expected statements bind anything: build each from the dispatch and the result
/// the verifier accepted (see [`crate::leaf::LeafVerifier::verify_sampling`]), never from a
/// prover's claim. The leaf proofs only fix the layers' shape.
pub fn verify_root(leaves: &[(&Leaf, &LeafProof)], root: &RootProof) -> Result<(), Error> {
    verify_root_with(leaves, root, FriParams::RECURSION)
}

/// An upper estimate of the memory [`verify_root`] peaks at, in bytes, for one leaf of `rows`
/// gate rows on `n` qubits with `shots`: the prepared leaf (about 1 KB per gate row, measured
/// 2^11 to 2^20 rows) and the layer (about 180 MB). Proving the root takes about 350 MB more.
pub fn verify_peak_bytes(n: usize, rows: usize, shots: u64) -> u64 {
    verifier_peak_bytes(n, rows, shots)
        .saturating_mul(3)
        .saturating_add(256 << 20)
}

pub(crate) fn prove_root_with(
    leaves: &[(&Leaf, &LeafProof)],
    fri: FriParams,
) -> Result<(RootProof, Vec<F>), Error> {
    let mut proofs = Vec::new();
    let mut level = Vec::with_capacity(leaves.len());
    for (leaf, sample) in leaves {
        let layer = Layer::over_leaf_with(leaf, sample, fri)?;
        let out = layer.prove(&sample.proof, &sample.statement)?;
        proofs.push(encode_proof(&out.proof));
        level.push((layer.verifier(), out));
    }
    let root = reduce(level, fri, |agg, left, right| {
        let out = agg.prove(left, right)?;
        proofs.push(encode_proof(&out.proof));
        Ok(out)
    })?;
    Ok((RootProof { proofs }, root.statement))
}

pub(crate) fn verify_root_with(
    leaves: &[(&Leaf, &LeafProof)],
    root: &RootProof,
    fri: FriParams,
) -> Result<(), Error> {
    let expected = leaves.len().max(1) * 2 - 1;
    if leaves.is_empty() || root.proofs.len() != expected {
        return Err(Error::Verify(format!(
            "{} proofs for {} leaves, expected {expected}",
            root.proofs.len(),
            leaves.len()
        )));
    }
    let mut proofs = root.proofs.iter();
    let mut next = |verifier: &CircuitVerifier<Cfg>, statement: Vec<F>| {
        let bytes = proofs.next().expect("counted above");
        let proof = decode_proof(bytes)?;
        verify(verifier, &proof, &statement)?;
        Ok::<_, Error>(RecursionProof { proof, statement })
    };
    let mut level = Vec::with_capacity(leaves.len());
    for (leaf, sample) in leaves {
        let layer = Layer::over_leaf_with(leaf, sample, fri)?;
        let verifier = layer.verifier();
        let out = next(&verifier, sample.statement.clone())?;
        level.push((verifier, out));
    }
    reduce(level, fri, |agg, left, right| {
        next(
            &agg.verifier(),
            root_statement(&[left.statement.clone(), right.statement.clone()]),
        )
    })?;
    Ok(())
}

/// Folds one level at a time until one node is left; `step` gives an aggregation's proof.
fn reduce(
    mut level: Vec<(CircuitVerifier<Cfg>, RecursionProof)>,
    fri: FriParams,
    mut step: impl FnMut(
        &Aggregation,
        &RecursionProof,
        &RecursionProof,
    ) -> Result<RecursionProof, Error>,
) -> Result<RecursionProof, Error> {
    if level.is_empty() {
        return Err(Error::Prove("a root needs at least one leaf".into()));
    }
    while level.len() > 1 {
        let mut nodes = level.into_iter();
        let mut up = Vec::new();
        while let Some(left) = nodes.next() {
            let Some(right) = nodes.next() else {
                up.push(left);
                break;
            };
            let agg = Aggregation::new_with((left.0, &left.1), (right.0, &right.1), fri)?;
            let out = step(&agg, &left.1, &right.1)?;
            up.push((agg.verifier(), out));
        }
        level = up;
    }
    Ok(level.pop().expect("one node left").1)
}

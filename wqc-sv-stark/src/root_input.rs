//! The leaves JSON a v2 root (and its wrap chain) is verified over: `{"leaves":[...]}`, in the
//! order the composer was given them, each with the circuit, the dispatch, the digest, seed
//! and canonical counts the orchestrator accepted, and the leaf proof (base64). The root
//! verifies against the statements built from those fields, never against a prover's claim.
//!
//! The orchestrator verifies through the FFI (`wqc_sv_verify_root`, `wqc_sv_verify_wrap`);
//! anyone holding the published evidence (wqc-docs `spec/zk-SNARK.md` §11.6) recomputes the
//! wrap digest with [`verify_wrap_json`].

use base64::Engine as _;
use serde::Deserialize;

use crate::born::Sampling;
use crate::leaf::{self, Dispatch, Leaf, LeafProof};
use crate::wire::{parse_circuit, parse_counts, parse_leaf};
use crate::{root, wrap, Error, SecurityLevel};

/// One leaf: its circuit, and the dispatch and result the orchestrator accepted
/// (`shots == 0`: a `statevector_scalar` leaf, without seed and counts).
#[derive(Deserialize)]
struct RootLeaf {
    qubit_count: u32,
    circuit: String,
    #[serde(default)]
    classical_bit_count: u32,
    #[serde(default)]
    shots: u64,
    security_level: String,
    circuit_id: String,
    sub_task_id: String,
    node_id: String,
    slice_id: String,
    digest: [u64; 4],
    #[serde(default)]
    sample_seed: u64,
    #[serde(default)]
    counts: String,
    /// The leaf proof (standard base64): it fixes the layer's shape, the expected statement
    /// is built from the fields above.
    proof: String,
}

#[derive(Deserialize)]
struct RootInput {
    leaves: Vec<RootLeaf>,
}

/// Verifies a task's v2 root (`root::encode_root` bytes) over the leaves in `json`. Unlike
/// [`verify_wrap_json`] it takes any number of leaves: a root over more than
/// [`wrap::MAX_LEAVES`] is valid, it just cannot be wrapped.
pub fn verify_root_json(json: &str, root_bytes: &[u8]) -> Result<(), Error> {
    let leaves = root_leaves(&parse(json)?)?;
    let refs: Vec<_> = leaves.iter().map(|(l, p)| (l, p)).collect();
    root::verify_root(&refs, &root::decode_root(root_bytes)?)
}

/// Verifies a task's v2 root, as [`verify_root_json`], then its wrap chain
/// (`wrap::encode_wrap` bytes), and returns the wrap digest: four Goldilocks elements, the
/// SNARK's public input and SettlementV4's `wrapDigest`. More than [`wrap::MAX_LEAVES`]
/// leaves are refused before any verifying.
pub fn verify_wrap_json(
    json: &str,
    root_bytes: &[u8],
    wrap_bytes: &[u8],
) -> Result<[u64; 4], Error> {
    let input = parse(json)?;
    if input.leaves.len() > wrap::MAX_LEAVES {
        return Err(Error::Verify(format!(
            "{} leaves, more than {}",
            input.leaves.len(),
            wrap::MAX_LEAVES
        )));
    }
    let leaves = root_leaves(&input)?;
    let refs: Vec<_> = leaves.iter().map(|(l, p)| (l, p)).collect();
    let root = root::decode_root(root_bytes)?;
    let (rv, rp) = root::verified_root(&refs, &root)?;
    let top = wrap::verify_wrap(rv, &rp, &wrap::decode_wrap(wrap_bytes)?)?;
    let digest = wrap::snark_public_inputs(&top);
    digest
        .as_slice()
        .try_into()
        .map_err(|_| Error::Verify(format!("{} digest elements", digest.len())))
}

fn parse(json: &str) -> Result<RootInput, Error> {
    serde_json::from_str(json).map_err(|e| Error::Verify(format!("leaves JSON: {e}")))
}

fn root_leaves(input: &RootInput) -> Result<Vec<(Leaf, LeafProof)>, Error> {
    input.leaves.iter().map(root_leaf).collect()
}

/// Prepares `l`'s leaf with its proof and the statement the orchestrator expects of it.
fn root_leaf(l: &RootLeaf) -> Result<(Leaf, LeafProof), Error> {
    let level = SecurityLevel::parse(&l.security_level).ok_or_else(|| {
        Error::InvalidCircuit(format!("unknown security level {:?}", l.security_level))
    })?;
    let bytes = base64::engine::general_purpose::STANDARD
        .decode(&l.proof)
        .map_err(|e| Error::Verify(format!("leaf proof base64: {e}")))?;
    let proof = leaf::decode_proof(&bytes)?;
    let n = l.qubit_count as usize;
    let d = Dispatch {
        circuit_id: &l.circuit_id,
        sub_task_id: &l.sub_task_id,
        node_id: &l.node_id,
        slice_id: &l.slice_id,
    };
    if l.shots == 0 {
        let c = parse_circuit(&l.circuit)?;
        if !c.measures.is_empty() {
            return Err(Error::InvalidCircuit(
                "MEASURE in a circuit without shots".into(),
            ));
        }
        let statement = leaf::statement(d.context(), l.digest)?;
        return Ok((
            leaf::build(level, n, c.gates)?,
            LeafProof { proof, statement },
        ));
    }
    let c = parse_leaf(&l.circuit, n)?;
    let shots =
        u32::try_from(l.shots).map_err(|_| Error::InvalidCircuit(format!("{} shots", l.shots)))?;
    let sampling = Sampling {
        measures: c.measures,
        cbits: l.classical_bit_count as usize,
        shots,
    };
    let counts = parse_counts(&l.counts, &sampling)?;
    let statement =
        leaf::expected_sampling_statement(&sampling, &d, l.digest, l.sample_seed, &counts)?;
    let built = leaf::build_sampling(level, c.qubits, c.gates, sampling)?;
    Ok((built, LeafProof { proof, statement }))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Malformed input and too many leaves are refused before anything is built.
    #[test]
    fn refuses_before_verifying() {
        assert!(verify_wrap_json("not json", b"", b"").is_err());
        assert!(verify_root_json(r#"{"leaves":[{"qubit_count":1}]}"#, b"").is_err());
        let leaf = r#"{"qubit_count":1,"circuit":"[]","security_level":"low","circuit_id":"c","sub_task_id":"s","node_id":"n","slice_id":"0","digest":[0,0,0,0],"proof":"!"}"#;
        let many = format!(
            r#"{{"leaves":[{}]}}"#,
            [leaf; wrap::MAX_LEAVES + 1].join(",")
        );
        let err = verify_wrap_json(&many, b"", b"").unwrap_err();
        assert!(err.to_string().contains("more than"), "{err}");
        let err = verify_root_json(&format!(r#"{{"leaves":[{leaf}]}}"#), b"").unwrap_err();
        assert!(err.to_string().contains("base64"), "{err}");
    }
}

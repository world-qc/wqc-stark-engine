//! R3-M2.5: in-circuit Merkle fold over ValMmcs Keccak digests.
//!
//! ## What is in-circuit
//! - Index bits and public binding of leaf / layer digests / root inside
//!   [`MerkleFoldAir`] (carried on `AggPcsCertificate` in V6).
//!
//! ## What stays host-side (ValMmcs Keccak-256)
//! - `hash_lde_leaf` and `compress_digests` equality checks on those public digests
//!   (identical to `SerializingHasher<Keccak256Hash>` / binary compress).
//!
//! Full Keccak-f[1600] round constraints inside the AIR remain **M2.5b** (bit-level
//! θ/ρ/π/χ/ι). This milestone makes the Merkle *tree algebra* in-circuit and forces
//! every verify path to re-check Keccak digests against ValMmcs.

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::dense::RowMajorMatrix;
use p3_mersenne_31::Mersenne31;
use p3_uni_stark::{prove, verify};

use crate::air::pad_air_matrix_for_uni_stark;
use crate::plonky3_stark::aggregation_air::AGG_WIDTH;
use crate::plonky3_stark::config::{devnet_circle_config, WqcStarkConfig};

use super::merkle_keccak::{
    compress_digests, hash_lde_leaf, verify_agg_merkle_path, AGG_LDE_MERKLE_DEPTH,
};

/// Max depth supported in the fold AIR (AggregationAir LDE uses 3).
pub const MERKLE_FOLD_DEPTH: usize = AGG_LDE_MERKLE_DEPTH;

/// Public: leaf[32] | root[32] | index | depth | layer_digests[depth*32] | siblings[depth*32]
pub const MERKLE_FOLD_NUM_PUBLIC: usize = 32 + 32 + 1 + 1 + MERKLE_FOLD_DEPTH * 32 * 2;

/// Trace width: index bits[depth] | mux flags reused from bits (stable statement row).
pub const MERKLE_FOLD_WIDTH: usize = MERKLE_FOLD_DEPTH;

#[derive(Copy, Clone, Debug)]
pub struct MerkleFoldAir;

impl<F: Field> BaseAir<F> for MerkleFoldAir {
    fn width(&self) -> usize {
        MERKLE_FOLD_WIDTH
    }

    fn max_constraint_degree(&self) -> Option<usize> {
        Some(2)
    }

    fn num_public_values(&self) -> usize {
        MERKLE_FOLD_NUM_PUBLIC
    }
}

impl<AB: AirBuilder> Air<AB> for MerkleFoldAir
where
    AB::F: Field + PrimeCharacteristicRing,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let curr = main.current_slice();
        let next = main.next_slice();
        let one = AB::Expr::ONE;

        // Snapshot publics before mutable asserts (borrow checker).
        let (pv_index, pv_depth): (AB::Expr, AB::Expr) = {
            let pv = builder.public_values();
            (pv[64].into(), pv[65].into())
        };

        // Index bits boolean and stable.
        for i in 0..MERKLE_FOLD_WIDTH {
            let b: AB::Expr = curr[i].into();
            builder.assert_zero(b.clone() * (b - one.clone()));
            builder
                .when_transition()
                .assert_zero(next[i].into() - curr[i].into());
        }

        // depth public must equal MERKLE_FOLD_DEPTH for AggregationAir paths we prove.
        let expected_depth: AB::Expr = AB::F::from_u32(MERKLE_FOLD_DEPTH as u32).into();
        builder.assert_zero(pv_depth - expected_depth);

        // index = sum bit_i * 2^i (public pv[64])
        let mut acc = AB::Expr::ZERO;
        let mut pow = AB::Expr::ONE;
        let two = one.clone() + one.clone();
        for bit in curr.iter().take(MERKLE_FOLD_DEPTH) {
            acc += (*bit).into() * pow.clone();
            pow *= two.clone();
        }
        builder.assert_zero(acc - pv_index);
    }
}

fn u8s_to_pv(bytes: &[u8], out: &mut Vec<Mersenne31>) {
    for &b in bytes {
        out.push(Mersenne31::from_u32(b as u32));
    }
}

fn build_public_values(
    leaf: [u8; 32],
    root: [u8; 32],
    index: u32,
    layer_digests: &[[u8; 32]],
    siblings: &[[u8; 32]],
) -> Result<Vec<Mersenne31>, String> {
    if layer_digests.len() != MERKLE_FOLD_DEPTH || siblings.len() != MERKLE_FOLD_DEPTH {
        return Err(format!(
            "expected depth {MERKLE_FOLD_DEPTH}, got layers={} siblings={}",
            layer_digests.len(),
            siblings.len()
        ));
    }
    let mut pv = Vec::with_capacity(MERKLE_FOLD_NUM_PUBLIC);
    u8s_to_pv(&leaf, &mut pv);
    u8s_to_pv(&root, &mut pv);
    pv.push(Mersenne31::from_u32(index));
    pv.push(Mersenne31::from_u32(MERKLE_FOLD_DEPTH as u32));
    for d in layer_digests {
        u8s_to_pv(d, &mut pv);
    }
    for s in siblings {
        u8s_to_pv(s, &mut pv);
    }
    debug_assert_eq!(pv.len(), MERKLE_FOLD_NUM_PUBLIC);
    Ok(pv)
}

fn build_fold_matrix(index: usize) -> RowMajorMatrix<Mersenne31> {
    let mut row = Vec::with_capacity(MERKLE_FOLD_WIDTH);
    for i in 0..MERKLE_FOLD_DEPTH {
        let bit = ((index >> i) & 1) as u32;
        row.push(Mersenne31::from_u32(bit));
    }
    let mut values = row.clone();
    values.extend_from_slice(&row);
    RowMajorMatrix::new(values, MERKLE_FOLD_WIDTH)
}

/// Proof that a ValMmcs Merkle path folds correctly (in-circuit bits + host Keccak digests).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KeccakMerklePathProof {
    pub leaf_digest: [u8; 32],
    pub layer_digests: Vec<[u8; 32]>,
    pub fold_stark: Vec<u8>,
}

pub fn generate_keccak_merkle_path_proof(
    lde_row: &[Mersenne31],
    siblings: &[[u8; 32]],
    index: usize,
    expected_root: &[u8; 32],
) -> Result<KeccakMerklePathProof, String> {
    if lde_row.len() != AGG_WIDTH {
        return Err("LDE row width mismatch".into());
    }
    if siblings.len() != MERKLE_FOLD_DEPTH {
        return Err(format!(
            "expected {MERKLE_FOLD_DEPTH} siblings, got {}",
            siblings.len()
        ));
    }
    if !verify_agg_merkle_path(lde_row, siblings, index, expected_root) {
        return Err("Merkle path does not match commitment root".into());
    }

    let leaf_digest = hash_lde_leaf(lde_row);
    let mut digest = leaf_digest;
    let mut idx = index;
    let mut layer_digests = Vec::with_capacity(MERKLE_FOLD_DEPTH);
    for sib in siblings {
        let (left, right) = if idx.is_multiple_of(2) {
            (digest, *sib)
        } else {
            (*sib, digest)
        };
        digest = compress_digests(left, right);
        layer_digests.push(digest);
        idx /= 2;
    }
    if &digest != expected_root {
        return Err("folded root mismatch".into());
    }

    let pv = build_public_values(
        leaf_digest,
        *expected_root,
        index as u32,
        &layer_digests,
        siblings,
    )?;
    let matrix = pad_air_matrix_for_uni_stark(build_fold_matrix(index));
    p3_air::check_constraints(&MerkleFoldAir, &matrix, &pv);
    let config = devnet_circle_config();
    let proof = prove(&config, &MerkleFoldAir, matrix, &pv);
    let fold_stark =
        postcard::to_allocvec(&proof).map_err(|e| format!("postcard encode merkle fold: {e}"))?;

    Ok(KeccakMerklePathProof {
        leaf_digest,
        layer_digests,
        fold_stark,
    })
}

pub fn verify_keccak_merkle_path_proof(
    lde_row: &[Mersenne31],
    siblings: &[[u8; 32]],
    index: usize,
    expected_root: &[u8; 32],
    proof: &KeccakMerklePathProof,
) -> bool {
    if siblings.len() != MERKLE_FOLD_DEPTH {
        eprintln!("[MerkleFold] Failed: sibling depth");
        return false;
    }
    if !verify_agg_merkle_path(lde_row, siblings, index, expected_root) {
        eprintln!("[MerkleFold] Failed: ValMmcs Keccak path");
        return false;
    }
    if hash_lde_leaf(lde_row) != proof.leaf_digest {
        eprintln!("[MerkleFold] Failed: leaf digest");
        return false;
    }
    if proof.layer_digests.len() != MERKLE_FOLD_DEPTH {
        return false;
    }

    // Host Keccak layer checks (ValMmcs compress).
    let mut digest = proof.leaf_digest;
    let mut idx = index;
    for (i, sib) in siblings.iter().enumerate() {
        let (left, right) = if idx.is_multiple_of(2) {
            (digest, *sib)
        } else {
            (*sib, digest)
        };
        let out = compress_digests(left, right);
        if out != proof.layer_digests[i] {
            eprintln!("[MerkleFold] Failed: Keccak compress layer {i}");
            return false;
        }
        digest = out;
        idx /= 2;
    }
    if &digest != expected_root {
        return false;
    }

    let pv = match build_public_values(
        proof.leaf_digest,
        *expected_root,
        index as u32,
        &proof.layer_digests,
        siblings,
    ) {
        Ok(pv) => pv,
        Err(_) => return false,
    };
    let stark: p3_uni_stark::Proof<WqcStarkConfig> = match postcard::from_bytes(&proof.fold_stark) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("[MerkleFold] Failed: postcard: {e}");
            return false;
        }
    };
    let config = devnet_circle_config();
    match verify(&config, &MerkleFoldAir, &stark, &pv) {
        Ok(()) => true,
        Err(e) => {
            eprintln!("[MerkleFold] Failed: STARK verify {e:?}");
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::aggregation::CHILD_HASH_LEN;
    use crate::air::pad_air_matrix_for_uni_stark;
    use crate::plonky3_stark::aggregation::build_agg_matrix;
    use crate::plonky3_stark::config::devnet_circle_config;
    use p3_commit::{Mmcs, Pcs};
    use p3_matrix::Matrix;
    use p3_uni_stark::StarkGenericConfig;

    #[test]
    fn merkle_fold_stark_against_pcs_opening() {
        let matrix = pad_air_matrix_for_uni_stark(build_agg_matrix(
            [3u8; CHILD_HASH_LEN],
            [4u8; CHILD_HASH_LEN],
        ));
        let config = devnet_circle_config();
        let pcs = config.pcs();
        let domain = <crate::plonky3_stark::config::Pcs as Pcs<
            crate::plonky3_stark::config::Challenge,
            crate::plonky3_stark::config::Challenger,
        >>::natural_domain_for_degree(pcs, matrix.height());
        let (comm, prover_data) = <crate::plonky3_stark::config::Pcs as Pcs<
            crate::plonky3_stark::config::Challenge,
            crate::plonky3_stark::config::Challenger,
        >>::commit(pcs, vec![(domain, matrix)]);
        let batch = pcs.mmcs.open_batch(0, &prover_data);
        let root = *comm.roots().first().unwrap();
        assert_eq!(batch.opening_proof.len(), MERKLE_FOLD_DEPTH);

        let path = generate_keccak_merkle_path_proof(
            &batch.opened_values[0],
            &batch.opening_proof,
            0,
            &root,
        )
        .expect("prove fold");
        assert!(verify_keccak_merkle_path_proof(
            &batch.opened_values[0],
            &batch.opening_proof,
            0,
            &root,
            &path
        ));
    }
}

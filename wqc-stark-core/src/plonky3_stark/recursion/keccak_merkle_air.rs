//! R3-M2.5 / M2.5b: in-circuit Merkle fold + Keccak-256 sponge STARKs.
//!
//! ## In-circuit
//! - [`MerkleFoldAir`]: index bits / depth / public digest binding
//! - Nested [`Keccak256StarkProof`] for LDE leaf hash and each sibling compress
//!   (bit-level Keccak-f[1600] via [`super::keccak256_air`])
//!
//! ## Host (witness only)
//! - May call ValMmcs helpers while building witnesses.
//! - Verify path does **not** rely on host digest equality for soundness.

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::dense::RowMajorMatrix;
use p3_mersenne_31::Mersenne31;
use p3_uni_stark::{prove, verify};

use crate::air::pad_air_matrix_for_uni_stark;
use crate::plonky3_stark::aggregation_air::AGG_WIDTH;
use crate::plonky3_stark::config::{devnet_circle_config, WqcStarkConfig};

use super::keccak256_air::{
    prove_compress, prove_lde_leaf, verify_compress_digest, verify_lde_leaf_digest,
    Keccak256StarkProof,
};
use super::keccak_f_native::{keccak256_compress, keccak256_lde_leaf};
use super::merkle_keccak::AGG_LDE_MERKLE_DEPTH;

/// Max depth supported in the fold AIR (AggregationAir LDE uses 3).
pub const MERKLE_FOLD_DEPTH: usize = AGG_LDE_MERKLE_DEPTH;

/// Public: leaf[32] | root[32] | index | depth | layer_digests[depth*32] | siblings[depth*32]
pub const MERKLE_FOLD_NUM_PUBLIC: usize = 32 + 32 + 1 + 1 + MERKLE_FOLD_DEPTH * 32 * 2;

/// Trace width: index bits[depth].
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

        let (pv_index, pv_depth): (AB::Expr, AB::Expr) = {
            let pv = builder.public_values();
            (pv[64].into(), pv[65].into())
        };

        for i in 0..MERKLE_FOLD_WIDTH {
            let b: AB::Expr = curr[i].into();
            builder.assert_zero(b.clone() * (b - one.clone()));
            builder
                .when_transition()
                .assert_zero(next[i].into() - curr[i].into());
        }

        let expected_depth: AB::Expr = AB::F::from_u32(MERKLE_FOLD_DEPTH as u32).into();
        builder.assert_zero(pv_depth - expected_depth);

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

/// Proof that a ValMmcs Merkle path is correct (fold AIR + in-circuit Keccak sponges).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KeccakMerklePathProof {
    pub leaf_digest: [u8; 32],
    pub layer_digests: Vec<[u8; 32]>,
    pub fold_stark: Vec<u8>,
    /// R3-M2.5b: Keccak-256 sponge STARK for the LDE leaf hash.
    pub leaf_keccak: Keccak256StarkProof,
    /// R3-M2.5b: one compress sponge STARK per Merkle layer.
    pub compress_starks: Vec<Keccak256StarkProof>,
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

    let leaf_keccak = prove_lde_leaf(lde_row)?;
    let leaf_digest = leaf_keccak.digest;
    if leaf_digest != keccak256_lde_leaf(lde_row) {
        return Err("leaf sponge digest mismatch vs native".into());
    }

    let mut digest = leaf_digest;
    let mut idx = index;
    let mut layer_digests = Vec::with_capacity(MERKLE_FOLD_DEPTH);
    let mut compress_starks = Vec::with_capacity(MERKLE_FOLD_DEPTH);
    for sib in siblings {
        let (left, right) = if idx.is_multiple_of(2) {
            (digest, *sib)
        } else {
            (*sib, digest)
        };
        let cproof = prove_compress(left, right)?;
        if cproof.digest != keccak256_compress(left, right) {
            return Err("compress sponge digest mismatch vs native".into());
        }
        digest = cproof.digest;
        layer_digests.push(digest);
        compress_starks.push(cproof);
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
    let fold_stark = super::prove_workspace::encode_stark_and_drop(proof, "merkle fold")?;

    Ok(KeccakMerklePathProof {
        leaf_digest,
        layer_digests,
        fold_stark,
        leaf_keccak,
        compress_starks,
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
    if proof.layer_digests.len() != MERKLE_FOLD_DEPTH
        || proof.compress_starks.len() != MERKLE_FOLD_DEPTH
    {
        eprintln!("[MerkleFold] Failed: layer/compress count");
        return false;
    }
    if proof.leaf_digest != proof.leaf_keccak.digest {
        eprintln!("[MerkleFold] Failed: leaf_digest vs leaf_keccak");
        return false;
    }
    if !verify_lde_leaf_digest(lde_row, &proof.leaf_digest, &proof.leaf_keccak) {
        eprintln!("[MerkleFold] Failed: leaf Keccak sponge");
        return false;
    }

    let mut digest = proof.leaf_digest;
    let mut idx = index;
    for (i, sib) in siblings.iter().enumerate() {
        let (left, right) = if idx.is_multiple_of(2) {
            (digest, *sib)
        } else {
            (*sib, digest)
        };
        let expected = proof.layer_digests[i];
        if !verify_compress_digest(left, right, &expected, &proof.compress_starks[i]) {
            eprintln!("[MerkleFold] Failed: compress sponge layer {i}");
            return false;
        }
        digest = expected;
        idx /= 2;
    }
    if &digest != expected_root {
        eprintln!("[MerkleFold] Failed: root mismatch");
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
    use crate::plonky3_stark::recursion::merkle_keccak::{
        hash_lde_leaf, merkle_root_from_path_keccak,
    };
    use p3_field::PrimeCharacteristicRing;

    #[test]
    fn merkle_fold_stark_against_synthetic_keccak_path() {
        // Keccak fold AIR is independent of production Poseidon ValMmcs.
        let lde_row: Vec<_> = (0..AGG_WIDTH)
            .map(|i| Mersenne31::from_u32(i as u32 + 1))
            .collect();
        let leaf = hash_lde_leaf(&lde_row);
        let siblings = [[9u8; 32]; MERKLE_FOLD_DEPTH];
        let root = merkle_root_from_path_keccak(leaf, &siblings, 0);

        let path =
            generate_keccak_merkle_path_proof(&lde_row, &siblings, 0, &root).expect("prove fold");
        assert!(verify_keccak_merkle_path_proof(
            &lde_row, &siblings, 0, &root, &path
        ));
    }
}

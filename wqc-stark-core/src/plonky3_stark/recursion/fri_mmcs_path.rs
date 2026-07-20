//! R3-M3d: variable-depth ValMmcs / flattened-ChallengeMmcs Merkle path STARKs.
//!
//! Single-matrix binary paths (cap_height=0) with in-circuit Keccak leaf + compress.
//! Statement LDE path (depth=3, W=66) remains in [`super::keccak_merkle_air`].
//!
//! Fold AIR uses degree-2 active-bit selectors so AggregationAir-sized paths can use
//! [`devnet_circle_config`] (not the Keccak blowup).

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::dense::RowMajorMatrix;
use p3_mersenne_31::Mersenne31;
use p3_uni_stark::{prove, verify};

use crate::air::pad_air_matrix_for_uni_stark;
use crate::plonky3_stark::config::{devnet_circle_config, WqcStarkConfig};

use super::keccak256_air::{
    prove_compress, prove_val_leaf, verify_compress_digest, verify_val_leaf_digest,
    Keccak256StarkProof,
};
use super::keccak_f_native::{keccak256_compress, keccak256_val_leaf};
use super::merkle_keccak::hash_val_leaf;

/// Max Merkle depth for FRI Mmcs paths (matches [`super::opening_cert::AGG_PCS_MAX_SIBLINGS`]).
pub const FRI_MMCS_MAX_DEPTH: usize = 8;

/// Public: leaf[32] | root[32] | index | depth | layer[MAX*32] | siblings[MAX*32]
pub const FRI_MMCS_FOLD_NUM_PUBLIC: usize = 32 + 32 + 1 + 1 + FRI_MMCS_MAX_DEPTH * 32 * 2;

/// Trace: index bits[MAX] | active flags[MAX] (active[i]=1 iff layer i is used).
pub const FRI_MMCS_FOLD_WIDTH: usize = FRI_MMCS_MAX_DEPTH * 2;

#[derive(Copy, Clone, Debug)]
pub struct FriMmcsFoldAir;

impl<F: Field> BaseAir<F> for FriMmcsFoldAir {
    fn width(&self) -> usize {
        FRI_MMCS_FOLD_WIDTH
    }

    fn max_constraint_degree(&self) -> Option<usize> {
        Some(2)
    }

    fn num_public_values(&self) -> usize {
        FRI_MMCS_FOLD_NUM_PUBLIC
    }
}

impl<AB: AirBuilder> Air<AB> for FriMmcsFoldAir
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

        for i in 0..FRI_MMCS_FOLD_WIDTH {
            let b: AB::Expr = curr[i].into();
            builder.assert_zero(b.clone() * (b - one.clone()));
            builder
                .when_transition()
                .assert_zero(next[i].into() - curr[i].into());
        }

        let bits = &curr[..FRI_MMCS_MAX_DEPTH];
        let active = &curr[FRI_MMCS_MAX_DEPTH..];

        // active[0] = 1 (depth ≥ 1); active is prefix-1 then zeros.
        builder.assert_zero(AB::Expr::from(active[0]) - one.clone());
        for i in 1..FRI_MMCS_MAX_DEPTH {
            let a: AB::Expr = active[i].into();
            let prev: AB::Expr = active[i - 1].into();
            // a_i ⇒ a_{i-1}
            builder.assert_zero(a * (one.clone() - prev));
        }

        let mut depth_acc = AB::Expr::ZERO;
        for a in active.iter().take(FRI_MMCS_MAX_DEPTH) {
            depth_acc += AB::Expr::from(*a);
        }
        builder.assert_zero(depth_acc - pv_depth);

        // Inactive index bits must be zero.
        for (b_cell, a_cell) in bits.iter().zip(active.iter()).take(FRI_MMCS_MAX_DEPTH) {
            let b: AB::Expr = (*b_cell).into();
            let a: AB::Expr = (*a_cell).into();
            builder.assert_zero(b * (one.clone() - a));
        }

        let mut acc = AB::Expr::ZERO;
        let mut pow = one.clone();
        let two = one.clone() + one.clone();
        for bit in bits.iter().take(FRI_MMCS_MAX_DEPTH) {
            acc += AB::Expr::from(*bit) * pow.clone();
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
    depth: usize,
    layer_digests: &[[u8; 32]],
    siblings: &[[u8; 32]],
) -> Result<Vec<Mersenne31>, String> {
    if depth == 0 || depth > FRI_MMCS_MAX_DEPTH {
        return Err(format!("depth {depth} out of range"));
    }
    if layer_digests.len() != depth || siblings.len() != depth {
        return Err(format!(
            "expected depth {depth}, got layers={} siblings={}",
            layer_digests.len(),
            siblings.len()
        ));
    }
    let mut pv = Vec::with_capacity(FRI_MMCS_FOLD_NUM_PUBLIC);
    u8s_to_pv(&leaf, &mut pv);
    u8s_to_pv(&root, &mut pv);
    pv.push(Mersenne31::from_u32(index));
    pv.push(Mersenne31::from_u32(depth as u32));
    for d in layer_digests
        .iter()
        .chain(std::iter::repeat(&[0u8; 32]))
        .take(FRI_MMCS_MAX_DEPTH)
    {
        u8s_to_pv(d, &mut pv);
    }
    for s in siblings
        .iter()
        .chain(std::iter::repeat(&[0u8; 32]))
        .take(FRI_MMCS_MAX_DEPTH)
    {
        u8s_to_pv(s, &mut pv);
    }
    debug_assert_eq!(pv.len(), FRI_MMCS_FOLD_NUM_PUBLIC);
    Ok(pv)
}

fn build_fold_matrix(index: usize, depth: usize) -> RowMajorMatrix<Mersenne31> {
    let mut row = Vec::with_capacity(FRI_MMCS_FOLD_WIDTH);
    for i in 0..FRI_MMCS_MAX_DEPTH {
        let bit = if i < depth {
            ((index >> i) & 1) as u32
        } else {
            0
        };
        row.push(Mersenne31::from_u32(bit));
    }
    for i in 0..FRI_MMCS_MAX_DEPTH {
        row.push(Mersenne31::from_u32(if i < depth { 1 } else { 0 }));
    }
    let mut values = row.clone();
    values.extend_from_slice(&row);
    RowMajorMatrix::new(values, FRI_MMCS_FOLD_WIDTH)
}

/// In-circuit Merkle path for a single ValMmcs (or flattened Challenge) matrix.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FriMmcsPathProof {
    pub depth: u32,
    pub leaf_width: u32,
    pub leaf_digest: [u8; 32],
    pub layer_digests: Vec<[u8; 32]>,
    pub fold_stark: Vec<u8>,
    pub leaf_keccak: Keccak256StarkProof,
    pub compress_starks: Vec<Keccak256StarkProof>,
}

/// Prove a binary Merkle path for an arbitrary-width M31 leaf row.
pub fn generate_fri_mmcs_path_proof(
    row: &[Mersenne31],
    siblings: &[[u8; 32]],
    index: usize,
    expected_root: &[u8; 32],
) -> Result<FriMmcsPathProof, String> {
    let depth = siblings.len();
    if depth == 0 || depth > FRI_MMCS_MAX_DEPTH {
        return Err(format!("unsupported Merkle depth {depth}"));
    }
    let leaf_keccak = prove_val_leaf(row)?;
    let leaf_digest = leaf_keccak.digest;
    if leaf_digest != keccak256_val_leaf(row) || leaf_digest != hash_val_leaf(row) {
        return Err("leaf digest mismatch vs native/FieldHash".into());
    }

    let mut digest = leaf_digest;
    let mut idx = index;
    let mut layer_digests = Vec::with_capacity(depth);
    let mut compress_starks = Vec::with_capacity(depth);
    for sib in siblings {
        let (left, right) = if idx.is_multiple_of(2) {
            (digest, *sib)
        } else {
            (*sib, digest)
        };
        let cproof = prove_compress(left, right)?;
        if cproof.digest != keccak256_compress(left, right) {
            return Err("compress digest mismatch".into());
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
        depth,
        &layer_digests,
        siblings,
    )?;
    let matrix = pad_air_matrix_for_uni_stark(build_fold_matrix(index, depth));
    p3_air::check_constraints(&FriMmcsFoldAir, &matrix, &pv);
    let config = devnet_circle_config();
    let proof = prove(&config, &FriMmcsFoldAir, matrix, &pv);
    let fold_stark =
        postcard::to_allocvec(&proof).map_err(|e| format!("postcard encode fri mmcs fold: {e}"))?;

    Ok(FriMmcsPathProof {
        depth: depth as u32,
        leaf_width: row.len() as u32,
        leaf_digest,
        layer_digests,
        fold_stark,
        leaf_keccak,
        compress_starks,
    })
}

pub fn verify_fri_mmcs_path_proof(
    row: &[Mersenne31],
    siblings: &[[u8; 32]],
    index: usize,
    expected_root: &[u8; 32],
    proof: &FriMmcsPathProof,
) -> bool {
    let depth = proof.depth as usize;
    if siblings.len() != depth
        || proof.layer_digests.len() != depth
        || proof.compress_starks.len() != depth
        || row.len() as u32 != proof.leaf_width
        || depth == 0
        || depth > FRI_MMCS_MAX_DEPTH
    {
        eprintln!("[FriMmcsPath] Failed: shape");
        return false;
    }
    if proof.leaf_digest != proof.leaf_keccak.digest {
        eprintln!("[FriMmcsPath] Failed: leaf_digest vs keccak");
        return false;
    }
    if !verify_val_leaf_digest(row, &proof.leaf_digest, &proof.leaf_keccak) {
        eprintln!("[FriMmcsPath] Failed: leaf sponge");
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
            eprintln!("[FriMmcsPath] Failed: compress layer {i}");
            return false;
        }
        digest = expected;
        idx /= 2;
    }
    if &digest != expected_root {
        eprintln!("[FriMmcsPath] Failed: root");
        return false;
    }
    let pv = match build_public_values(
        proof.leaf_digest,
        *expected_root,
        index as u32,
        depth,
        &proof.layer_digests,
        siblings,
    ) {
        Ok(pv) => pv,
        Err(_) => return false,
    };
    let stark: p3_uni_stark::Proof<WqcStarkConfig> = match postcard::from_bytes(&proof.fold_stark) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("[FriMmcsPath] postcard: {e}");
            return false;
        }
    };
    let config = devnet_circle_config();
    match verify(&config, &FriMmcsFoldAir, &stark, &pv) {
        Ok(()) => true,
        Err(e) => {
            eprintln!("[FriMmcsPath] STARK: {e:?}");
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_field::PrimeCharacteristicRing;

    #[test]
    fn fri_mmcs_path_quot_width3_depth1() {
        let row = [
            Mersenne31::from_u32(1),
            Mersenne31::from_u32(2),
            Mersenne31::from_u32(3),
        ];
        let leaf = hash_val_leaf(&row);
        let sibling = [9u8; 32];
        let root = keccak256_compress(leaf, sibling);
        let proof = generate_fri_mmcs_path_proof(&row, &[sibling], 0, &root).expect("prove");
        assert!(verify_fri_mmcs_path_proof(
            &row,
            &[sibling],
            0,
            &root,
            &proof
        ));
    }

    #[test]
    fn fri_mmcs_path_chal_width6() {
        let row: Vec<_> = (0..6)
            .map(|i| Mersenne31::from_u32(i as u32 + 10))
            .collect();
        let leaf = hash_val_leaf(&row);
        let sibling = [3u8; 32];
        let root = keccak256_compress(sibling, leaf); // index=1
        let proof = generate_fri_mmcs_path_proof(&row, &[sibling], 1, &root).expect("prove");
        assert!(verify_fri_mmcs_path_proof(
            &row,
            &[sibling],
            1,
            &root,
            &proof
        ));
    }
}

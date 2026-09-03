//! E5b prototype: Poseidon2 Mmcs group fold parallel to [`super::fri_mmcs_group_m4b`].
//!
//! Replaces Keccak sponge segments (width ~1657) with width-16 Poseidon2 perm traces (width 21).
//!
//! Public values (`depth` = max path depth; unused high slots are zero):
//! `path_count | max_depth | [shared_root[8]]`
//! `×path { leaf_row[W] | leaf_digest[8] | [root[8]] | depth_onehot[max_depth]
//!   | index_bits[max_depth] | siblings[max_depth×8] }`.
//! `depth_onehot[i]` is boolean, sums to 1, and means `path_depth == i+1`.
//! Intermediate Merkle digests chain via segment-boundary transitions; the final
//! compress output binds to `root` at segment `n_leaf + d - 1` when `onehot[d-1]`.

#![allow(clippy::needless_range_loop)]

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_mersenne_31::Mersenne31;
use p3_uni_stark::{prove, verify};

use crate::air::pad_air_matrix_for_uni_stark;
use crate::plonky3_stark::config::{
    devnet_circle_config, devnet_circle_config_with_queries, WqcStarkConfig, DEVNET_FRI_NUM_QUERIES,
};

use super::fri_mmcs_group_m4b::{
    roots_are_shared, MmcsPathStatement, M4B_MAX_PATHS, M4B_PATH_IDX_BITS,
};
use super::fri_mmcs_path::FRI_MMCS_MAX_DEPTH;
use super::fri_mmcs_path_m4a::M4A_SEG_IDX_BITS;
use super::merkle_poseidon2::{
    compress_digests_poseidon, hash_val_leaf_poseidon, leaf_perm_state,
    merkle_root_from_path_poseidon, poseidon_compress_perm_input, poseidon_leaf_perm_count,
    poseidon_m4b_width_eligible,
};
use super::poseidon2_perm_air::{
    build_perm_trace, constrain_external, constrain_internal, constrain_mds_only,
    selector_for_step, POSEIDON2_LIVE_COL, POSEIDON2_PERM_STEPS, POSEIDON2_PERM_WIDTH,
    POSEIDON2_STEP_BITS, POSEIDON2_STEP_COL,
};
use super::poseidon2_spike::POSEIDON2_WIDTH;
use crate::plonky3_stark::config_poseidon::POSEIDON_RATE;

pub const P2_SEG_START_COL: usize = POSEIDON2_PERM_WIDTH;
pub const P2_SEG_IDX_COL: usize = POSEIDON2_PERM_WIDTH + 1;
pub const P2_PATH_IDX_COL: usize = P2_SEG_IDX_COL + M4A_SEG_IDX_BITS;

pub const POSEIDON2_GROUP_WIDTH: usize =
    POSEIDON2_PERM_WIDTH + 1 + M4A_SEG_IDX_BITS + M4B_PATH_IDX_BITS;

const DIGEST_LIMBS: usize = 8;

/// Poseidon2 Mmcs group proof (homogeneous or mixed depth ≤ `depth` = max_depth).
///
/// Leaf and layer digests are **not** carried: the verifier recomputes them from the
/// path statements it already holds.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PoseidonGroupFoldProof {
    pub path_count: u32,
    pub depth: u32,
    pub leaf_width: u32,
    pub group_stark: Vec<u8>,
}

#[derive(Copy, Clone, Debug)]
pub struct PoseidonMmcsGroupPathAir {
    pub leaf_width: usize,
    pub depth: usize,
    pub path_count: usize,
    /// All paths open the same commitment: one `root[8]` in the header instead of per path.
    pub shared_root: bool,
}

/// `path_count | depth` plus the shared `root[8]` when every path shares one root.
fn p2_header_len(shared_root: bool) -> usize {
    if shared_root {
        2 + DIGEST_LIMBS
    } else {
        2
    }
}

fn pv_shared_root_off() -> usize {
    2
}

/// Per-path PV stride: leaf | leaf_digest | [root] | onehot[D] | index_bits[D] | siblings[D×8].
fn p2_path_stride(leaf_width: usize, depth: usize, shared_root: bool) -> usize {
    let root_limbs = if shared_root { 0 } else { DIGEST_LIMBS };
    leaf_width + DIGEST_LIMBS + root_limbs + depth + depth + depth * DIGEST_LIMBS
}

fn p2_num_public(leaf_width: usize, depth: usize, path_count: usize, shared_root: bool) -> usize {
    p2_header_len(shared_root) + path_count * p2_path_stride(leaf_width, depth, shared_root)
}

fn pv_path_base(path: usize, leaf_width: usize, depth: usize, shared_root: bool) -> usize {
    p2_header_len(shared_root) + path * p2_path_stride(leaf_width, depth, shared_root)
}
fn pv_leaf_digest_off(path: usize, leaf_width: usize, depth: usize, shared_root: bool) -> usize {
    pv_path_base(path, leaf_width, depth, shared_root) + leaf_width
}
/// Per-path root slot; folds onto the header slot when `shared_root`.
fn pv_root_off(path: usize, leaf_width: usize, depth: usize, shared_root: bool) -> usize {
    if shared_root {
        pv_shared_root_off()
    } else {
        pv_leaf_digest_off(path, leaf_width, depth, shared_root) + DIGEST_LIMBS
    }
}
fn pv_onehot_off(path: usize, leaf_width: usize, depth: usize, shared_root: bool) -> usize {
    let root_limbs = if shared_root { 0 } else { DIGEST_LIMBS };
    pv_leaf_digest_off(path, leaf_width, depth, shared_root) + DIGEST_LIMBS + root_limbs
}
fn pv_index_bits_off(path: usize, leaf_width: usize, depth: usize, shared_root: bool) -> usize {
    pv_onehot_off(path, leaf_width, depth, shared_root) + depth
}
fn pv_siblings_off(path: usize, leaf_width: usize, depth: usize, shared_root: bool) -> usize {
    pv_index_bits_off(path, leaf_width, depth, shared_root) + depth
}

impl<F: Field> BaseAir<F> for PoseidonMmcsGroupPathAir {
    fn width(&self) -> usize {
        POSEIDON2_GROUP_WIDTH
    }

    fn max_constraint_degree(&self) -> Option<usize> {
        None
    }

    fn num_public_values(&self) -> usize {
        p2_num_public(
            self.leaf_width,
            self.depth,
            self.path_count,
            self.shared_root,
        )
    }
}

fn bool_m31(b: bool) -> Mersenne31 {
    if b {
        Mersenne31::ONE
    } else {
        Mersenne31::ZERO
    }
}

fn eq_bits_const<AB: AirBuilder>(bits: &[AB::Var], target: u32) -> AB::Expr
where
    AB::F: PrimeCharacteristicRing,
{
    let mut sel = AB::Expr::ONE;
    for (k, bit) in bits.iter().enumerate() {
        let b: AB::Expr = (*bit).into();
        if ((target >> k) & 1) == 1 {
            sel *= b;
        } else {
            sel *= AB::Expr::ONE - b;
        }
    }
    sel
}

fn digest_bytes_to_limbs(d: [u8; 32]) -> [Mersenne31; DIGEST_LIMBS] {
    core::array::from_fn(|i| {
        let off = i * 4;
        Mersenne31::new(u32::from_le_bytes(d[off..off + 4].try_into().unwrap()))
    })
}

fn compress_state(left: [u8; 32], right: [u8; 32]) -> [Mersenne31; POSEIDON2_WIDTH] {
    poseidon_compress_perm_input(left, right)
}

fn push_row_meta(values: &mut Vec<Mersenne31>, seg_start: bool, seg_idx: usize, path_idx: usize) {
    values.push(bool_m31(seg_start));
    for k in 0..M4A_SEG_IDX_BITS {
        values.push(bool_m31(((seg_idx >> k) & 1) == 1));
    }
    for k in 0..M4B_PATH_IDX_BITS {
        values.push(bool_m31(((path_idx >> k) & 1) == 1));
    }
}

fn append_perm_segment(
    values: &mut Vec<Mersenne31>,
    input: [Mersenne31; POSEIDON2_WIDTH],
    seg_idx: usize,
    path_idx: usize,
) {
    let trace = build_perm_trace(input);
    for r in 0..trace.height() {
        let start = r * POSEIDON2_PERM_WIDTH;
        values.extend_from_slice(&trace.values[start..start + POSEIDON2_PERM_WIDTH]);
        push_row_meta(values, r == 0, seg_idx, path_idx);
    }
}

fn build_group_matrix(
    paths: &[(Vec<Mersenne31>, Vec<[Mersenne31; POSEIDON2_WIDTH]>)],
) -> RowMajorMatrix<Mersenne31> {
    let mut values = Vec::new();
    for (p, (row, compress_inputs)) in paths.iter().enumerate() {
        let n_leaf = poseidon_leaf_perm_count(row.len());
        for k in 0..n_leaf {
            append_perm_segment(&mut values, leaf_perm_state(row, k), k, p);
        }
        for (layer, input) in compress_inputs.iter().enumerate() {
            append_perm_segment(&mut values, *input, n_leaf + layer, p);
        }
    }
    let active_rows = values.len() / POSEIDON2_GROUP_WIDTH;
    let mut matrix =
        pad_air_matrix_for_uni_stark(RowMajorMatrix::new(values, POSEIDON2_GROUP_WIDTH));
    for r in active_rows..matrix.height() {
        matrix.values[r * POSEIDON2_GROUP_WIDTH + POSEIDON2_LIVE_COL] = Mersenne31::ZERO;
    }
    matrix
}

impl<AB: AirBuilder> Air<AB> for PoseidonMmcsGroupPathAir
where
    AB::F: Field + PrimeCharacteristicRing,
{
    fn eval(&self, builder: &mut AB) {
        let leaf_width = self.leaf_width;
        let depth = self.depth;
        let path_count = self.path_count;
        let shared = self.shared_root;
        let main = builder.main();
        let local = main.current_slice();
        let next = main.next_slice();
        let pv: Vec<AB::Expr> = builder
            .public_values()
            .iter()
            .map(|v| (*v).into())
            .collect();
        let one = AB::Expr::ONE;
        let two = AB::Expr::TWO;
        let is_tr = builder.is_transition();

        let curr_state: [AB::Var; POSEIDON2_WIDTH] = core::array::from_fn(|i| local[i]);
        let next_state: [AB::Var; POSEIDON2_WIDTH] = core::array::from_fn(|i| next[i]);
        let step_bits: [AB::Var; POSEIDON2_STEP_BITS] =
            core::array::from_fn(|i| local[POSEIDON2_STEP_COL + i]);
        let live_c: AB::Expr = local[POSEIDON2_LIVE_COL].into();
        let live_n: AB::Expr = next[POSEIDON2_LIVE_COL].into();
        let both_live = live_c.clone() * live_n.clone();
        let end_active = live_c.clone() * (one.clone() - live_n.clone());
        let seg_start_c: AB::Expr = local[P2_SEG_START_COL].into();
        let seg_bits_c: [AB::Var; M4A_SEG_IDX_BITS] =
            core::array::from_fn(|i| local[P2_SEG_IDX_COL + i]);
        let path_bits_c: [AB::Var; M4B_PATH_IDX_BITS] =
            core::array::from_fn(|i| local[P2_PATH_IDX_COL + i]);

        let seg_start_n: AB::Expr = next[P2_SEG_START_COL].into();
        let seg_bits_n: [AB::Var; M4A_SEG_IDX_BITS] =
            core::array::from_fn(|i| next[P2_SEG_IDX_COL + i]);
        let path_bits_n: [AB::Var; M4B_PATH_IDX_BITS] =
            core::array::from_fn(|i| next[P2_PATH_IDX_COL + i]);

        builder.assert_bools(step_bits);
        builder.assert_bools(seg_bits_c);
        builder.assert_bools(path_bits_c);
        builder.assert_bools([local[POSEIDON2_LIVE_COL]]);

        let mut same_meta = one.clone();
        for k in 0..M4A_SEG_IDX_BITS {
            let c: AB::Expr = seg_bits_c[k].into();
            let n: AB::Expr = seg_bits_n[k].into();
            same_meta *= one.clone() - (c.clone() + n.clone() - two.clone() * c * n);
        }
        for k in 0..M4B_PATH_IDX_BITS {
            let c: AB::Expr = path_bits_c[k].into();
            let n: AB::Expr = path_bits_n[k].into();
            same_meta *= one.clone() - (c.clone() + n.clone() - two.clone() * c * n);
        }
        let cont = is_tr.clone() * same_meta.clone() * both_live.clone();

        // In-segment Poseidon2 perm transitions.
        for step in 0..POSEIDON2_PERM_STEPS {
            let sel = selector_for_step::<AB>(&step_bits, step);
            let enable = cont.clone() * sel;
            match step {
                0 => constrain_mds_only(builder, &curr_state, &next_state, enable),
                1..=4 => {
                    let rc = &p3_mersenne_31::MERSENNE31_POSEIDON2_RC_16_EXTERNAL_INITIAL[step - 1];
                    constrain_external(builder, &curr_state, &next_state, rc, enable);
                }
                5..=18 => {
                    let rc = p3_mersenne_31::MERSENNE31_POSEIDON2_RC_16_INTERNAL[step - 5];
                    constrain_internal(builder, &curr_state, &next_state, rc, enable);
                }
                19..=22 => {
                    let rc = &p3_mersenne_31::MERSENNE31_POSEIDON2_RC_16_EXTERNAL_FINAL[step - 19];
                    constrain_external(builder, &curr_state, &next_state, rc, enable);
                }
                _ => unreachable!(),
            }
        }

        builder.assert_zero(pv[0].clone() - AB::Expr::from(AB::F::from_u32(path_count as u32)));
        builder.assert_zero(pv[1].clone() - AB::Expr::from(AB::F::from_u32(depth as u32)));

        let n_leaf = poseidon_leaf_perm_count(leaf_width);

        for p in 0..path_count {
            let path_sel = eq_bits_const::<AB>(&path_bits_c, p as u32);
            let path_sel_n = eq_bits_const::<AB>(&path_bits_n, p as u32);
            let row_base = pv_path_base(p, leaf_width, depth, shared);
            let leaf_d_base = pv_leaf_digest_off(p, leaf_width, depth, shared);
            let root_base = pv_root_off(p, leaf_width, depth, shared);
            let oh_base = pv_onehot_off(p, leaf_width, depth, shared);
            let idx_bits_base = pv_index_bits_off(p, leaf_width, depth, shared);
            let sib_base = pv_siblings_off(p, leaf_width, depth, shared);

            let mut oh_sum = AB::Expr::ZERO;
            for i in 0..depth {
                let bit = pv[oh_base + i].clone();
                builder.assert_zero(bit.clone() * (bit.clone() - one.clone()));
                oh_sum += bit;
            }
            builder.assert_zero(oh_sum - one.clone());
            for layer in 0..depth {
                let mut layer_active = AB::Expr::ZERO;
                for i in layer..depth {
                    layer_active += pv[oh_base + i].clone();
                }
                let unused = one.clone() - layer_active;
                builder.assert_zero(unused.clone() * pv[idx_bits_base + layer].clone());
                for limb in 0..DIGEST_LIMBS {
                    builder.assert_zero(
                        unused.clone() * pv[sib_base + layer * DIGEST_LIMBS + limb].clone(),
                    );
                }
            }

            // Leaf sponge segment starts (RATE=8 overwrite absorb + capacity carry).
            for k in 0..n_leaf {
                let leaf_start = seg_start_c.clone()
                    * eq_bits_const::<AB>(&seg_bits_c, k as u32)
                    * path_sel.clone();
                let off = k * POSEIDON_RATE;
                for i in 0..POSEIDON_RATE {
                    let row_i = off + i;
                    if row_i < leaf_width {
                        builder.assert_zero(
                            leaf_start.clone()
                                * (AB::Expr::from(curr_state[i]) - pv[row_base + row_i].clone()),
                        );
                    } else if n_leaf == 1 {
                        // Single-perm partial leaf: unused rate starts at zero.
                        builder.assert_zero(leaf_start.clone() * AB::Expr::from(curr_state[i]));
                    }
                    // Multi-perm partial tail: remaining rate slots carry the
                    // previous perm output (not zero); segment-boundary
                    // constraints + perm trace witness enforce the sponge.
                }
                if k == 0 {
                    for i in POSEIDON_RATE..POSEIDON2_WIDTH {
                        builder.assert_zero(leaf_start.clone() * AB::Expr::from(curr_state[i]));
                    }
                }
            }
            // Capacity continuity across leaf sponge perms: next leaf seg keeps prior capacity.
            for k in 1..n_leaf {
                let leaf_next = is_tr.clone()
                    * seg_start_n.clone()
                    * eq_bits_const::<AB>(&seg_bits_n, k as u32)
                    * path_sel_n.clone();
                for i in POSEIDON_RATE..POSEIDON2_WIDTH {
                    builder.assert_zero(
                        leaf_next.clone()
                            * (AB::Expr::from(next_state[i]) - AB::Expr::from(curr_state[i])),
                    );
                }
            }

            // Compress layer 0 start: left‖right from leaf_digest PV + sibling[0].
            // Enabled when depth ≥ 1 (`sum onehot[i] for i≥0`).
            {
                let mut layer_active = AB::Expr::ZERO;
                for i in 0..depth {
                    layer_active += pv[oh_base + i].clone();
                }
                let start = seg_start_c.clone()
                    * eq_bits_const::<AB>(&seg_bits_c, n_leaf as u32)
                    * path_sel.clone()
                    * layer_active;
                let bit = pv[idx_bits_base].clone();
                let not_bit = one.clone() - bit.clone();
                for limb in 0..DIGEST_LIMBS {
                    let prev = pv[leaf_d_base + limb].clone();
                    let sib = pv[sib_base + limb].clone();
                    let left = not_bit.clone() * prev.clone() + bit.clone() * sib.clone();
                    let right = bit.clone() * prev + not_bit.clone() * sib;
                    builder.assert_zero(start.clone() * (AB::Expr::from(curr_state[limb]) - left));
                    builder.assert_zero(
                        start.clone() * (AB::Expr::from(curr_state[DIGEST_LIMBS + limb]) - right),
                    );
                }
            }

            // Compress layers L>0: chain digest from previous segment output on the
            // boundary transition (prev = curr_state[0..8]), siblings/bits from PV.
            // Layer L is live iff path_depth > L (`sum_{i=L}^{max-1} onehot[i]`).
            for layer in 1..depth {
                let mut layer_active = AB::Expr::ZERO;
                for i in layer..depth {
                    layer_active += pv[oh_base + i].clone();
                }
                let start_next = is_tr.clone()
                    * seg_start_n.clone()
                    * eq_bits_const::<AB>(&seg_bits_n, (n_leaf + layer) as u32)
                    * path_sel_n.clone()
                    * layer_active;
                let bit = pv[idx_bits_base + layer].clone();
                let not_bit = one.clone() - bit.clone();
                for limb in 0..DIGEST_LIMBS {
                    let prev: AB::Expr = curr_state[limb].into();
                    let sib = pv[sib_base + layer * DIGEST_LIMBS + limb].clone();
                    let left = not_bit.clone() * prev.clone() + bit.clone() * sib.clone();
                    let right = bit.clone() * prev + not_bit.clone() * sib;
                    builder.assert_zero(
                        start_next.clone() * (AB::Expr::from(next_state[limb]) - left),
                    );
                    builder.assert_zero(
                        start_next.clone()
                            * (AB::Expr::from(next_state[DIGEST_LIMBS + limb]) - right),
                    );
                }
            }

            // Segment outputs bind when the next row starts a new segment or padding begins.
            let end_seg = is_tr.clone() * seg_start_n.clone() * live_n.clone();
            let bind_out = end_seg + end_active.clone();
            let leaf_out = bind_out.clone()
                * eq_bits_const::<AB>(&seg_bits_c, (n_leaf - 1) as u32)
                * path_sel.clone();
            for limb in 0..DIGEST_LIMBS {
                builder.assert_zero(
                    leaf_out.clone()
                        * (AB::Expr::from(curr_state[limb]) - pv[leaf_d_base + limb].clone()),
                );
            }
            // Final compress output binds to claimed Merkle root at segment
            // `n_leaf + d - 1` when `onehot[d-1]` (path_depth == d).
            for d in 1..=depth {
                let root_out = bind_out.clone()
                    * eq_bits_const::<AB>(&seg_bits_c, (n_leaf + d - 1) as u32)
                    * path_sel.clone()
                    * pv[oh_base + d - 1].clone();
                for limb in 0..DIGEST_LIMBS {
                    builder.assert_zero(
                        root_out.clone()
                            * (AB::Expr::from(curr_state[limb]) - pv[root_base + limb].clone()),
                    );
                }
            }
        }

        // Meta columns constant within a segment except at boundaries.
        for k in 0..M4A_SEG_IDX_BITS {
            let c: AB::Expr = seg_bits_c[k].into();
            let n: AB::Expr = seg_bits_n[k].into();
            builder.assert_zero(is_tr.clone() * same_meta.clone() * (n - c));
        }
        for k in 0..M4B_PATH_IDX_BITS {
            let c: AB::Expr = path_bits_c[k].into();
            let n: AB::Expr = path_bits_n[k].into();
            builder.assert_zero(is_tr.clone() * same_meta.clone() * (n - c));
        }

        // Path index increments only when a new path starts.
        let path_val_c = bits_value_expr::<AB>(&path_bits_c);
        let path_val_n = bits_value_expr::<AB>(&path_bits_n);
        let new_path = seg_start_n.clone() * eq_bits_const::<AB>(&seg_bits_n, 0);
        builder.assert_zero(
            is_tr.clone()
                * (one.clone() - new_path.clone())
                * (path_val_n.clone() - path_val_c.clone()),
        );
        builder.assert_zero(is_tr * new_path * (path_val_n - path_val_c.clone() - one.clone()));
    }
}

fn bits_value_expr<AB: AirBuilder>(bits: &[AB::Var]) -> AB::Expr
where
    AB::F: PrimeCharacteristicRing,
{
    let mut acc = AB::Expr::ZERO;
    let mut pow = AB::Expr::ONE;
    let two = AB::Expr::TWO;
    for bit in bits {
        acc += (*bit).into() * pow.clone();
        pow *= two.clone();
    }
    acc
}

#[allow(clippy::too_many_arguments)]
fn build_public_values(
    leaf_width: usize,
    depth: usize,
    path_count: usize,
    rows: &[Vec<Mersenne31>],
    leaf_digests: &[[u8; 32]],
    roots: &[[u8; 32]],
    indices: &[u32],
    siblings: &[Vec<[u8; 32]>],
) -> Result<Vec<Mersenne31>, String> {
    let shared = roots_are_shared(roots);
    let mut pv = Vec::with_capacity(p2_num_public(leaf_width, depth, path_count, shared));
    pv.push(Mersenne31::from_u32(path_count as u32));
    pv.push(Mersenne31::from_u32(depth as u32));
    if shared {
        pv.extend_from_slice(&digest_bytes_to_limbs(roots[0]));
    }
    for p in 0..path_count {
        if rows[p].len() != leaf_width {
            return Err("inhomogeneous leaf_width".into());
        }
        let actual_depth = siblings[p].len();
        if actual_depth == 0 || actual_depth > depth {
            return Err("siblings length mismatch".into());
        }
        pv.extend_from_slice(&rows[p]);
        pv.extend_from_slice(&digest_bytes_to_limbs(leaf_digests[p]));
        if !shared {
            pv.extend_from_slice(&digest_bytes_to_limbs(roots[p]));
        }
        for i in 0..depth {
            pv.push(bool_m31(actual_depth == i + 1));
        }
        for i in 0..depth {
            if i < actual_depth {
                pv.push(Mersenne31::from_u32((indices[p] >> i) & 1));
            } else {
                pv.push(Mersenne31::ZERO);
            }
        }
        for i in 0..depth {
            if i < actual_depth {
                pv.extend_from_slice(&digest_bytes_to_limbs(siblings[p][i]));
            } else {
                pv.extend_from_slice(&digest_bytes_to_limbs([0u8; 32]));
            }
        }
    }
    debug_assert_eq!(
        pv.len(),
        p2_num_public(leaf_width, depth, path_count, shared)
    );
    Ok(pv)
}

type FoldPathWitness = ([u8; 32], Vec<[u8; 32]>, Vec<[Mersenne31; POSEIDON2_WIDTH]>);

fn fold_path_witness(
    row: &[Mersenne31],
    siblings: &[[u8; 32]],
    index: usize,
    expected_root: &[u8; 32],
) -> Result<FoldPathWitness, String> {
    let depth = siblings.len();
    if depth == 0 || depth > FRI_MMCS_MAX_DEPTH || !poseidon_m4b_width_eligible(row.len()) {
        return Err(format!(
            "unsupported path depth {depth} or leaf width {}",
            row.len()
        ));
    }
    let leaf_digest = hash_val_leaf_poseidon(row);
    let mut digest = leaf_digest;
    let mut idx = index;
    let mut layer_digests = Vec::with_capacity(depth);
    let mut compress_inputs = Vec::with_capacity(depth);
    for sib in siblings {
        let (left, right) = if idx.is_multiple_of(2) {
            (digest, *sib)
        } else {
            (*sib, digest)
        };
        compress_inputs.push(compress_state(left, right));
        digest = compress_digests_poseidon(left, right);
        layer_digests.push(digest);
        idx /= 2;
    }
    if &digest != expected_root {
        return Err("folded root mismatch".into());
    }
    Ok((leaf_digest, layer_digests, compress_inputs))
}

pub fn generate_poseidon_group_fold_proof(
    statements: &[MmcsPathStatement],
) -> Result<PoseidonGroupFoldProof, String> {
    generate_poseidon_group_fold_proof_with_queries(statements, DEVNET_FRI_NUM_QUERIES)
}

/// Like [`generate_poseidon_group_fold_proof`], with explicit nested FRI query count
/// (typically matching the outer leaf/agg proof).
pub fn generate_poseidon_group_fold_proof_with_queries(
    statements: &[MmcsPathStatement],
    num_queries: usize,
) -> Result<PoseidonGroupFoldProof, String> {
    let path_count = statements.len();
    if path_count == 0 || path_count > M4B_MAX_PATHS {
        return Err(format!("path_count {path_count} out of range"));
    }
    if num_queries == 0 || num_queries > DEVNET_FRI_NUM_QUERIES {
        return Err(format!(
            "nested FRI query count {num_queries} out of range 1..={DEVNET_FRI_NUM_QUERIES}"
        ));
    }
    let leaf_width = statements[0].row.len();
    let depth = statements
        .iter()
        .map(|s| s.siblings.len())
        .max()
        .unwrap_or(0);
    if depth == 0 || depth > FRI_MMCS_MAX_DEPTH {
        return Err(format!("unsupported max_depth {depth}"));
    }
    if !poseidon_m4b_width_eligible(leaf_width) {
        return Err(format!(
            "leaf_width {leaf_width} not M4b-eligible for Poseidon group"
        ));
    }

    let mut rows = Vec::with_capacity(path_count);
    let mut leaf_digests = Vec::with_capacity(path_count);
    let mut compress_inputs = Vec::with_capacity(path_count);
    let mut roots = Vec::with_capacity(path_count);
    let mut indices = Vec::with_capacity(path_count);
    let mut siblings = Vec::with_capacity(path_count);

    for (p, stmt) in statements.iter().enumerate() {
        if stmt.row.len() != leaf_width {
            return Err(format!("path {p}: inhomogeneous leaf_width"));
        }
        let d = stmt.siblings.len();
        if d == 0 || d > depth {
            return Err(format!("path {p}: unsupported depth {d}"));
        }
        let (leaf_d, _layers, compress) =
            fold_path_witness(&stmt.row, &stmt.siblings, stmt.index, &stmt.root)?;
        rows.push(stmt.row.clone());
        leaf_digests.push(leaf_d);
        compress_inputs.push(compress);
        roots.push(stmt.root);
        indices.push(stmt.index as u32);
        siblings.push(stmt.siblings.clone());
    }

    let air = PoseidonMmcsGroupPathAir {
        leaf_width,
        depth,
        path_count,
        shared_root: roots_are_shared(&roots),
    };
    let matrix_paths: Vec<_> = rows
        .iter()
        .zip(compress_inputs.iter())
        .map(|(row, compress)| (row.clone(), compress.clone()))
        .collect();
    let matrix = build_group_matrix(&matrix_paths);
    drop(compress_inputs);

    let pv = build_public_values(
        leaf_width,
        depth,
        path_count,
        &rows,
        &leaf_digests,
        &roots,
        &indices,
        &siblings,
    )?;
    drop(rows);
    drop(roots);
    drop(indices);
    drop(siblings);

    p3_air::check_constraints(&air, &matrix, &pv);
    let config = if num_queries == DEVNET_FRI_NUM_QUERIES {
        devnet_circle_config()
    } else {
        devnet_circle_config_with_queries(num_queries)
    };
    let proof = prove(&config, &air, matrix, &pv);
    let group_stark = super::prove_workspace::encode_stark_and_drop(proof, "poseidon m4b group")?;

    Ok(PoseidonGroupFoldProof {
        path_count: path_count as u32,
        depth: depth as u32,
        leaf_width: leaf_width as u32,
        group_stark,
    })
}

pub fn verify_poseidon_group_fold_proof(
    statements: &[MmcsPathStatement],
    proof: &PoseidonGroupFoldProof,
) -> bool {
    let path_count = proof.path_count as usize;
    let depth = proof.depth as usize;
    let leaf_width = proof.leaf_width as usize;
    if statements.len() != path_count
        || path_count == 0
        || depth == 0
        || depth > FRI_MMCS_MAX_DEPTH
        || !poseidon_m4b_width_eligible(leaf_width)
    {
        eprintln!("[PoseidonM4b] Failed: shape");
        return false;
    }

    let mut rows = Vec::with_capacity(path_count);
    let mut leaf_digests = Vec::with_capacity(path_count);
    let mut roots = Vec::with_capacity(path_count);
    let mut indices = Vec::with_capacity(path_count);
    let mut siblings = Vec::with_capacity(path_count);

    let mut saw_max = false;
    for (p, stmt) in statements.iter().enumerate() {
        let d = stmt.siblings.len();
        if stmt.row.len() != leaf_width || d == 0 || d > depth {
            return false;
        }
        if d == depth {
            saw_max = true;
        }
        // Digests are recomputed from the statement, not carried on the wire.
        let leaf_digest = hash_val_leaf_poseidon(&stmt.row);
        let root = merkle_root_from_path_poseidon(leaf_digest, &stmt.siblings, stmt.index);
        if root != stmt.root {
            eprintln!("[PoseidonM4b] Failed: root path {p}");
            return false;
        }
        rows.push(stmt.row.clone());
        leaf_digests.push(leaf_digest);
        roots.push(stmt.root);
        indices.push(stmt.index as u32);
        siblings.push(stmt.siblings.clone());
    }
    if !saw_max {
        eprintln!("[PoseidonM4b] Failed: max_depth mismatch");
        return false;
    }

    let pv = match build_public_values(
        leaf_width,
        depth,
        path_count,
        &rows,
        &leaf_digests,
        &roots,
        &indices,
        &siblings,
    ) {
        Ok(v) => v,
        Err(e) => {
            eprintln!("[PoseidonM4b] pv: {e}");
            return false;
        }
    };

    let air = PoseidonMmcsGroupPathAir {
        leaf_width,
        depth,
        path_count,
        shared_root: roots_are_shared(&roots),
    };
    let stark: p3_uni_stark::Proof<WqcStarkConfig> = match postcard::from_bytes(&proof.group_stark)
    {
        Ok(p) => p,
        Err(e) => {
            eprintln!("[PoseidonM4b] postcard: {e}");
            return false;
        }
    };
    let config = match super::fri_fs_replay::circle_config_matching_proof(&stark) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("[PoseidonM4b] config: {e}");
            return false;
        }
    };
    verify(&config, &air, &stark, &pv).is_ok()
}

#[cfg(test)]
mod tests {
    use super::super::fri_mmcs_group_m4b::{
        generate_keccak_group_fold_proof, verify_keccak_group_fold_proof, MmcsPathStatement,
    };
    use super::super::keccak_f_native::keccak256_compress;
    use super::super::merkle_keccak::hash_val_leaf_keccak;
    use super::*;
    use crate::plonky3_stark::config_poseidon::pack_digest;
    use p3_field::PrimeCharacteristicRing;

    fn packed_sib(seed: u32) -> [u8; 32] {
        pack_digest([Mersenne31::from_u32(seed); 8])
    }

    fn stmt_poseidon_w3(index: usize, sibling: [u8; 32], seed: u32) -> MmcsPathStatement {
        let row = vec![
            Mersenne31::from_u32(seed),
            Mersenne31::from_u32(seed + 1),
            Mersenne31::from_u32(seed + 2),
        ];
        let leaf = hash_val_leaf_poseidon(&row);
        let root = if index.is_multiple_of(2) {
            compress_digests_poseidon(leaf, sibling)
        } else {
            compress_digests_poseidon(sibling, leaf)
        };
        MmcsPathStatement {
            row,
            siblings: vec![sibling],
            index,
            root,
        }
    }

    fn stmt_keccak_w3(index: usize, sibling: [u8; 32], seed: u32) -> MmcsPathStatement {
        let row = vec![
            Mersenne31::from_u32(seed),
            Mersenne31::from_u32(seed + 1),
            Mersenne31::from_u32(seed + 2),
        ];
        let leaf = hash_val_leaf_keccak(&row);
        let root = if index.is_multiple_of(2) {
            keccak256_compress(leaf, sibling)
        } else {
            keccak256_compress(sibling, leaf)
        };
        MmcsPathStatement {
            row,
            siblings: vec![sibling],
            index,
            root,
        }
    }

    #[test]
    fn poseidon_m4b_two_paths_depth1_roundtrip() {
        let stmts = vec![
            stmt_poseidon_w3(0, packed_sib(9), 1),
            stmt_poseidon_w3(1, packed_sib(3), 10),
        ];
        let proof = generate_poseidon_group_fold_proof(&stmts).expect("prove");
        assert!(verify_poseidon_group_fold_proof(&stmts, &proof));
    }

    #[test]
    fn poseidon_m4b_group_smaller_than_keccak_m4b() {
        let p_stmts = vec![
            stmt_poseidon_w3(0, packed_sib(9), 1),
            stmt_poseidon_w3(1, packed_sib(3), 10),
        ];
        let k_stmts = vec![
            stmt_keccak_w3(0, [9u8; 32], 1),
            stmt_keccak_w3(1, [3u8; 32], 10),
        ];
        let poseidon = generate_poseidon_group_fold_proof(&p_stmts).expect("poseidon prove");
        let keccak = generate_keccak_group_fold_proof(&k_stmts).expect("keccak prove");
        assert!(verify_poseidon_group_fold_proof(&p_stmts, &poseidon));
        assert!(verify_keccak_group_fold_proof(&k_stmts, &keccak));
        eprintln!(
            "M4b W=3 N=2 depth=1: poseidon_group={} vs keccak_group={}",
            poseidon.group_stark.len(),
            keccak.group_stark.len()
        );
        assert!(
            poseidon.group_stark.len() < keccak.group_stark.len(),
            "poseidon {} not smaller than keccak {}",
            poseidon.group_stark.len(),
            keccak.group_stark.len()
        );
    }

    fn stmt_poseidon_w48(index: usize, sibling: [u8; 32], seed: u32) -> MmcsPathStatement {
        let row: Vec<_> = (0..48)
            .map(|i| Mersenne31::from_u32(seed + i as u32 * 17 + 3))
            .collect();
        let leaf = hash_val_leaf_poseidon(&row);
        let root = if index.is_multiple_of(2) {
            compress_digests_poseidon(leaf, sibling)
        } else {
            compress_digests_poseidon(sibling, leaf)
        };
        MmcsPathStatement {
            row,
            siblings: vec![sibling],
            index,
            root,
        }
    }

    fn stmt_poseidon_w21(index: usize, sibling: [u8; 32], seed: u32) -> MmcsPathStatement {
        let row: Vec<_> = (0..21)
            .map(|i| Mersenne31::from_u32(seed + i as u32 * 5 + 7))
            .collect();
        let leaf = hash_val_leaf_poseidon(&row);
        let root = if index.is_multiple_of(2) {
            compress_digests_poseidon(leaf, sibling)
        } else {
            compress_digests_poseidon(sibling, leaf)
        };
        MmcsPathStatement {
            row,
            siblings: vec![sibling],
            index,
            root,
        }
    }

    #[test]
    fn poseidon_m4b_sponge_capacity_carry_width21() {
        use crate::plonky3_stark::config_poseidon::poseidon_sponge_leaf_perm_inputs;
        use p3_mersenne_31::default_mersenne31_poseidon2_16;
        use p3_symmetric::Permutation;

        let row: Vec<_> = (0..21)
            .map(|i| Mersenne31::from_u32(i as u32 * 5 + 7))
            .collect();
        let inputs = poseidon_sponge_leaf_perm_inputs(&row);
        let perm = default_mersenne31_poseidon2_16();
        for (k, inp) in inputs.iter().enumerate() {
            let mut native = *inp;
            perm.permute_mut(&mut native);
            let trace = build_perm_trace(*inp);
            let last = &trace.values[(trace.height() - 1) * trace.width..][..POSEIDON2_WIDTH];
            assert_eq!(last, native.as_slice(), "perm {k} output mismatch");
            if k + 1 < inputs.len() {
                for i in POSEIDON_RATE..POSEIDON2_WIDTH {
                    assert_eq!(
                        inputs[k + 1][i],
                        native[i],
                        "capacity carry {k}->{} slot {i}",
                        k + 1
                    );
                }
            }
        }
    }

    #[test]
    fn poseidon_m4b_two_paths_width21_depth1_roundtrip() {
        let stmts = vec![
            stmt_poseidon_w21(0, packed_sib(9), 100),
            stmt_poseidon_w21(1, packed_sib(3), 200),
        ];
        let proof = generate_poseidon_group_fold_proof(&stmts).expect("prove w21");
        assert_eq!(proof.leaf_width, 21);
        assert!(verify_poseidon_group_fold_proof(&stmts, &proof));
    }

    #[test]
    fn poseidon_m4b_two_paths_width48_depth1_roundtrip() {
        let stmts = vec![
            stmt_poseidon_w48(0, packed_sib(9), 100),
            stmt_poseidon_w48(1, packed_sib(3), 200),
        ];
        let proof = generate_poseidon_group_fold_proof(&stmts).expect("prove w48");
        assert_eq!(proof.leaf_width, 48);
        assert!(verify_poseidon_group_fold_proof(&stmts, &proof));
    }

    /// Two-layer Merkle path (depth=2) exercises compress chaining without layer PVs.
    fn stmt_poseidon_w3_depth2(
        index: usize,
        sib0: [u8; 32],
        sib1: [u8; 32],
        seed: u32,
    ) -> MmcsPathStatement {
        let row = vec![
            Mersenne31::from_u32(seed),
            Mersenne31::from_u32(seed + 1),
            Mersenne31::from_u32(seed + 2),
        ];
        let leaf = hash_val_leaf_poseidon(&row);
        let mut digest = leaf;
        let mut idx = index;
        for sib in [sib0, sib1] {
            let (left, right) = if idx.is_multiple_of(2) {
                (digest, sib)
            } else {
                (sib, digest)
            };
            digest = compress_digests_poseidon(left, right);
            idx /= 2;
        }
        MmcsPathStatement {
            row,
            siblings: vec![sib0, sib1],
            index,
            root: digest,
        }
    }

    #[test]
    fn poseidon_m4b_two_paths_depth2_roundtrip() {
        let stmts = vec![
            stmt_poseidon_w3_depth2(0, packed_sib(9), packed_sib(11), 1),
            stmt_poseidon_w3_depth2(3, packed_sib(3), packed_sib(7), 10),
        ];
        let proof = generate_poseidon_group_fold_proof(&stmts).expect("prove d2");
        assert_eq!(proof.depth, 2);
        assert_eq!(
            p2_num_public(3, 2, 2, false),
            2 + 2 * (3 + 8 + 8 + 2 + 2 + 2 * 8)
        );
        assert!(verify_poseidon_group_fold_proof(&stmts, &proof));
    }

    /// Two paths under one commitment exercise the shared-root header.
    #[test]
    fn poseidon_m4b_shared_root_roundtrip() {
        let sib = packed_sib(9);
        let left = stmt_poseidon_w3(0, sib, 1);
        let right = MmcsPathStatement {
            row: left.row.clone(),
            siblings: vec![sib],
            index: 0,
            root: left.root,
        };
        let stmts = vec![left, right];
        let proof = generate_poseidon_group_fold_proof(&stmts).expect("prove shared root");
        assert!(verify_poseidon_group_fold_proof(&stmts, &proof));
    }

    #[test]
    fn poseidon_m4b_pv_stride_is_depth_packed() {
        // Packed d=8 W=3: leaf + digest + root + onehot + idx + sibs.
        assert_eq!(p2_path_stride(3, 8, false), 3 + 8 + 8 + 8 + 8 + 64);
        assert_eq!(p2_num_public(3, 8, 40, false), 2 + 40 * 99);
        // Shared root hoists 8 limbs into the header.
        assert_eq!(p2_path_stride(3, 8, true), 3 + 8 + 8 + 8 + 64);
        assert_eq!(p2_num_public(3, 8, 40, true), 10 + 40 * 91);
    }

    #[test]
    fn poseidon_m4b_mixed_depth_1_and_2_roundtrip() {
        let stmts = vec![
            stmt_poseidon_w3(0, packed_sib(9), 1),
            stmt_poseidon_w3_depth2(3, packed_sib(3), packed_sib(7), 10),
        ];
        let proof = generate_poseidon_group_fold_proof(&stmts).expect("prove mixed");
        assert_eq!(proof.depth, 2);
        assert_eq!(proof.path_count, 2);
        assert!(verify_poseidon_group_fold_proof(&stmts, &proof));
        assert!(!verify_poseidon_group_fold_proof(&stmts[..1], &proof));
    }
}

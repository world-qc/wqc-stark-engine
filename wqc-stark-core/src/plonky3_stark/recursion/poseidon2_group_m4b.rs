//! E5b prototype: Poseidon2 Mmcs group fold parallel to [`super::fri_mmcs_group_m4b`].
//!
//! Replaces Keccak sponge segments (width ~1657) with width-16 Poseidon2 perm traces (width 21).
//! Wire format is **not** production-ready; size/constraint prototype only.

#![allow(clippy::needless_range_loop)]

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_mersenne_31::Mersenne31;
use p3_uni_stark::{prove, verify};

use crate::air::pad_air_matrix_for_uni_stark;
use crate::plonky3_stark::config::{devnet_circle_config, WqcStarkConfig};

use super::fri_mmcs_group_m4b::{MmcsPathStatement, M4B_MAX_PATHS, M4B_PATH_IDX_BITS};
use super::fri_mmcs_path::FRI_MMCS_MAX_DEPTH;
use super::fri_mmcs_path_m4a::M4A_SEG_IDX_BITS;
use super::merkle_poseidon2::{
    compress_digests_poseidon, hash_val_leaf_poseidon, merkle_root_from_path_poseidon,
};
use super::poseidon2_spike::POSEIDON2_WIDTH;
use super::poseidon2_perm_air::{
    build_perm_trace, constrain_external, constrain_internal, constrain_mds_only,
    selector_for_step, POSEIDON2_LIVE_COL, POSEIDON2_PERM_ROWS, POSEIDON2_PERM_STEPS,
    POSEIDON2_PERM_WIDTH, POSEIDON2_STEP_BITS, POSEIDON2_STEP_COL,
};

pub const POSEIDON2_SEG_ROWS: usize = POSEIDON2_PERM_ROWS;

pub const P2_SEG_START_COL: usize = POSEIDON2_PERM_WIDTH;
pub const P2_SEG_IDX_COL: usize = POSEIDON2_PERM_WIDTH + 1;
pub const P2_PATH_IDX_COL: usize = P2_SEG_IDX_COL + M4A_SEG_IDX_BITS;

pub const POSEIDON2_GROUP_WIDTH: usize =
    POSEIDON2_PERM_WIDTH + 1 + M4A_SEG_IDX_BITS + M4B_PATH_IDX_BITS;

const DIGEST_LIMBS: usize = 8;

/// Homogeneous group proof using Poseidon2 perm segments (prototype).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PoseidonGroupFoldProof {
    pub path_count: u32,
    pub depth: u32,
    pub leaf_width: u32,
    pub leaf_digests: Vec<[u8; 32]>,
    pub layer_digests: Vec<Vec<[u8; 32]>>,
    pub group_stark: Vec<u8>,
}

#[derive(Copy, Clone, Debug)]
pub struct PoseidonMmcsGroupPathAir {
    pub leaf_width: usize,
    pub depth: usize,
    pub path_count: usize,
}

fn p2_path_stride(leaf_width: usize) -> usize {
    leaf_width + DIGEST_LIMBS * 2 + 1 + FRI_MMCS_MAX_DEPTH + FRI_MMCS_MAX_DEPTH * DIGEST_LIMBS * 2
}

fn p2_num_public(leaf_width: usize, path_count: usize) -> usize {
    2 + path_count * p2_path_stride(leaf_width)
}

fn pv_path_base(path: usize, leaf_width: usize) -> usize {
    2 + path * p2_path_stride(leaf_width)
}
fn pv_leaf_digest_off(path: usize, leaf_width: usize) -> usize {
    pv_path_base(path, leaf_width) + leaf_width
}
fn pv_root_off(path: usize, leaf_width: usize) -> usize {
    pv_leaf_digest_off(path, leaf_width) + DIGEST_LIMBS
}
fn pv_index_off(path: usize, leaf_width: usize) -> usize {
    pv_root_off(path, leaf_width) + DIGEST_LIMBS
}
fn pv_index_bits_off(path: usize, leaf_width: usize) -> usize {
    pv_index_off(path, leaf_width) + 1
}
fn pv_siblings_off(path: usize, leaf_width: usize) -> usize {
    pv_index_bits_off(path, leaf_width) + FRI_MMCS_MAX_DEPTH
}
fn pv_layers_off(path: usize, leaf_width: usize) -> usize {
    pv_siblings_off(path, leaf_width) + FRI_MMCS_MAX_DEPTH * DIGEST_LIMBS
}

impl<F: Field> BaseAir<F> for PoseidonMmcsGroupPathAir {
    fn width(&self) -> usize {
        POSEIDON2_GROUP_WIDTH
    }

    fn max_constraint_degree(&self) -> Option<usize> {
        None
    }

    fn num_public_values(&self) -> usize {
        p2_num_public(self.leaf_width, self.path_count)
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

fn leaf_state_from_row(row: &[Mersenne31]) -> [Mersenne31; POSEIDON2_WIDTH] {
    let mut state = [Mersenne31::ZERO; POSEIDON2_WIDTH];
    for (i, v) in row.iter().enumerate().take(POSEIDON2_WIDTH) {
        state[i] = *v;
    }
    state
}

fn compress_state(left: [u8; 32], right: [u8; 32]) -> [Mersenne31; POSEIDON2_WIDTH] {
    let mut state = [Mersenne31::ZERO; POSEIDON2_WIDTH];
    for (i, chunk) in left[..16]
        .chunks(4)
        .chain(right[..16].chunks(4))
        .enumerate()
        .take(DIGEST_LIMBS)
    {
        let mut b = [0u8; 4];
        b.copy_from_slice(chunk);
        state[i] = Mersenne31::new(u32::from_le_bytes(b));
    }
    state
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
        append_perm_segment(&mut values, leaf_state_from_row(row), 0, p);
        for (i, input) in compress_inputs.iter().enumerate() {
            append_perm_segment(&mut values, *input, i + 1, p);
        }
    }
    let active_rows = values.len() / POSEIDON2_GROUP_WIDTH;
    let mut matrix = pad_air_matrix_for_uni_stark(RowMajorMatrix::new(values, POSEIDON2_GROUP_WIDTH));
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

        for p in 0..path_count {
            let path_sel = eq_bits_const::<AB>(&path_bits_c, p as u32);
            let row_base = pv_path_base(p, leaf_width);
            let leaf_d_base = pv_leaf_digest_off(p, leaf_width);
            let root_base = pv_root_off(p, leaf_width);
            let idx_bits_base = pv_index_bits_off(p, leaf_width);
            let sib_base = pv_siblings_off(p, leaf_width);
            let layer_base = pv_layers_off(p, leaf_width);

            // Leaf segment start: bind absorb state.
            let leaf_start =
                seg_start_c.clone() * eq_bits_const::<AB>(&seg_bits_c, 0) * path_sel.clone();
            for i in 0..leaf_width {
                builder.assert_zero(
                    leaf_start.clone() * (AB::Expr::from(curr_state[i]) - pv[row_base + i].clone()),
                );
            }
            for i in leaf_width..POSEIDON2_WIDTH {
                builder.assert_zero(leaf_start.clone() * AB::Expr::from(curr_state[i]));
            }

            // Compress segment starts: left/right digest limbs from PV.
            for layer in 0..depth {
                let start = seg_start_c.clone()
                    * eq_bits_const::<AB>(&seg_bits_c, (layer + 1) as u32)
                    * path_sel.clone();
                let bit = pv[idx_bits_base + layer].clone();
                let not_bit = one.clone() - bit.clone();
                for limb in 0..DIGEST_LIMBS {
                    let idx = if limb < 4 { limb } else { limb - 4 };
                    let prev = if layer == 0 {
                        pv[leaf_d_base + idx].clone()
                    } else {
                        pv[layer_base + (layer - 1) * DIGEST_LIMBS + idx].clone()
                    };
                    let sib = pv[sib_base + layer * DIGEST_LIMBS + idx].clone();
                    let left = not_bit.clone() * prev.clone() + bit.clone() * sib.clone();
                    let right = bit.clone() * prev + not_bit.clone() * sib;
                    let want = if limb < 4 { left } else { right };
                    builder.assert_zero(
                        start.clone() * (AB::Expr::from(curr_state[limb]) - want),
                    );
                }
                for i in DIGEST_LIMBS..POSEIDON2_WIDTH {
                    builder.assert_zero(start.clone() * AB::Expr::from(curr_state[i]));
                }
            }

            // Segment outputs bind when the next row starts a new segment or padding begins.
            let end_seg = is_tr.clone() * seg_start_n.clone() * live_n.clone();
            let bind_out = end_seg + end_active.clone();
            let leaf_out =
                bind_out.clone() * eq_bits_const::<AB>(&seg_bits_c, 0) * path_sel.clone();
            for limb in 0..DIGEST_LIMBS {
                builder.assert_zero(
                    leaf_out.clone()
                        * (AB::Expr::from(curr_state[limb]) - pv[leaf_d_base + limb].clone()),
                );
            }
            for layer in 0..depth {
                let layer_out = bind_out.clone()
                    * eq_bits_const::<AB>(&seg_bits_c, (layer + 1) as u32)
                    * path_sel.clone();
                for limb in 0..DIGEST_LIMBS {
                    builder.assert_zero(
                        layer_out.clone()
                            * (AB::Expr::from(curr_state[limb])
                                - pv[layer_base + layer * DIGEST_LIMBS + limb].clone()),
                    );
                }
            }

            let last = depth - 1;
            for limb in 0..DIGEST_LIMBS {
                builder.assert_zero(
                    pv[layer_base + last * DIGEST_LIMBS + limb].clone()
                        - pv[root_base + limb].clone(),
                );
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
            is_tr.clone() * (one.clone() - new_path.clone()) * (path_val_n.clone() - path_val_c.clone()),
        );
        builder.assert_zero(
            is_tr * new_path * (path_val_n - path_val_c.clone() - one.clone()),
        );
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

fn build_public_values(
    leaf_width: usize,
    depth: usize,
    path_count: usize,
    rows: &[Vec<Mersenne31>],
    leaf_digests: &[[u8; 32]],
    roots: &[[u8; 32]],
    indices: &[u32],
    siblings: &[Vec<[u8; 32]>],
    layer_digests: &[Vec<[u8; 32]>],
) -> Result<Vec<Mersenne31>, String> {
    let mut pv = Vec::with_capacity(p2_num_public(leaf_width, path_count));
    pv.push(Mersenne31::from_u32(path_count as u32));
    pv.push(Mersenne31::from_u32(depth as u32));
    for p in 0..path_count {
        if rows[p].len() != leaf_width {
            return Err("inhomogeneous leaf_width".into());
        }
        pv.extend_from_slice(&rows[p]);
        pv.extend_from_slice(&digest_bytes_to_limbs(leaf_digests[p]));
        pv.extend_from_slice(&digest_bytes_to_limbs(roots[p]));
        pv.push(Mersenne31::from_u32(indices[p]));
        for i in 0..FRI_MMCS_MAX_DEPTH {
            let bit = if i < depth { (indices[p] >> i) & 1 } else { 0 };
            pv.push(Mersenne31::from_u32(bit));
        }
        for i in 0..FRI_MMCS_MAX_DEPTH {
            let s = if i < depth {
                digest_bytes_to_limbs(siblings[p][i])
            } else {
                [Mersenne31::ZERO; DIGEST_LIMBS]
            };
            pv.extend_from_slice(&s);
        }
        for i in 0..FRI_MMCS_MAX_DEPTH {
            let d = if i < depth {
                digest_bytes_to_limbs(layer_digests[p][i])
            } else {
                [Mersenne31::ZERO; DIGEST_LIMBS]
            };
            pv.extend_from_slice(&d);
        }
    }
    Ok(pv)
}

fn fold_path_witness(
    row: &[Mersenne31],
    siblings: &[[u8; 32]],
    index: usize,
    expected_root: &[u8; 32],
) -> Result<([u8; 32], Vec<[u8; 32]>, Vec<[Mersenne31; POSEIDON2_WIDTH]>), String> {
    let depth = siblings.len();
    if depth == 0 || depth > FRI_MMCS_MAX_DEPTH || row.len() > POSEIDON2_WIDTH {
        return Err(format!("unsupported path depth {depth} or leaf width {}", row.len()));
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
    let path_count = statements.len();
    if path_count == 0 || path_count > M4B_MAX_PATHS {
        return Err(format!("path_count {path_count} out of range"));
    }
    let depth = statements[0].siblings.len();
    let leaf_width = statements[0].row.len();
    if depth == 0 || depth > FRI_MMCS_MAX_DEPTH {
        return Err(format!("unsupported depth {depth}"));
    }
    if leaf_width > POSEIDON2_WIDTH {
        return Err(format!("leaf_width {leaf_width} > {POSEIDON2_WIDTH} in prototype"));
    }

    let mut rows = Vec::with_capacity(path_count);
    let mut leaf_digests = Vec::with_capacity(path_count);
    let mut layer_digests = Vec::with_capacity(path_count);
    let mut compress_inputs = Vec::with_capacity(path_count);
    let mut roots = Vec::with_capacity(path_count);
    let mut indices = Vec::with_capacity(path_count);
    let mut siblings = Vec::with_capacity(path_count);

    for (p, stmt) in statements.iter().enumerate() {
        if stmt.siblings.len() != depth || stmt.row.len() != leaf_width {
            return Err(format!("path {p}: inhomogeneous shape"));
        }
        let (leaf_d, layers, compress) =
            fold_path_witness(&stmt.row, &stmt.siblings, stmt.index, &stmt.root)?;
        rows.push(stmt.row.clone());
        leaf_digests.push(leaf_d);
        layer_digests.push(layers);
        compress_inputs.push(compress);
        roots.push(stmt.root);
        indices.push(stmt.index as u32);
        siblings.push(stmt.siblings.clone());
    }

    let air = PoseidonMmcsGroupPathAir {
        leaf_width,
        depth,
        path_count,
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
        &layer_digests,
    )?;
    drop(rows);
    drop(roots);
    drop(indices);
    drop(siblings);

    p3_air::check_constraints(&air, &matrix, &pv);
    let config = devnet_circle_config();
    let proof = prove(&config, &air, matrix, &pv);
    let group_stark = super::prove_workspace::encode_stark_and_drop(proof, "poseidon m4b group")?;

    Ok(PoseidonGroupFoldProof {
        path_count: path_count as u32,
        depth: depth as u32,
        leaf_width: leaf_width as u32,
        leaf_digests,
        layer_digests,
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
        || proof.leaf_digests.len() != path_count
        || proof.layer_digests.len() != path_count
        || path_count == 0
        || depth == 0
        || depth > FRI_MMCS_MAX_DEPTH
        || leaf_width > POSEIDON2_WIDTH
    {
        eprintln!("[PoseidonM4b] Failed: shape");
        return false;
    }

    let mut rows = Vec::with_capacity(path_count);
    let mut roots = Vec::with_capacity(path_count);
    let mut indices = Vec::with_capacity(path_count);
    let mut siblings = Vec::with_capacity(path_count);

    for (p, stmt) in statements.iter().enumerate() {
        if stmt.row.len() != leaf_width || stmt.siblings.len() != depth {
            return false;
        }
        if proof.leaf_digests[p] != hash_val_leaf_poseidon(&stmt.row) {
            eprintln!("[PoseidonM4b] Failed: leaf digest path {p}");
            return false;
        }
        if proof.layer_digests[p].len() != depth {
            return false;
        }
        let root = merkle_root_from_path_poseidon(proof.leaf_digests[p], &stmt.siblings, stmt.index);
        if root != stmt.root {
            eprintln!("[PoseidonM4b] Failed: root path {p}");
            return false;
        }
        rows.push(stmt.row.clone());
        roots.push(stmt.root);
        indices.push(stmt.index as u32);
        siblings.push(stmt.siblings.clone());
    }

    let pv = match build_public_values(
        leaf_width,
        depth,
        path_count,
        &rows,
        &proof.leaf_digests,
        &roots,
        &indices,
        &siblings,
        &proof.layer_digests,
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
    };
    let stark: p3_uni_stark::Proof<WqcStarkConfig> = match postcard::from_bytes(&proof.group_stark)
    {
        Ok(p) => p,
        Err(e) => {
            eprintln!("[PoseidonM4b] postcard: {e}");
            return false;
        }
    };
    verify(&devnet_circle_config(), &air, &stark, &pv).is_ok()
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::fri_mmcs_group_m4b::{
        generate_keccak_group_fold_proof, verify_keccak_group_fold_proof, MmcsPathStatement,
    };
    use super::super::merkle_keccak::hash_val_leaf;
    use super::super::keccak_f_native::keccak256_compress;
    use p3_field::PrimeCharacteristicRing;

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
        let leaf = hash_val_leaf(&row);
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
            stmt_poseidon_w3(0, [9u8; 32], 1),
            stmt_poseidon_w3(1, [3u8; 32], 10),
        ];
        let proof = generate_poseidon_group_fold_proof(&stmts).expect("prove");
        assert!(verify_poseidon_group_fold_proof(&stmts, &proof));
    }

    #[test]
    fn poseidon_m4b_group_smaller_than_keccak_m4b() {
        let p_stmts = vec![
            stmt_poseidon_w3(0, [9u8; 32], 1),
            stmt_poseidon_w3(1, [3u8; 32], 10),
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
}

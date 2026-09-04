//! R3-M4a: one Merkle path → one multi-segment Keccak path AIR + one outer STARK.
//!
//! Replaces per-step nested `Keccak256StarkProof`s with a single `path_stark`.
//! Leaf messages may use **1 or 2** Keccak permutations (`msg_len ≤ 2·KECCAK_RATE`,
//! height 32 or 64). Compress segments stay single-perm / [`M4A_SEG_ROWS`] rows.

#![allow(clippy::needless_range_loop)]

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_mersenne_31::Mersenne31;
use p3_uni_stark::{prove, verify};

use crate::air::pad_air_matrix_for_uni_stark;
use crate::plonky3_stark::config::{keccak_circle_config, WqcStarkConfig};

use super::fri_mmcs_path::FRI_MMCS_MAX_DEPTH;
use super::keccak256_air::{
    build_sponge_matrix, COMPRESS_MSG_LEN, ROUND_BITS, ROUND_BIT_COL, SPONGE_WIDTH,
};
use super::keccak_f_air::{constrain_keccak_round_with_rc, LIVE_COL};
use super::keccak_f_native::{
    keccak256_compress, keccak256_val_leaf, num_permutations, val_row_to_bytes, KECCAK256_OUT,
    KECCAK_DELIM, KECCAK_RATE, KECCAK_ROUNDS, KECCAK_STATE_BITS, RC,
};
use super::merkle_keccak::hash_val_leaf_keccak;

/// Rows per single-permutation sponge (`build_sponge_matrix` for msg ≤ rate).
/// Compress segments always use this height; 2-perm leaves use 64.
pub const M4A_SEG_ROWS: usize = 32;

pub const M4A_SEG_START_COL: usize = SPONGE_WIDTH;
pub const M4A_SEG_IDX_COL: usize = SPONGE_WIDTH + 1;
pub const M4A_SEG_IDX_BITS: usize = 5;
pub const M4A_PATH_WIDTH: usize = SPONGE_WIDTH + 1 + M4A_SEG_IDX_BITS;

/// Public layout:
/// `leaf_msg[L] | leaf_digest[32] | root[32] | index | depth
///  | index_bits[MAX] | siblings[MAX*32] | layer_digests[MAX*32]`
pub fn m4a_num_public(leaf_msg_len: usize) -> usize {
    leaf_msg_len
        + 32
        + 32
        + 1
        + 1
        + FRI_MMCS_MAX_DEPTH
        + FRI_MMCS_MAX_DEPTH * 32
        + FRI_MMCS_MAX_DEPTH * 32
}

const fn pv_leaf_digest_off(leaf_msg_len: usize) -> usize {
    leaf_msg_len
}
const fn pv_root_off(leaf_msg_len: usize) -> usize {
    leaf_msg_len + 32
}
const fn pv_index_off(leaf_msg_len: usize) -> usize {
    leaf_msg_len + 64
}
const fn pv_depth_off(leaf_msg_len: usize) -> usize {
    leaf_msg_len + 65
}
const fn pv_index_bits_off(leaf_msg_len: usize) -> usize {
    leaf_msg_len + 66
}
const fn pv_siblings_off(leaf_msg_len: usize) -> usize {
    leaf_msg_len + 66 + FRI_MMCS_MAX_DEPTH
}
const fn pv_layers_off(leaf_msg_len: usize) -> usize {
    leaf_msg_len + 66 + FRI_MMCS_MAX_DEPTH + FRI_MMCS_MAX_DEPTH * 32
}

#[derive(Copy, Clone, Debug)]
pub struct MmcsBatchedPathAir {
    pub leaf_msg_len: usize,
    pub depth: usize,
}

impl<F: Field> BaseAir<F> for MmcsBatchedPathAir {
    fn width(&self) -> usize {
        M4A_PATH_WIDTH
    }

    fn max_constraint_degree(&self) -> Option<usize> {
        None
    }

    fn num_public_values(&self) -> usize {
        m4a_num_public(self.leaf_msg_len)
    }
}

fn bool_m31(b: bool) -> Mersenne31 {
    if b {
        Mersenne31::ONE
    } else {
        Mersenne31::ZERO
    }
}

fn round_value_expr<AB: AirBuilder>(round_bits: &[AB::Var]) -> AB::Expr
where
    AB::F: PrimeCharacteristicRing,
{
    let mut acc = AB::Expr::ZERO;
    let mut pow = AB::Expr::ONE;
    let two = AB::Expr::TWO;
    for bit in round_bits {
        acc += (*bit).into() * pow.clone();
        pow *= two.clone();
    }
    acc
}

fn eq_round_const<AB: AirBuilder>(round_bits: &[AB::Var], target: u32) -> AB::Expr
where
    AB::F: PrimeCharacteristicRing,
{
    let mut sel = AB::Expr::ONE;
    for (k, bit) in round_bits.iter().enumerate() {
        let b: AB::Expr = (*bit).into();
        if ((target >> k) & 1) == 1 {
            sel *= b;
        } else {
            sel *= AB::Expr::ONE - b;
        }
    }
    sel
}

fn eq_seg_const<AB: AirBuilder>(seg_bits: &[AB::Var], target: u32) -> AB::Expr
where
    AB::F: PrimeCharacteristicRing,
{
    eq_round_const::<AB>(seg_bits, target)
}

fn rc_bits_from_round<AB: AirBuilder>(round_bits: &[AB::Var]) -> Vec<AB::Expr>
where
    AB::F: PrimeCharacteristicRing,
{
    let mut rc_bits = vec![AB::Expr::ZERO; 64];
    for (r, &rc) in RC.iter().enumerate() {
        let sel = eq_round_const::<AB>(round_bits, r as u32);
        for b in 0..64 {
            if ((rc >> b) & 1) == 1 {
                rc_bits[b] += sel.clone();
            }
        }
    }
    rc_bits
}

fn pack_byte_from_state_bits<AB: AirBuilder>(bits: &[AB::Var], byte_index: usize) -> AB::Expr
where
    AB::F: PrimeCharacteristicRing,
{
    let mut acc = AB::Expr::ZERO;
    let mut pow = AB::Expr::ONE;
    let two = AB::Expr::TWO;
    for bit in 0..8 {
        let b: AB::Expr = bits[byte_index * 8 + bit].into();
        acc += b * pow.clone();
        pow *= two.clone();
    }
    acc
}

fn first_block_rate_byte_leaf<AB: AirBuilder>(
    pv: &[AB::Expr],
    msg_len: usize,
    byte_i: usize,
) -> AB::Expr
where
    AB::F: PrimeCharacteristicRing,
{
    if msg_len <= KECCAK_RATE {
        let is_msg = byte_i < msg_len;
        let is_delim = byte_i == msg_len;
        let is_end = byte_i == KECCAK_RATE - 1;
        if is_delim && is_end {
            AB::F::from_u32((KECCAK_DELIM as u32) ^ 0x80).into()
        } else if is_msg {
            pv[byte_i].clone()
        } else if is_delim {
            AB::F::from_u32(KECCAK_DELIM as u32).into()
        } else if is_end {
            AB::F::from_u32(0x80).into()
        } else {
            AB::Expr::ZERO
        }
    } else {
        // Multi-perm leaf: first block is a full rate of raw message bytes.
        pv[byte_i].clone()
    }
}

/// Rate-byte XOR mask absorbed between permutation 0 and 1 (2-perm leaf only).
fn second_block_rate_byte<AB: AirBuilder>(
    pv: &[AB::Expr],
    msg_len: usize,
    byte_i: usize,
) -> AB::Expr
where
    AB::F: PrimeCharacteristicRing,
{
    let rest = msg_len - KECCAK_RATE;
    let is_msg = byte_i < rest;
    let is_delim = byte_i == rest;
    let is_end = byte_i == KECCAK_RATE - 1;
    if is_delim && is_end {
        AB::F::from_u32((KECCAK_DELIM as u32) ^ 0x80).into()
    } else if is_msg {
        pv[KECCAK_RATE + byte_i].clone()
    } else if is_delim {
        AB::F::from_u32(KECCAK_DELIM as u32).into()
    } else if is_end {
        AB::F::from_u32(0x80).into()
    } else {
        AB::Expr::ZERO
    }
}

impl<AB: AirBuilder> Air<AB> for MmcsBatchedPathAir
where
    AB::F: Field + PrimeCharacteristicRing,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let curr: Vec<AB::Var> = main.current_slice().to_vec();
        let next: Vec<AB::Var> = main.next_slice().to_vec();
        let one = AB::Expr::ONE;
        let two = AB::Expr::TWO;
        let pv: Vec<AB::Expr> = builder
            .public_values()
            .iter()
            .map(|v| (*v).into())
            .collect();
        let l = self.leaf_msg_len;
        let depth = self.depth;

        for i in 0..M4A_PATH_WIDTH {
            let b: AB::Expr = curr[i].into();
            builder.assert_zero(b.clone() * (b - one.clone()));
        }

        let live_c: AB::Expr = curr[LIVE_COL].into();
        let live_n: AB::Expr = next[LIVE_COL].into();
        let seg_start_n: AB::Expr = next[M4A_SEG_START_COL].into();
        let seg_start_c: AB::Expr = curr[M4A_SEG_START_COL].into();
        let seg_bits_c = &curr[M4A_SEG_IDX_COL..M4A_SEG_IDX_COL + M4A_SEG_IDX_BITS];
        let seg_bits_n = &next[M4A_SEG_IDX_COL..M4A_SEG_IDX_COL + M4A_SEG_IDX_BITS];
        let round_c = &curr[ROUND_BIT_COL..ROUND_BIT_COL + ROUND_BITS];
        let round_n = &next[ROUND_BIT_COL..ROUND_BIT_COL + ROUND_BITS];
        let round_val_c = round_value_expr::<AB>(round_c);
        let round_val_n = round_value_expr::<AB>(round_n);

        let mut sum_eq = AB::Expr::ZERO;
        for r in 0..KECCAK_ROUNDS {
            sum_eq += eq_round_const::<AB>(round_c, r as u32);
        }
        builder.assert_zero(live_c.clone() * (sum_eq - one.clone()));
        for k in 0..ROUND_BITS {
            let b: AB::Expr = round_c[k].into();
            builder.assert_zero((one.clone() - live_c.clone()) * b);
        }

        let rc_bits = rc_bits_from_round::<AB>(round_c);
        let is_tr = builder.is_transition();
        let both_live = live_c.clone() * live_n.clone();
        let wrap = eq_round_const::<AB>(round_c, 23) * eq_round_const::<AB>(round_n, 0);
        let mut same_seg = one.clone() - seg_start_n.clone();
        for k in 0..M4A_SEG_IDX_BITS {
            let c: AB::Expr = seg_bits_c[k].into();
            let n: AB::Expr = seg_bits_n[k].into();
            same_seg *= one.clone() - (c.clone() + n.clone() - two.clone() * c * n);
        }
        let cont = both_live.clone() * (one.clone() - wrap.clone()) * same_seg.clone();

        constrain_keccak_round_with_rc(
            builder,
            &curr[..KECCAK_STATE_BITS],
            &next[..KECCAK_STATE_BITS],
            &rc_bits,
            is_tr.clone() * cont.clone(),
        );
        builder.assert_zero(
            is_tr.clone() * cont * (round_val_n.clone() - round_val_c.clone() - one.clone()),
        );

        let to_final = live_c.clone() * (one.clone() - live_n.clone()) * same_seg.clone();
        constrain_keccak_round_with_rc(
            builder,
            &curr[..KECCAK_STATE_BITS],
            &next[..KECCAK_STATE_BITS],
            &rc_bits,
            is_tr.clone() * to_final.clone(),
        );
        let twenty_three: AB::Expr = AB::F::from_u32(23).into();
        builder.assert_zero(is_tr.clone() * to_final * (round_val_c.clone() - twenty_three));

        let idle = one.clone() - live_c.clone();
        for i in 0..SPONGE_WIDTH {
            let c: AB::Expr = curr[i].into();
            let n: AB::Expr = next[i].into();
            builder.assert_zero(is_tr.clone() * idle.clone() * same_seg.clone() * (n - c));
        }
        for k in 0..M4A_SEG_IDX_BITS {
            let c: AB::Expr = seg_bits_c[k].into();
            let n: AB::Expr = seg_bits_n[k].into();
            builder.assert_zero(is_tr.clone() * same_seg.clone() * (n - c));
        }

        // Leaf absorb at seg_start ∧ seg_idx=0.
        let leaf_start = seg_start_c.clone() * eq_seg_const::<AB>(seg_bits_c, 0);
        for byte_i in 0..KECCAK_RATE {
            let packed = pack_byte_from_state_bits::<AB>(&curr[..KECCAK_STATE_BITS], byte_i);
            let want = first_block_rate_byte_leaf::<AB>(&pv, l, byte_i);
            builder.assert_zero(leaf_start.clone() * (packed - want));
        }
        for i in KECCAK_RATE * 8..KECCAK_STATE_BITS {
            let b: AB::Expr = curr[i].into();
            builder.assert_zero(leaf_start.clone() * b);
        }
        builder.assert_zero(leaf_start.clone() * (live_c.clone() - one.clone()));
        builder.assert_zero(leaf_start * round_val_c.clone());

        // Second-block absorb on wrap inside the leaf segment (2-perm leaves).
        if l > KECCAK_RATE {
            let wrap_en = is_tr.clone()
                * both_live.clone()
                * wrap.clone()
                * same_seg.clone()
                * eq_seg_const::<AB>(seg_bits_c, 0);
            let expected = super::keccak_f_air::keccak_round_bits_expr_with_rc::<AB>(
                &curr[..KECCAK_STATE_BITS],
                &rc_bits,
            );
            for byte_i in 0..KECCAK_RATE {
                let mut xor_pack = AB::Expr::ZERO;
                let mut pow = AB::Expr::ONE;
                for bit in 0..8 {
                    let idx = byte_i * 8 + bit;
                    let nb: AB::Expr = next[idx].into();
                    let eb = expected[idx].clone();
                    let x = nb.clone() + eb.clone() - two.clone() * nb * eb;
                    xor_pack += x * pow.clone();
                    pow *= two.clone();
                }
                let want = second_block_rate_byte::<AB>(&pv, l, byte_i);
                builder.assert_zero(wrap_en.clone() * (xor_pack - want));
            }
            for i in KECCAK_RATE * 8..KECCAK_STATE_BITS {
                let nb: AB::Expr = next[i].into();
                builder.assert_zero(wrap_en.clone() * (nb - expected[i].clone()));
            }
            builder.assert_zero(wrap_en * round_val_n.clone());
        }

        let idx_bits_base = pv_index_bits_off(l);
        let leaf_d_base = pv_leaf_digest_off(l);
        let sib_base = pv_siblings_off(l);
        let layer_base = pv_layers_off(l);

        for layer in 0..depth {
            let start = seg_start_c.clone() * eq_seg_const::<AB>(seg_bits_c, (layer + 1) as u32);
            let bit = pv[idx_bits_base + layer].clone();
            let not_bit = one.clone() - bit.clone();
            for byte_i in 0..32 {
                let prev = if layer == 0 {
                    pv[leaf_d_base + byte_i].clone()
                } else {
                    pv[layer_base + (layer - 1) * 32 + byte_i].clone()
                };
                let sib = pv[sib_base + layer * 32 + byte_i].clone();
                let left = not_bit.clone() * prev.clone() + bit.clone() * sib.clone();
                let right = bit.clone() * prev + not_bit.clone() * sib;
                let packed_l = pack_byte_from_state_bits::<AB>(&curr[..KECCAK_STATE_BITS], byte_i);
                let packed_r =
                    pack_byte_from_state_bits::<AB>(&curr[..KECCAK_STATE_BITS], 32 + byte_i);
                builder.assert_zero(start.clone() * (packed_l - left));
                builder.assert_zero(start.clone() * (packed_r - right));
            }
            for byte_i in COMPRESS_MSG_LEN..KECCAK_RATE {
                let packed = pack_byte_from_state_bits::<AB>(&curr[..KECCAK_STATE_BITS], byte_i);
                let want: AB::Expr = if byte_i == COMPRESS_MSG_LEN {
                    AB::F::from_u32(KECCAK_DELIM as u32).into()
                } else if byte_i == KECCAK_RATE - 1 {
                    AB::F::from_u32(0x80).into()
                } else {
                    AB::Expr::ZERO
                };
                builder.assert_zero(start.clone() * (packed - want));
            }
            for i in KECCAK_RATE * 8..KECCAK_STATE_BITS {
                let b: AB::Expr = curr[i].into();
                builder.assert_zero(start.clone() * b);
            }
            builder.assert_zero(start.clone() * (live_c.clone() - one.clone()));
            builder.assert_zero(start * round_val_c.clone());
        }

        // Digest binding on idle rows of each segment.
        let leaf_idle = idle.clone() * eq_seg_const::<AB>(seg_bits_c, 0);
        for byte_i in 0..KECCAK256_OUT {
            let packed = pack_byte_from_state_bits::<AB>(&curr[..KECCAK_STATE_BITS], byte_i);
            builder.assert_zero(leaf_idle.clone() * (packed - pv[leaf_d_base + byte_i].clone()));
        }
        for layer in 0..depth {
            let layer_idle = idle.clone() * eq_seg_const::<AB>(seg_bits_c, (layer + 1) as u32);
            for byte_i in 0..KECCAK256_OUT {
                let packed = pack_byte_from_state_bits::<AB>(&curr[..KECCAK_STATE_BITS], byte_i);
                builder.assert_zero(
                    layer_idle.clone() * (packed - pv[layer_base + layer * 32 + byte_i].clone()),
                );
            }
        }

        // Last layer digest == root.
        let last = depth - 1;
        let root_base = pv_root_off(l);
        for byte_i in 0..32 {
            builder.assert_zero(
                pv[layer_base + last * 32 + byte_i].clone() - pv[root_base + byte_i].clone(),
            );
        }

        // depth public == AIR depth; index bits reconstruct index.
        builder.assert_zero(
            pv[pv_depth_off(l)].clone() - AB::Expr::from(AB::F::from_u32(depth as u32)),
        );
        let mut acc = AB::Expr::ZERO;
        let mut pow = one.clone();
        for i in 0..FRI_MMCS_MAX_DEPTH {
            let bit = pv[idx_bits_base + i].clone();
            if i < depth {
                acc += bit * pow.clone();
            } else {
                builder.assert_zero(bit);
            }
            pow *= two.clone();
        }
        builder.assert_zero(acc - pv[pv_index_off(l)].clone());

        builder
            .when_first_row()
            .assert_zero(AB::Expr::from(curr[M4A_SEG_START_COL]) - one.clone());
        for k in 0..M4A_SEG_IDX_BITS {
            builder
                .when_first_row()
                .assert_zero(AB::Expr::from(curr[M4A_SEG_IDX_COL + k]));
        }
    }
}

/// One Merkle path as a single outer Plonky3 STARK (no per-step Keccak proofs).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FriMmcsBatchedPathProof {
    pub depth: u32,
    pub leaf_width: u32,
    pub leaf_digest: [u8; 32],
    pub layer_digests: Vec<[u8; 32]>,
    pub path_stark: Vec<u8>,
}

fn push_seg_meta(values: &mut Vec<Mersenne31>, seg_start: bool, seg_idx: usize) {
    values.push(bool_m31(seg_start));
    for k in 0..M4A_SEG_IDX_BITS {
        values.push(bool_m31(((seg_idx >> k) & 1) == 1));
    }
}

fn append_sponge_segment(
    values: &mut Vec<Mersenne31>,
    msg: &[u8],
    seg_idx: usize,
) -> Result<(), String> {
    let n_perm = num_permutations(msg.len());
    if seg_idx == 0 {
        if n_perm == 0 || n_perm > 2 {
            return Err(format!(
                "M4a leaf requires 1..=2 perms (msg_len {}); got {n_perm}",
                msg.len()
            ));
        }
    } else if n_perm != 1 {
        return Err(format!(
            "M4a compress requires single-perm sponge (msg_len {}); got {n_perm}",
            msg.len()
        ));
    }
    let sponge = build_sponge_matrix(msg);
    let height = sponge.height();
    if seg_idx > 0 && height != M4A_SEG_ROWS {
        return Err(format!(
            "expected {M4A_SEG_ROWS}-row compress sponge, got {height}"
        ));
    }
    for r in 0..height {
        let start = r * SPONGE_WIDTH;
        values.extend_from_slice(&sponge.values[start..start + SPONGE_WIDTH]);
        push_seg_meta(values, r == 0, seg_idx);
    }
    Ok(())
}

fn build_path_matrix(
    leaf_msg: &[u8],
    compress_msgs: &[[u8; COMPRESS_MSG_LEN]],
) -> Result<RowMajorMatrix<Mersenne31>, String> {
    let mut values = Vec::new();
    append_sponge_segment(&mut values, leaf_msg, 0)?;
    for (i, msg) in compress_msgs.iter().enumerate() {
        append_sponge_segment(&mut values, msg, i + 1)?;
    }
    Ok(pad_air_matrix_for_uni_stark(RowMajorMatrix::new(
        values,
        M4A_PATH_WIDTH,
    )))
}

fn build_public_values(
    leaf_msg: &[u8],
    leaf_digest: [u8; 32],
    root: [u8; 32],
    index: u32,
    depth: usize,
    siblings: &[[u8; 32]],
    layer_digests: &[[u8; 32]],
) -> Result<Vec<Mersenne31>, String> {
    if depth == 0 || depth > FRI_MMCS_MAX_DEPTH {
        return Err(format!("depth {depth} out of range"));
    }
    if siblings.len() != depth || layer_digests.len() != depth {
        return Err("siblings/layer_digests length mismatch".into());
    }
    let mut pv = Vec::with_capacity(m4a_num_public(leaf_msg.len()));
    for &b in leaf_msg {
        pv.push(Mersenne31::from_u32(b as u32));
    }
    for &b in &leaf_digest {
        pv.push(Mersenne31::from_u32(b as u32));
    }
    for &b in &root {
        pv.push(Mersenne31::from_u32(b as u32));
    }
    pv.push(Mersenne31::from_u32(index));
    pv.push(Mersenne31::from_u32(depth as u32));
    for i in 0..FRI_MMCS_MAX_DEPTH {
        let bit = if i < depth { (index >> i) & 1 } else { 0 };
        pv.push(Mersenne31::from_u32(bit));
    }
    for i in 0..FRI_MMCS_MAX_DEPTH {
        let s = if i < depth { siblings[i] } else { [0u8; 32] };
        for &b in &s {
            pv.push(Mersenne31::from_u32(b as u32));
        }
    }
    for i in 0..FRI_MMCS_MAX_DEPTH {
        let d = if i < depth {
            layer_digests[i]
        } else {
            [0u8; 32]
        };
        for &b in &d {
            pv.push(Mersenne31::from_u32(b as u32));
        }
    }
    debug_assert_eq!(pv.len(), m4a_num_public(leaf_msg.len()));
    Ok(pv)
}

/// Prove a binary Merkle path as a single batched Keccak path STARK.
pub fn generate_fri_mmcs_batched_path_proof(
    row: &[Mersenne31],
    siblings: &[[u8; 32]],
    index: usize,
    expected_root: &[u8; 32],
) -> Result<FriMmcsBatchedPathProof, String> {
    let depth = siblings.len();
    if depth == 0 || depth > FRI_MMCS_MAX_DEPTH {
        return Err(format!("unsupported Merkle depth {depth}"));
    }
    let leaf_msg = val_row_to_bytes(row);
    let n_perm = num_permutations(leaf_msg.len());
    if leaf_msg.len() < 12
        || leaf_msg.len() > 2 * KECCAK_RATE
        || !leaf_msg.len().is_multiple_of(4)
        || n_perm == 0
        || n_perm > 2
    {
        return Err(format!(
            "M4a leaf msg_len {} unsupported (need 12..=272, multiple of 4, ≤2 perms; got {n_perm})",
            leaf_msg.len()
        ));
    }
    let leaf_digest = keccak256_val_leaf(row);
    if leaf_digest != hash_val_leaf_keccak(row) {
        return Err("leaf digest mismatch".into());
    }

    let mut digest = leaf_digest;
    let mut idx = index;
    let mut layer_digests = Vec::with_capacity(depth);
    let mut compress_msgs = Vec::with_capacity(depth);
    for sib in siblings {
        let (left, right) = if idx.is_multiple_of(2) {
            (digest, *sib)
        } else {
            (*sib, digest)
        };
        let mut msg = [0u8; COMPRESS_MSG_LEN];
        msg[..32].copy_from_slice(&left);
        msg[32..].copy_from_slice(&right);
        let next_d = keccak256_compress(left, right);
        digest = next_d;
        layer_digests.push(digest);
        compress_msgs.push(msg);
        idx /= 2;
    }
    if &digest != expected_root {
        return Err("folded root mismatch".into());
    }

    let air = MmcsBatchedPathAir {
        leaf_msg_len: leaf_msg.len(),
        depth,
    };
    let matrix = build_path_matrix(&leaf_msg, &compress_msgs)?;
    let pv = build_public_values(
        &leaf_msg,
        leaf_digest,
        *expected_root,
        index as u32,
        depth,
        siblings,
        &layer_digests,
    )?;
    p3_air::check_constraints(&air, &matrix, &pv);
    let config = keccak_circle_config();
    let proof = prove(&config, &air, matrix, &pv);
    let path_stark = super::prove_workspace::encode_stark_and_drop(proof, "m4a path")?;

    Ok(FriMmcsBatchedPathProof {
        depth: depth as u32,
        leaf_width: row.len() as u32,
        leaf_digest,
        layer_digests,
        path_stark,
    })
}

pub fn verify_fri_mmcs_batched_path_proof(
    row: &[Mersenne31],
    siblings: &[[u8; 32]],
    index: usize,
    expected_root: &[u8; 32],
    proof: &FriMmcsBatchedPathProof,
) -> bool {
    let depth = proof.depth as usize;
    if siblings.len() != depth
        || proof.layer_digests.len() != depth
        || row.len() as u32 != proof.leaf_width
        || depth == 0
        || depth > FRI_MMCS_MAX_DEPTH
    {
        eprintln!("[M4aPath] Failed: shape");
        return false;
    }
    let leaf_msg = val_row_to_bytes(row);
    if leaf_msg.len() != proof.leaf_width as usize * 4 {
        return false;
    }
    if proof.leaf_digest != keccak256_val_leaf(row) {
        eprintln!("[M4aPath] Failed: leaf digest");
        return false;
    }
    // Host-side path sanity (same as nested prover).
    let mut digest = proof.leaf_digest;
    let mut idx = index;
    for (i, sib) in siblings.iter().enumerate() {
        let (left, right) = if idx.is_multiple_of(2) {
            (digest, *sib)
        } else {
            (*sib, digest)
        };
        let next_d = keccak256_compress(left, right);
        if next_d != proof.layer_digests[i] {
            eprintln!("[M4aPath] Failed: layer {i} digest");
            return false;
        }
        digest = next_d;
        idx /= 2;
    }
    if &digest != expected_root {
        eprintln!("[M4aPath] Failed: root");
        return false;
    }

    let air = MmcsBatchedPathAir {
        leaf_msg_len: leaf_msg.len(),
        depth,
    };
    let pv = match build_public_values(
        &leaf_msg,
        proof.leaf_digest,
        *expected_root,
        index as u32,
        depth,
        siblings,
        &proof.layer_digests,
    ) {
        Ok(pv) => pv,
        Err(_) => return false,
    };
    let stark: p3_uni_stark::Proof<WqcStarkConfig> = match postcard::from_bytes(&proof.path_stark) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("[M4aPath] postcard: {e}");
            return false;
        }
    };
    let config = keccak_circle_config();
    match verify(&config, &air, &stark, &pv) {
        Ok(()) => true,
        Err(e) => {
            eprintln!("[M4aPath] STARK: {e:?}");
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::plonky3_stark::recursion::fri_mmcs_path::generate_fri_mmcs_path_proof;
    use p3_field::PrimeCharacteristicRing;

    #[test]
    fn m4a_path_quot_width3_depth1() {
        let row = [
            Mersenne31::from_u32(1),
            Mersenne31::from_u32(2),
            Mersenne31::from_u32(3),
        ];
        let leaf = hash_val_leaf_keccak(&row);
        let sibling = [9u8; 32];
        let root = keccak256_compress(leaf, sibling);
        let proof =
            generate_fri_mmcs_batched_path_proof(&row, &[sibling], 0, &root).expect("m4a prove");
        assert!(verify_fri_mmcs_batched_path_proof(
            &row,
            &[sibling],
            0,
            &root,
            &proof
        ));

        // Size baseline vs digest-only Poseidon PCS path (nested Keccak STARKs retired).
        let poseidon_sib =
            crate::plonky3_stark::config_poseidon::pack_digest([Mersenne31::from_u32(9); 8]);
        let poseidon_leaf = crate::plonky3_stark::recursion::merkle_keccak::hash_val_leaf(&row);
        let poseidon_root = crate::plonky3_stark::recursion::merkle_keccak::compress_digests(
            poseidon_leaf,
            poseidon_sib,
        );
        let nested = generate_fri_mmcs_path_proof(&row, &[poseidon_sib], 0, &poseidon_root)
            .expect("poseidon nested");
        let nested_bytes: usize = nested.fold_stark.len()
            + nested.leaf_keccak.stark.len()
            + nested
                .compress_starks
                .iter()
                .map(|p| p.stark.len())
                .sum::<usize>();
        eprintln!(
            "M4a size: path_stark={} vs poseidon digest-path wire={}",
            proof.path_stark.len(),
            nested_bytes
        );
        // M4a carries a real Keccak path STARK; Poseidon PCS paths are digest-only stubs.
        assert!(
            nested_bytes < proof.path_stark.len(),
            "poseidon digest path {} should be smaller than m4a {}",
            nested_bytes,
            proof.path_stark.len()
        );
    }

    #[test]
    fn m4a_path_chal_width6_depth1() {
        let row: Vec<_> = (0..6)
            .map(|i| Mersenne31::from_u32(i as u32 + 10))
            .collect();
        let leaf = hash_val_leaf_keccak(&row);
        let sibling = [3u8; 32];
        let root = keccak256_compress(sibling, leaf); // index=1
        let proof =
            generate_fri_mmcs_batched_path_proof(&row, &[sibling], 1, &root).expect("m4a prove");
        assert!(verify_fri_mmcs_batched_path_proof(
            &row,
            &[sibling],
            1,
            &root,
            &proof
        ));
    }

    #[test]
    fn m4a_path_quot_width3_depth2() {
        let row = [
            Mersenne31::from_u32(1),
            Mersenne31::from_u32(2),
            Mersenne31::from_u32(3),
        ];
        let leaf = hash_val_leaf_keccak(&row);
        let s0 = [9u8; 32];
        let s1 = [7u8; 32];
        let d0 = keccak256_compress(leaf, s0); // index bit0 = 0
        let root = keccak256_compress(s1, d0); // index bit1 = 1 → index = 2
        let proof =
            generate_fri_mmcs_batched_path_proof(&row, &[s0, s1], 2, &root).expect("m4a prove");
        assert!(verify_fri_mmcs_batched_path_proof(
            &row,
            &[s0, s1],
            2,
            &root,
            &proof
        ));
    }

    /// Idle unitary quot_batch concat is 16×W=3 = 48 M31 → 192 bytes (2 Keccak perms).
    #[test]
    fn m4a_path_concat_width48_depth1() {
        let row: Vec<_> = (0..48)
            .map(|i| Mersenne31::from_u32(i as u32 * 17 + 3))
            .collect();
        assert_eq!(val_row_to_bytes(&row).len(), 192);
        assert_eq!(num_permutations(192), 2);
        let leaf = hash_val_leaf_keccak(&row);
        let sibling = [11u8; 32];
        let root = keccak256_compress(leaf, sibling);
        let proof =
            generate_fri_mmcs_batched_path_proof(&row, &[sibling], 0, &root).expect("m4a prove");
        assert!(verify_fri_mmcs_batched_path_proof(
            &row,
            &[sibling],
            0,
            &root,
            &proof
        ));
        eprintln!(
            "M4a 2-perm leaf (W=48) path_stark={}",
            proof.path_stark.len()
        );
    }
}

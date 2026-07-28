//! R3-M4b: fold many homogeneous single-matrix Merkle paths into one group STARK.
//!
//! Builds on M4a segments: each path is `(1 + depth)` sponges; the group concatenates
//! `path_count` paths and proves them under one `MmcsGroupPathAir`.
//!
//! MVP limits (same as M4a per path):
//! - leaf messages with **1 or 2** Keccak permutations (`msg_len ≤ 2·KECCAK_RATE`)
//! - compress messages stay single-perm / 64 bytes
//! - **homogeneous** `leaf_width` and `depth` across the group
//! - batch openings (`FriChalBatchPathProof` / multi-chunk quot) deferred

#![allow(clippy::needless_range_loop)]

use std::cell::Cell;

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_mersenne_31::Mersenne31;
use p3_uni_stark::{prove, verify};

use crate::air::pad_air_matrix_for_uni_stark;
use crate::plonky3_stark::config::{keccak_circle_config, WqcStarkConfig};

use super::fri_mmcs_path::FRI_MMCS_MAX_DEPTH;
use super::fri_mmcs_path_m4a::{
    M4A_SEG_IDX_BITS, M4A_SEG_IDX_COL, M4A_SEG_ROWS, M4A_SEG_START_COL,
};
use super::keccak256_air::{
    build_sponge_matrix, COMPRESS_MSG_LEN, ROUND_BITS, ROUND_BIT_COL, SPONGE_WIDTH,
};
use super::keccak_f_air::{constrain_keccak_round_with_rc, LIVE_COL};
use super::keccak_f_native::{
    keccak256_compress, keccak256_val_leaf, num_permutations, val_row_to_bytes, KECCAK256_OUT,
    KECCAK_DELIM, KECCAK_RATE, KECCAK_ROUNDS, KECCAK_STATE_BITS, RC,
};
use super::merkle_keccak::hash_val_leaf;

/// Enough for idle unitary Val-trace + Chal-commit (80) with headroom.
pub const M4B_MAX_PATHS: usize = 128;

/// Default paths per Mmcs group STARK (`WQC_PCS_MMCS_GROUP_CHUNK` when unset).
/// Chosen at the time/size knee (~5 MiB STARK payload, ~17 min unitary leaf PCS).
pub const M4B_GROUP_CHUNK_DEFAULT: usize = 24;

/// User-facing env: max Merkle paths batched into one Mmcs group STARK during PCS prove.
pub const PCS_MMCS_GROUP_CHUNK_ENV: &str = "WQC_PCS_MMCS_GROUP_CHUNK";

thread_local! {
    /// Session override for one PCS build (spill / gate). Nested guards restore.
    static M4B_CHUNK_OVERRIDE: Cell<Option<usize>> = const { Cell::new(None) };
}

/// RAII guard that sets the thread-local Mmcs group chunk for a PCS build.
pub struct M4bChunkGuard {
    prev: Option<usize>,
}

impl M4bChunkGuard {
    pub fn set(chunk: usize) -> Self {
        let chunk = chunk.clamp(1, M4B_MAX_PATHS);
        let prev = M4B_CHUNK_OVERRIDE.with(|c| c.replace(Some(chunk)));
        Self { prev }
    }
}

impl Drop for M4bChunkGuard {
    fn drop(&mut self) {
        M4B_CHUNK_OVERRIDE.with(|c| c.set(self.prev));
    }
}

/// Env / default chunk only (ignores session override). Used by the memory gate.
pub fn m4b_group_chunk_from_env() -> usize {
    parse_group_chunk_env(PCS_MMCS_GROUP_CHUNK_ENV).unwrap_or(M4B_GROUP_CHUNK_DEFAULT)
}

fn parse_group_chunk_env(key: &str) -> Option<usize> {
    std::env::var(key)
        .ok()
        .and_then(|v| v.trim().parse::<usize>().ok())
        .filter(|&n| n >= 1)
        .map(|n| n.min(M4B_MAX_PATHS))
}

/// Peak-RAM / prove-time tunable: max paths proven in a single group STARK.
/// Session override (PCS memory spill) wins over `WQC_PCS_MMCS_GROUP_CHUNK`.
pub fn m4b_group_chunk() -> usize {
    if let Some(o) = M4B_CHUNK_OVERRIDE.with(|c| c.get()) {
        return o;
    }
    m4b_group_chunk_from_env()
}
pub const M4B_PATH_IDX_BITS: usize = 7;
pub const M4B_PATH_IDX_COL: usize = M4A_SEG_IDX_COL + M4A_SEG_IDX_BITS;
pub const M4B_GROUP_WIDTH: usize = SPONGE_WIDTH + 1 + M4A_SEG_IDX_BITS + M4B_PATH_IDX_BITS;

/// One opening statement for the group fold (single-matrix Val/Chal path).
#[derive(Debug, Clone)]
pub struct MmcsPathStatement {
    pub row: Vec<Mersenne31>,
    pub siblings: Vec<[u8; 32]>,
    pub index: usize,
    pub root: [u8; 32],
}

/// All paths of a homogeneous group as one outer Plonky3 STARK.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KeccakGroupFoldProof {
    pub path_count: u32,
    pub depth: u32,
    pub leaf_width: u32,
    pub leaf_digests: Vec<[u8; 32]>,
    pub layer_digests: Vec<Vec<[u8; 32]>>,
    pub group_stark: Vec<u8>,
}

#[derive(Copy, Clone, Debug)]
pub struct MmcsGroupPathAir {
    pub leaf_msg_len: usize,
    pub depth: usize,
    pub path_count: usize,
}

/// Public layout:
/// `path_count | depth | { leaf_msg[L] | leaf_digest[32] | root[32] | index
///   | index_bits[MAX] | siblings[MAX*32] | layer_digests[MAX*32] } × path_count`
pub fn m4b_path_stride(leaf_msg_len: usize) -> usize {
    leaf_msg_len + 65 + FRI_MMCS_MAX_DEPTH + FRI_MMCS_MAX_DEPTH * 64
}

pub fn m4b_num_public(leaf_msg_len: usize, path_count: usize) -> usize {
    2 + path_count * m4b_path_stride(leaf_msg_len)
}

const fn pv_path_base(path: usize, leaf_msg_len: usize) -> usize {
    2 + path * (leaf_msg_len + 65 + FRI_MMCS_MAX_DEPTH + FRI_MMCS_MAX_DEPTH * 64)
}
const fn pv_leaf_digest_off(path: usize, leaf_msg_len: usize) -> usize {
    pv_path_base(path, leaf_msg_len) + leaf_msg_len
}
const fn pv_root_off(path: usize, leaf_msg_len: usize) -> usize {
    pv_path_base(path, leaf_msg_len) + leaf_msg_len + 32
}
const fn pv_index_off(path: usize, leaf_msg_len: usize) -> usize {
    pv_path_base(path, leaf_msg_len) + leaf_msg_len + 64
}
const fn pv_index_bits_off(path: usize, leaf_msg_len: usize) -> usize {
    pv_path_base(path, leaf_msg_len) + leaf_msg_len + 65
}
const fn pv_siblings_off(path: usize, leaf_msg_len: usize) -> usize {
    pv_path_base(path, leaf_msg_len) + leaf_msg_len + 65 + FRI_MMCS_MAX_DEPTH
}
const fn pv_layers_off(path: usize, leaf_msg_len: usize) -> usize {
    pv_path_base(path, leaf_msg_len)
        + leaf_msg_len
        + 65
        + FRI_MMCS_MAX_DEPTH
        + FRI_MMCS_MAX_DEPTH * 32
}

impl<F: Field> BaseAir<F> for MmcsGroupPathAir {
    fn width(&self) -> usize {
        M4B_GROUP_WIDTH
    }

    fn max_constraint_degree(&self) -> Option<usize> {
        None
    }

    fn num_public_values(&self) -> usize {
        m4b_num_public(self.leaf_msg_len, self.path_count)
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

fn bits_value_expr<AB: AirBuilder>(bits: &[AB::Var]) -> AB::Expr
where
    AB::F: PrimeCharacteristicRing,
{
    round_value_expr::<AB>(bits)
}

fn rc_bits_from_round<AB: AirBuilder>(round_bits: &[AB::Var]) -> Vec<AB::Expr>
where
    AB::F: PrimeCharacteristicRing,
{
    let mut rc_bits = vec![AB::Expr::ZERO; 64];
    for (r, &rc) in RC.iter().enumerate() {
        let sel = eq_bits_const::<AB>(round_bits, r as u32);
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
    msg_base: usize,
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
            pv[msg_base + byte_i].clone()
        } else if is_delim {
            AB::F::from_u32(KECCAK_DELIM as u32).into()
        } else if is_end {
            AB::F::from_u32(0x80).into()
        } else {
            AB::Expr::ZERO
        }
    } else {
        pv[msg_base + byte_i].clone()
    }
}

/// Rate-byte XOR mask absorbed between permutation 0 and 1 (2-perm leaf only).
fn second_block_rate_byte<AB: AirBuilder>(
    pv: &[AB::Expr],
    msg_base: usize,
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
        pv[msg_base + KECCAK_RATE + byte_i].clone()
    } else if is_delim {
        AB::F::from_u32(KECCAK_DELIM as u32).into()
    } else if is_end {
        AB::F::from_u32(0x80).into()
    } else {
        AB::Expr::ZERO
    }
}

impl<AB: AirBuilder> Air<AB> for MmcsGroupPathAir
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
        let path_count = self.path_count;

        for i in 0..M4B_GROUP_WIDTH {
            let b: AB::Expr = curr[i].into();
            builder.assert_zero(b.clone() * (b - one.clone()));
        }

        let live_c: AB::Expr = curr[LIVE_COL].into();
        let live_n: AB::Expr = next[LIVE_COL].into();
        let seg_start_n: AB::Expr = next[M4A_SEG_START_COL].into();
        let seg_start_c: AB::Expr = curr[M4A_SEG_START_COL].into();
        let seg_bits_c = &curr[M4A_SEG_IDX_COL..M4A_SEG_IDX_COL + M4A_SEG_IDX_BITS];
        let seg_bits_n = &next[M4A_SEG_IDX_COL..M4A_SEG_IDX_COL + M4A_SEG_IDX_BITS];
        let path_bits_c = &curr[M4B_PATH_IDX_COL..M4B_PATH_IDX_COL + M4B_PATH_IDX_BITS];
        let path_bits_n = &next[M4B_PATH_IDX_COL..M4B_PATH_IDX_COL + M4B_PATH_IDX_BITS];
        let round_c = &curr[ROUND_BIT_COL..ROUND_BIT_COL + ROUND_BITS];
        let round_n = &next[ROUND_BIT_COL..ROUND_BIT_COL + ROUND_BITS];
        let round_val_c = round_value_expr::<AB>(round_c);
        let round_val_n = round_value_expr::<AB>(round_n);
        let path_val_c = bits_value_expr::<AB>(path_bits_c);
        let path_val_n = bits_value_expr::<AB>(path_bits_n);

        let mut sum_eq = AB::Expr::ZERO;
        for r in 0..KECCAK_ROUNDS {
            sum_eq += eq_bits_const::<AB>(round_c, r as u32);
        }
        builder.assert_zero(live_c.clone() * (sum_eq - one.clone()));
        for k in 0..ROUND_BITS {
            let b: AB::Expr = round_c[k].into();
            builder.assert_zero((one.clone() - live_c.clone()) * b);
        }

        let rc_bits = rc_bits_from_round::<AB>(round_c);
        let is_tr = builder.is_transition();
        let both_live = live_c.clone() * live_n.clone();
        let wrap = eq_bits_const::<AB>(round_c, 23) * eq_bits_const::<AB>(round_n, 0);
        let mut same_meta = one.clone() - seg_start_n.clone();
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
        let cont = both_live.clone() * (one.clone() - wrap.clone()) * same_meta.clone();

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

        let to_final = live_c.clone() * (one.clone() - live_n.clone()) * same_meta.clone();
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
            builder.assert_zero(is_tr.clone() * idle.clone() * same_meta.clone() * (n - c));
        }
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

        // Path index: stays put unless next row starts a new path (seg_start ∧ seg_idx=0).
        let new_path = seg_start_n.clone() * eq_bits_const::<AB>(seg_bits_n, 0);
        builder.assert_zero(
            is_tr.clone()
                * (one.clone() - new_path.clone())
                * (path_val_n.clone() - path_val_c.clone()),
        );
        builder.assert_zero(
            is_tr.clone() * new_path * (path_val_n - path_val_c.clone() - one.clone()),
        );

        builder.assert_zero(pv[0].clone() - AB::Expr::from(AB::F::from_u32(path_count as u32)));
        builder.assert_zero(pv[1].clone() - AB::Expr::from(AB::F::from_u32(depth as u32)));

        for p in 0..path_count {
            let path_sel = eq_bits_const::<AB>(path_bits_c, p as u32);
            let msg_base = pv_path_base(p, l);
            let leaf_d_base = pv_leaf_digest_off(p, l);
            let sib_base = pv_siblings_off(p, l);
            let layer_base = pv_layers_off(p, l);
            let idx_bits_base = pv_index_bits_off(p, l);
            let root_base = pv_root_off(p, l);

            let leaf_start =
                seg_start_c.clone() * eq_bits_const::<AB>(seg_bits_c, 0) * path_sel.clone();
            for byte_i in 0..KECCAK_RATE {
                let packed = pack_byte_from_state_bits::<AB>(&curr[..KECCAK_STATE_BITS], byte_i);
                let want = first_block_rate_byte_leaf::<AB>(&pv, msg_base, l, byte_i);
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
                    * same_meta.clone()
                    * eq_bits_const::<AB>(seg_bits_c, 0)
                    * path_sel.clone();
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
                    let want = second_block_rate_byte::<AB>(&pv, msg_base, l, byte_i);
                    builder.assert_zero(wrap_en.clone() * (xor_pack - want));
                }
                for i in KECCAK_RATE * 8..KECCAK_STATE_BITS {
                    let nb: AB::Expr = next[i].into();
                    builder.assert_zero(wrap_en.clone() * (nb - expected[i].clone()));
                }
                builder.assert_zero(wrap_en * round_val_n.clone());
            }

            for layer in 0..depth {
                let start = seg_start_c.clone()
                    * eq_bits_const::<AB>(seg_bits_c, (layer + 1) as u32)
                    * path_sel.clone();
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
                    let packed_l =
                        pack_byte_from_state_bits::<AB>(&curr[..KECCAK_STATE_BITS], byte_i);
                    let packed_r =
                        pack_byte_from_state_bits::<AB>(&curr[..KECCAK_STATE_BITS], 32 + byte_i);
                    builder.assert_zero(start.clone() * (packed_l - left));
                    builder.assert_zero(start.clone() * (packed_r - right));
                }
                for byte_i in COMPRESS_MSG_LEN..KECCAK_RATE {
                    let packed =
                        pack_byte_from_state_bits::<AB>(&curr[..KECCAK_STATE_BITS], byte_i);
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

            let leaf_idle = idle.clone() * eq_bits_const::<AB>(seg_bits_c, 0) * path_sel.clone();
            for byte_i in 0..KECCAK256_OUT {
                let packed = pack_byte_from_state_bits::<AB>(&curr[..KECCAK_STATE_BITS], byte_i);
                builder
                    .assert_zero(leaf_idle.clone() * (packed - pv[leaf_d_base + byte_i].clone()));
            }
            for layer in 0..depth {
                let layer_idle = idle.clone()
                    * eq_bits_const::<AB>(seg_bits_c, (layer + 1) as u32)
                    * path_sel.clone();
                for byte_i in 0..KECCAK256_OUT {
                    let packed =
                        pack_byte_from_state_bits::<AB>(&curr[..KECCAK_STATE_BITS], byte_i);
                    builder.assert_zero(
                        layer_idle.clone()
                            * (packed - pv[layer_base + layer * 32 + byte_i].clone()),
                    );
                }
            }

            let last = depth - 1;
            for byte_i in 0..32 {
                builder.assert_zero(
                    pv[layer_base + last * 32 + byte_i].clone() - pv[root_base + byte_i].clone(),
                );
            }

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
            builder.assert_zero(acc - pv[pv_index_off(p, l)].clone());
        }

        builder
            .when_first_row()
            .assert_zero(AB::Expr::from(curr[M4A_SEG_START_COL]) - one.clone());
        for k in 0..M4A_SEG_IDX_BITS {
            builder
                .when_first_row()
                .assert_zero(AB::Expr::from(curr[M4A_SEG_IDX_COL + k]));
        }
        for k in 0..M4B_PATH_IDX_BITS {
            builder
                .when_first_row()
                .assert_zero(AB::Expr::from(curr[M4B_PATH_IDX_COL + k]));
        }
    }
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

fn append_sponge_segment(
    values: &mut Vec<Mersenne31>,
    msg: &[u8],
    seg_idx: usize,
    path_idx: usize,
) -> Result<(), String> {
    let n_perm = num_permutations(msg.len());
    if seg_idx == 0 {
        if n_perm == 0 || n_perm > 2 {
            return Err(format!(
                "M4b leaf requires 1..=2 perms (msg_len {}); got {n_perm}",
                msg.len()
            ));
        }
    } else if n_perm != 1 {
        return Err(format!(
            "M4b compress requires single-perm sponge (msg_len {}); got {n_perm}",
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
        push_row_meta(values, r == 0, seg_idx, path_idx);
    }
    Ok(())
}

fn build_group_matrix(
    paths: &[(Vec<u8>, Vec<[u8; COMPRESS_MSG_LEN]>)],
) -> Result<RowMajorMatrix<Mersenne31>, String> {
    let mut values = Vec::new();
    for (p, (leaf_msg, compress_msgs)) in paths.iter().enumerate() {
        append_sponge_segment(&mut values, leaf_msg, 0, p)?;
        for (i, msg) in compress_msgs.iter().enumerate() {
            append_sponge_segment(&mut values, msg, i + 1, p)?;
        }
    }
    Ok(pad_air_matrix_for_uni_stark(RowMajorMatrix::new(
        values,
        M4B_GROUP_WIDTH,
    )))
}

type PathFoldWitness = (
    Vec<u8>,
    [u8; 32],
    Vec<[u8; 32]>,
    Vec<[u8; COMPRESS_MSG_LEN]>,
);

fn fold_path_witness(
    row: &[Mersenne31],
    siblings: &[[u8; 32]],
    index: usize,
    expected_root: &[u8; 32],
) -> Result<PathFoldWitness, String> {
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
            "M4b leaf msg_len {} unsupported (need 12..=272, multiple of 4, ≤2 perms; got {n_perm})",
            leaf_msg.len()
        ));
    }
    let leaf_digest = keccak256_val_leaf(row);
    if leaf_digest != hash_val_leaf(row) {
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
    Ok((leaf_msg, leaf_digest, layer_digests, compress_msgs))
}

#[allow(clippy::too_many_arguments)]
fn build_public_values(
    leaf_msg_len: usize,
    depth: usize,
    path_count: usize,
    leaf_msgs: &[Vec<u8>],
    leaf_digests: &[[u8; 32]],
    roots: &[[u8; 32]],
    indices: &[u32],
    siblings: &[Vec<[u8; 32]>],
    layer_digests: &[Vec<[u8; 32]>],
) -> Result<Vec<Mersenne31>, String> {
    if path_count == 0 || path_count > M4B_MAX_PATHS {
        return Err(format!("path_count {path_count} out of range"));
    }
    if depth == 0 || depth > FRI_MMCS_MAX_DEPTH {
        return Err(format!("depth {depth} out of range"));
    }
    let mut pv = Vec::with_capacity(m4b_num_public(leaf_msg_len, path_count));
    pv.push(Mersenne31::from_u32(path_count as u32));
    pv.push(Mersenne31::from_u32(depth as u32));
    for p in 0..path_count {
        if leaf_msgs[p].len() != leaf_msg_len {
            return Err("inhomogeneous leaf_msg_len".into());
        }
        if siblings[p].len() != depth || layer_digests[p].len() != depth {
            return Err("siblings/layer_digests length mismatch".into());
        }
        for &b in &leaf_msgs[p] {
            pv.push(Mersenne31::from_u32(b as u32));
        }
        for &b in &leaf_digests[p] {
            pv.push(Mersenne31::from_u32(b as u32));
        }
        for &b in &roots[p] {
            pv.push(Mersenne31::from_u32(b as u32));
        }
        pv.push(Mersenne31::from_u32(indices[p]));
        for i in 0..FRI_MMCS_MAX_DEPTH {
            let bit = if i < depth { (indices[p] >> i) & 1 } else { 0 };
            pv.push(Mersenne31::from_u32(bit));
        }
        for i in 0..FRI_MMCS_MAX_DEPTH {
            let s = if i < depth { siblings[p][i] } else { [0u8; 32] };
            for &b in &s {
                pv.push(Mersenne31::from_u32(b as u32));
            }
        }
        for i in 0..FRI_MMCS_MAX_DEPTH {
            let d = if i < depth {
                layer_digests[p][i]
            } else {
                [0u8; 32]
            };
            for &b in &d {
                pv.push(Mersenne31::from_u32(b as u32));
            }
        }
    }
    debug_assert_eq!(pv.len(), m4b_num_public(leaf_msg_len, path_count));
    Ok(pv)
}

/// Prove a homogeneous set of single-matrix Merkle paths as one group STARK.
pub fn generate_keccak_group_fold_proof(
    statements: &[MmcsPathStatement],
) -> Result<KeccakGroupFoldProof, String> {
    let path_count = statements.len();
    if path_count == 0 || path_count > M4B_MAX_PATHS {
        return Err(format!(
            "path_count {path_count} out of range 1..={M4B_MAX_PATHS}"
        ));
    }
    let depth = statements[0].siblings.len();
    let leaf_width = statements[0].row.len();
    if depth == 0 || depth > FRI_MMCS_MAX_DEPTH {
        return Err(format!("unsupported Merkle depth {depth}"));
    }

    let mut leaf_msgs = Vec::with_capacity(path_count);
    let mut leaf_digests = Vec::with_capacity(path_count);
    let mut layer_digests = Vec::with_capacity(path_count);
    let mut compress_per_path = Vec::with_capacity(path_count);
    let mut roots = Vec::with_capacity(path_count);
    let mut indices = Vec::with_capacity(path_count);
    let mut siblings = Vec::with_capacity(path_count);

    for (p, stmt) in statements.iter().enumerate() {
        if stmt.siblings.len() != depth {
            return Err(format!("path {p}: inhomogeneous depth"));
        }
        if stmt.row.len() != leaf_width {
            return Err(format!("path {p}: inhomogeneous leaf_width"));
        }
        let (leaf_msg, leaf_digest, layers, compress_msgs) =
            fold_path_witness(&stmt.row, &stmt.siblings, stmt.index, &stmt.root)?;
        leaf_msgs.push(leaf_msg);
        leaf_digests.push(leaf_digest);
        layer_digests.push(layers);
        compress_per_path.push(compress_msgs);
        roots.push(stmt.root);
        indices.push(stmt.index as u32);
        siblings.push(stmt.siblings.clone());
    }

    let leaf_msg_len = leaf_msgs[0].len();
    let air = MmcsGroupPathAir {
        leaf_msg_len,
        depth,
        path_count,
    };
    // Build the AIR matrix, then free compress witnesses before prove.
    let matrix = {
        let matrix_paths: Vec<_> = leaf_msgs
            .iter()
            .zip(compress_per_path.iter())
            .map(|(m, c)| (m.clone(), c.clone()))
            .collect();
        build_group_matrix(&matrix_paths)?
    };
    drop(compress_per_path);

    let pv = build_public_values(
        leaf_msg_len,
        depth,
        path_count,
        &leaf_msgs,
        &leaf_digests,
        &roots,
        &indices,
        &siblings,
        &layer_digests,
    )?;
    // Wire result keeps digests only; free msg/index/sibling copies before prove.
    drop(leaf_msgs);
    drop(roots);
    drop(indices);
    drop(siblings);

    p3_air::check_constraints(&air, &matrix, &pv);
    let config = keccak_circle_config();
    let proof = prove(&config, &air, matrix, &pv);
    let group_stark = super::prove_workspace::encode_stark_and_drop(proof, "m4b group")?;

    Ok(KeccakGroupFoldProof {
        path_count: path_count as u32,
        depth: depth as u32,
        leaf_width: leaf_width as u32,
        leaf_digests,
        layer_digests,
        group_stark,
    })
}

pub fn verify_keccak_group_fold_proof(
    statements: &[MmcsPathStatement],
    proof: &KeccakGroupFoldProof,
) -> bool {
    let path_count = proof.path_count as usize;
    let depth = proof.depth as usize;
    if statements.len() != path_count
        || proof.leaf_digests.len() != path_count
        || proof.layer_digests.len() != path_count
        || path_count == 0
        || path_count > M4B_MAX_PATHS
        || depth == 0
        || depth > FRI_MMCS_MAX_DEPTH
    {
        eprintln!("[M4bGroup] Failed: shape");
        return false;
    }

    let leaf_width = proof.leaf_width as usize;
    let mut leaf_msgs = Vec::with_capacity(path_count);
    let mut roots = Vec::with_capacity(path_count);
    let mut indices = Vec::with_capacity(path_count);
    let mut siblings = Vec::with_capacity(path_count);

    for (p, stmt) in statements.iter().enumerate() {
        if stmt.row.len() != leaf_width || stmt.siblings.len() != depth {
            eprintln!("[M4bGroup] Failed: path {p} shape");
            return false;
        }
        if proof.layer_digests[p].len() != depth {
            eprintln!("[M4bGroup] Failed: path {p} layers");
            return false;
        }
        let leaf_msg = val_row_to_bytes(&stmt.row);
        if leaf_msg.len() != leaf_width * 4 {
            return false;
        }
        if proof.leaf_digests[p] != keccak256_val_leaf(&stmt.row) {
            eprintln!("[M4bGroup] Failed: path {p} leaf digest");
            return false;
        }
        let mut digest = proof.leaf_digests[p];
        let mut idx = stmt.index;
        for (i, sib) in stmt.siblings.iter().enumerate() {
            let (left, right) = if idx.is_multiple_of(2) {
                (digest, *sib)
            } else {
                (*sib, digest)
            };
            let next_d = keccak256_compress(left, right);
            if next_d != proof.layer_digests[p][i] {
                eprintln!("[M4bGroup] Failed: path {p} layer {i}");
                return false;
            }
            digest = next_d;
            idx /= 2;
        }
        if digest != stmt.root {
            eprintln!("[M4bGroup] Failed: path {p} root");
            return false;
        }
        leaf_msgs.push(leaf_msg);
        roots.push(stmt.root);
        indices.push(stmt.index as u32);
        siblings.push(stmt.siblings.clone());
    }

    let leaf_msg_len = leaf_msgs[0].len();
    let air = MmcsGroupPathAir {
        leaf_msg_len,
        depth,
        path_count,
    };
    let pv = match build_public_values(
        leaf_msg_len,
        depth,
        path_count,
        &leaf_msgs,
        &proof.leaf_digests,
        &roots,
        &indices,
        &siblings,
        &proof.layer_digests,
    ) {
        Ok(pv) => pv,
        Err(_) => return false,
    };
    let stark: p3_uni_stark::Proof<WqcStarkConfig> = match postcard::from_bytes(&proof.group_stark)
    {
        Ok(p) => p,
        Err(e) => {
            eprintln!("[M4bGroup] postcard: {e}");
            return false;
        }
    };
    let config = keccak_circle_config();
    match verify(&config, &air, &stark, &pv) {
        Ok(()) => true,
        Err(e) => {
            eprintln!("[M4bGroup] STARK: {e:?}");
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::plonky3_stark::recursion::fri_mmcs_path_m4a::generate_fri_mmcs_batched_path_proof;
    use p3_field::PrimeCharacteristicRing;

    fn stmt_w3(index: usize, sibling: [u8; 32], seed: u32) -> (MmcsPathStatement, [u8; 32]) {
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
        (
            MmcsPathStatement {
                row,
                siblings: vec![sibling],
                index,
                root,
            },
            root,
        )
    }

    #[test]
    fn m4b_group_two_paths_width3_depth1() {
        let (s0, _) = stmt_w3(0, [9u8; 32], 1);
        let (s1, _) = stmt_w3(1, [3u8; 32], 10);
        let stmts = vec![s0.clone(), s1.clone()];
        let proof = generate_keccak_group_fold_proof(&stmts).expect("m4b prove");
        assert!(verify_keccak_group_fold_proof(&stmts, &proof));
        assert_eq!(proof.path_count, 2);
        assert_eq!(proof.depth, 1);
        assert_eq!(proof.leaf_width, 3);

        let m4a0 = generate_fri_mmcs_batched_path_proof(&s0.row, &s0.siblings, s0.index, &s0.root)
            .expect("m4a0");
        let m4a1 = generate_fri_mmcs_batched_path_proof(&s1.row, &s1.siblings, s1.index, &s1.root)
            .expect("m4a1");
        let separate = m4a0.path_stark.len() + m4a1.path_stark.len();
        eprintln!(
            "M4b size: group_stark={} vs 2×M4a={}",
            proof.group_stark.len(),
            separate
        );
        assert!(
            proof.group_stark.len() < separate,
            "m4b {} not smaller than 2×m4a {}",
            proof.group_stark.len(),
            separate
        );
    }

    #[test]
    fn m4b_group_four_paths_width3_depth1() {
        let stmts: Vec<_> = (0..4)
            .map(|i| {
                let (s, _) = stmt_w3(i % 2, [u8::try_from(i + 5).unwrap(); 32], 20 + i as u32);
                s
            })
            .collect();
        let proof = generate_keccak_group_fold_proof(&stmts).expect("m4b prove");
        assert!(verify_keccak_group_fold_proof(&stmts, &proof));

        let mut separate = 0usize;
        for s in &stmts {
            let p = generate_fri_mmcs_batched_path_proof(&s.row, &s.siblings, s.index, &s.root)
                .expect("m4a");
            separate += p.path_stark.len();
        }
        eprintln!(
            "M4b N=4 size: group_stark={} vs 4×M4a={}",
            proof.group_stark.len(),
            separate
        );
        assert!(
            proof.group_stark.len() < separate,
            "m4b {} not smaller than 4×m4a {}",
            proof.group_stark.len(),
            separate
        );
    }

    /// Two homogeneous 48-wide (192-byte / 2-perm) leaves, depth 1.
    #[test]
    fn m4b_group_two_concat_width48_depth1() {
        let stmts: Vec<_> = (0..2)
            .map(|p| {
                let row: Vec<_> = (0..48)
                    .map(|i| Mersenne31::from_u32((p as u32 + 1) * 100 + i as u32 * 17 + 3))
                    .collect();
                assert_eq!(val_row_to_bytes(&row).len(), 192);
                let leaf = hash_val_leaf(&row);
                let sibling = [u8::try_from(p + 11).unwrap(); 32];
                let index = p;
                let root = if index % 2 == 0 {
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
            })
            .collect();
        let proof = generate_keccak_group_fold_proof(&stmts).expect("m4b prove");
        assert!(verify_keccak_group_fold_proof(&stmts, &proof));
        assert_eq!(proof.path_count, 2);
        assert_eq!(proof.leaf_width, 48);

        let mut separate = 0usize;
        for s in &stmts {
            let p = generate_fri_mmcs_batched_path_proof(&s.row, &s.siblings, s.index, &s.root)
                .expect("m4a");
            separate += p.path_stark.len();
        }
        eprintln!(
            "M4b W=48 N=2 size: group_stark={} vs 2×M4a={}",
            proof.group_stark.len(),
            separate
        );
    }
}

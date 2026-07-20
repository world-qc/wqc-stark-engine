//! V6 recursive aggregation transcript (R3-M2 / M2.5 / M3b2 / M3c3 / M3d): M1 fields +
//! AggregationAir PCS certs (Merkle fold + Keccak + FriFold + DeepRo + FRI Val/Challenge Mmcs).

use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_mersenne_31::Mersenne31;

use crate::aggregation::CHILD_HASH_LEN;
use crate::plonky3_stark::aggregation_air::AGG_WIDTH;

use super::air::{REC_KIND_AGG, REC_KIND_LEAF};
use super::context::RecursiveAggregationContext;
use super::deep_ro_air::DeepRoStepProof;
use super::deep_ro_bind::{AGG_DEEP_RO_MAX, AGG_DEEP_RO_TRACE_MAX};
use super::deep_ro_trace_air::DeepRoTraceStepProof;
use super::fri_fold_air::FriFoldStepProof;
use super::fri_fold_bind::{AGG_FRI_MAX_FOLD_YS, AGG_FRI_MAX_ROUNDS, AGG_FRI_PROVEN_QUERIES};
use super::fri_mmcs_bind::{FriChalBatchPathProof, FriChalMmcsQueryProof, FriValMmcsQueryProof};
use super::fri_mmcs_path::{FriMmcsPathProof, FRI_MMCS_MAX_DEPTH};
use super::keccak256_air::Keccak256StarkProof;
use super::keccak_merkle_air::{KeccakMerklePathProof, MERKLE_FOLD_DEPTH};
use super::opening_cert::{AggPcsCertificate, AGG_PCS_MAX_SIBLINGS};
use super::STARK_DIGEST_LEN;

pub const V6_REC_AGG_INNER_MARKER: &[u8] = b"_WQC_REC_AGG_V6_";
pub const V6_REC_TAIL_MARKER: &[u8] = b"_WQC_REC_TAIL_V6_";

fn read_cstr(proof: &[u8], offset: usize) -> Option<(String, usize)> {
    let tail = proof.get(offset..)?;
    let end_rel = tail.iter().position(|&b| b == 0)?;
    let end = offset + end_rel;
    let value = std::str::from_utf8(&proof[offset..end]).ok()?;
    Some((value.to_string(), end + 1))
}

fn read_u32_le(proof: &[u8], offset: usize) -> Option<(u32, usize)> {
    let bytes = proof.get(offset..offset + 4)?;
    let mut buf = [0u8; 4];
    buf.copy_from_slice(bytes);
    Some((u32::from_le_bytes(buf), offset + 4))
}

fn read_fixed<const N: usize>(proof: &[u8], offset: usize) -> Option<([u8; N], usize)> {
    let bytes = proof.get(offset..offset + N)?;
    let mut out = [0u8; N];
    out.copy_from_slice(bytes);
    Some((out, offset + N))
}

fn write_m31_row(out: &mut Vec<u8>, row: &[Mersenne31]) {
    for v in row {
        out.extend_from_slice(&v.as_canonical_u32().to_le_bytes());
    }
}

fn read_m31_row(proof: &[u8], offset: usize, len: usize) -> Option<(Vec<Mersenne31>, usize)> {
    let need = len.checked_mul(4)?;
    let bytes = proof.get(offset..offset + need)?;
    let mut row = Vec::with_capacity(len);
    for chunk in bytes.chunks_exact(4) {
        let mut buf = [0u8; 4];
        buf.copy_from_slice(chunk);
        row.push(Mersenne31::from_u32(u32::from_le_bytes(buf)));
    }
    Some((row, offset + need))
}

fn encode_keccak256_stark(out: &mut Vec<u8>, proof: &Keccak256StarkProof) {
    out.extend_from_slice(&proof.msg_len.to_le_bytes());
    out.extend_from_slice(&proof.digest);
    out.extend_from_slice(&(proof.stark.len() as u32).to_le_bytes());
    out.extend_from_slice(&proof.stark);
}

fn decode_keccak256_stark(proof: &[u8], offset: usize) -> Option<(Keccak256StarkProof, usize)> {
    let (msg_len, cursor) = read_u32_le(proof, offset)?;
    let (digest, cursor) = read_fixed::<32>(proof, cursor)?;
    let (stark_len, cursor) = read_u32_le(proof, cursor)?;
    let end = cursor + stark_len as usize;
    let stark = proof.get(cursor..end)?.to_vec();
    Some((
        Keccak256StarkProof {
            msg_len,
            digest,
            stark,
        },
        end,
    ))
}

fn encode_merkle_fold(out: &mut Vec<u8>, fold: &KeccakMerklePathProof) {
    out.extend_from_slice(&fold.leaf_digest);
    out.extend_from_slice(&(fold.layer_digests.len() as u32).to_le_bytes());
    for d in &fold.layer_digests {
        out.extend_from_slice(d);
    }
    out.extend_from_slice(&(fold.fold_stark.len() as u32).to_le_bytes());
    out.extend_from_slice(&fold.fold_stark);
    encode_keccak256_stark(out, &fold.leaf_keccak);
    out.extend_from_slice(&(fold.compress_starks.len() as u32).to_le_bytes());
    for c in &fold.compress_starks {
        encode_keccak256_stark(out, c);
    }
}

fn decode_merkle_fold(proof: &[u8], offset: usize) -> Option<(KeccakMerklePathProof, usize)> {
    let (leaf_digest, cursor) = read_fixed::<32>(proof, offset)?;
    let (layer_len, cursor) = read_u32_le(proof, cursor)?;
    if layer_len as usize != MERKLE_FOLD_DEPTH {
        return None;
    }
    let mut layer_digests = Vec::with_capacity(MERKLE_FOLD_DEPTH);
    let mut cursor = cursor;
    for _ in 0..MERKLE_FOLD_DEPTH {
        let (d, next) = read_fixed::<32>(proof, cursor)?;
        layer_digests.push(d);
        cursor = next;
    }
    let (stark_len, cursor) = read_u32_le(proof, cursor)?;
    let end = cursor + stark_len as usize;
    let fold_stark = proof.get(cursor..end)?.to_vec();
    let (leaf_keccak, cursor) = decode_keccak256_stark(proof, end)?;
    let (comp_len, cursor) = read_u32_le(proof, cursor)?;
    if comp_len as usize != MERKLE_FOLD_DEPTH {
        return None;
    }
    let mut compress_starks = Vec::with_capacity(MERKLE_FOLD_DEPTH);
    let mut cursor = cursor;
    for _ in 0..MERKLE_FOLD_DEPTH {
        let (c, next) = decode_keccak256_stark(proof, cursor)?;
        compress_starks.push(c);
        cursor = next;
    }
    Some((
        KeccakMerklePathProof {
            leaf_digest,
            layer_digests,
            fold_stark,
            leaf_keccak,
            compress_starks,
        },
        cursor,
    ))
}

fn encode_fri_fold(out: &mut Vec<u8>, fold: &FriFoldStepProof) {
    out.extend_from_slice(&fold.index.to_le_bytes());
    out.extend_from_slice(&fold.log_folded_height.to_le_bytes());
    out.extend_from_slice(&fold.t_inv.as_canonical_u32().to_le_bytes());
    write_m31_row(out, &fold.beta_limbs);
    write_m31_row(out, &fold.v0_limbs);
    write_m31_row(out, &fold.v1_limbs);
    write_m31_row(out, &fold.out_limbs);
    out.extend_from_slice(&(fold.fold_stark.len() as u32).to_le_bytes());
    out.extend_from_slice(&fold.fold_stark);
}

fn decode_fri_fold(proof: &[u8], offset: usize) -> Option<(FriFoldStepProof, usize)> {
    let (index, cursor) = read_u32_le(proof, offset)?;
    let (log_folded_height, cursor) = read_u32_le(proof, cursor)?;
    let (t_vec, cursor) = read_m31_row(proof, cursor, 1)?;
    let (beta_vec, cursor) = read_m31_row(proof, cursor, 3)?;
    let (v0_vec, cursor) = read_m31_row(proof, cursor, 3)?;
    let (v1_vec, cursor) = read_m31_row(proof, cursor, 3)?;
    let (out_vec, cursor) = read_m31_row(proof, cursor, 3)?;
    let (stark_len, cursor) = read_u32_le(proof, cursor)?;
    let end = cursor + stark_len as usize;
    let fold_stark = proof.get(cursor..end)?.to_vec();
    let mut beta_limbs = [Mersenne31::ZERO; 3];
    let mut v0_limbs = [Mersenne31::ZERO; 3];
    let mut v1_limbs = [Mersenne31::ZERO; 3];
    let mut out_limbs = [Mersenne31::ZERO; 3];
    beta_limbs.copy_from_slice(&beta_vec);
    v0_limbs.copy_from_slice(&v0_vec);
    v1_limbs.copy_from_slice(&v1_vec);
    out_limbs.copy_from_slice(&out_vec);
    Some((
        FriFoldStepProof {
            index,
            log_folded_height,
            t_inv: t_vec[0],
            beta_limbs,
            v0_limbs,
            v1_limbs,
            out_limbs,
            fold_stark,
        },
        end,
    ))
}

fn encode_fri_folds(out: &mut Vec<u8>, folds: &[FriFoldStepProof]) {
    out.extend_from_slice(&(folds.len() as u32).to_le_bytes());
    for fold in folds {
        encode_fri_fold(out, fold);
    }
}

fn decode_fri_folds(
    proof: &[u8],
    offset: usize,
    max: usize,
) -> Option<(Vec<FriFoldStepProof>, usize)> {
    let (len, cursor) = read_u32_le(proof, offset)?;
    if len as usize == 0 || len as usize > max {
        return None;
    }
    let mut folds = Vec::with_capacity(len as usize);
    let mut cursor = cursor;
    for _ in 0..len {
        let (fold, next) = decode_fri_fold(proof, cursor)?;
        folds.push(fold);
        cursor = next;
    }
    Some((folds, cursor))
}

fn encode_deep_ro(out: &mut Vec<u8>, deep: &DeepRoStepProof) {
    out.extend_from_slice(&deep.sx.as_canonical_u32().to_le_bytes());
    out.extend_from_slice(&deep.sy.as_canonical_u32().to_le_bytes());
    write_m31_row(out, &deep.alpha_limbs);
    write_m31_row(out, &deep.px);
    for pz in &deep.pz_limbs {
        write_m31_row(out, pz);
    }
    write_m31_row(out, &deep.lambda_limbs);
    out.extend_from_slice(&deep.v_n.as_canonical_u32().to_le_bytes());
    write_m31_row(out, &deep.out_limbs);
    out.extend_from_slice(&deep.log_n.to_le_bytes());
    write_m31_row(out, &deep.zeta_limbs);
    out.extend_from_slice(&(deep.deep_stark.len() as u32).to_le_bytes());
    out.extend_from_slice(&deep.deep_stark);
}

fn decode_deep_ro(proof: &[u8], offset: usize) -> Option<(DeepRoStepProof, usize)> {
    let (sx_v, cursor) = read_m31_row(proof, offset, 1)?;
    let (sy_v, cursor) = read_m31_row(proof, cursor, 1)?;
    let (alpha_vec, cursor) = read_m31_row(proof, cursor, 3)?;
    let (px_vec, cursor) = read_m31_row(proof, cursor, 3)?;
    let mut pz_limbs = [[Mersenne31::ZERO; 3]; 3];
    let mut cursor = cursor;
    for pz in &mut pz_limbs {
        let (pz_vec, next) = read_m31_row(proof, cursor, 3)?;
        pz.copy_from_slice(&pz_vec);
        cursor = next;
    }
    let (lambda_vec, cursor) = read_m31_row(proof, cursor, 3)?;
    let (v_n_v, cursor) = read_m31_row(proof, cursor, 1)?;
    let (out_vec, cursor) = read_m31_row(proof, cursor, 3)?;
    let (log_n, cursor) = read_u32_le(proof, cursor)?;
    let (zeta_vec, cursor) = read_m31_row(proof, cursor, 3)?;
    let (stark_len, cursor) = read_u32_le(proof, cursor)?;
    let end = cursor + stark_len as usize;
    let deep_stark = proof.get(cursor..end)?.to_vec();
    let mut alpha_limbs = [Mersenne31::ZERO; 3];
    let mut px = [Mersenne31::ZERO; 3];
    let mut lambda_limbs = [Mersenne31::ZERO; 3];
    let mut out_limbs = [Mersenne31::ZERO; 3];
    let mut zeta_limbs = [Mersenne31::ZERO; 3];
    alpha_limbs.copy_from_slice(&alpha_vec);
    px.copy_from_slice(&px_vec);
    lambda_limbs.copy_from_slice(&lambda_vec);
    out_limbs.copy_from_slice(&out_vec);
    zeta_limbs.copy_from_slice(&zeta_vec);
    Some((
        DeepRoStepProof {
            sx: sx_v[0],
            sy: sy_v[0],
            alpha_limbs,
            px,
            pz_limbs,
            lambda_limbs,
            v_n: v_n_v[0],
            out_limbs,
            log_n,
            zeta_limbs,
            deep_stark,
        },
        end,
    ))
}

fn encode_deep_ros(out: &mut Vec<u8>, deeps: &[DeepRoStepProof]) {
    out.extend_from_slice(&(deeps.len() as u32).to_le_bytes());
    for d in deeps {
        encode_deep_ro(out, d);
    }
}

fn decode_deep_ros(
    proof: &[u8],
    offset: usize,
    max: usize,
) -> Option<(Vec<DeepRoStepProof>, usize)> {
    let (len, cursor) = read_u32_le(proof, offset)?;
    if len as usize == 0 || len as usize > max {
        return None;
    }
    let mut deeps = Vec::with_capacity(len as usize);
    let mut cursor = cursor;
    for _ in 0..len {
        let (d, next) = decode_deep_ro(proof, cursor)?;
        deeps.push(d);
        cursor = next;
    }
    Some((deeps, cursor))
}

fn encode_deep_ro_trace(out: &mut Vec<u8>, deep: &DeepRoTraceStepProof) {
    out.extend_from_slice(&deep.sx.as_canonical_u32().to_le_bytes());
    out.extend_from_slice(&deep.sy.as_canonical_u32().to_le_bytes());
    write_m31_row(out, &deep.alpha_limbs);
    write_m31_row(out, &deep.px);
    for pz in &deep.pz_local_limbs {
        write_m31_row(out, pz);
    }
    for pz in &deep.pz_next_limbs {
        write_m31_row(out, pz);
    }
    write_m31_row(out, &deep.lambda_limbs);
    out.extend_from_slice(&deep.v_n.as_canonical_u32().to_le_bytes());
    write_m31_row(out, &deep.out_limbs);
    out.extend_from_slice(&deep.log_n.to_le_bytes());
    write_m31_row(out, &deep.zeta_limbs);
    write_m31_row(out, &deep.zeta_next_limbs);
    out.extend_from_slice(&(deep.deep_stark.len() as u32).to_le_bytes());
    out.extend_from_slice(&deep.deep_stark);
}

fn decode_deep_ro_trace(proof: &[u8], offset: usize) -> Option<(DeepRoTraceStepProof, usize)> {
    let (sx_v, cursor) = read_m31_row(proof, offset, 1)?;
    let (sy_v, cursor) = read_m31_row(proof, cursor, 1)?;
    let (alpha_vec, cursor) = read_m31_row(proof, cursor, 3)?;
    let (px_vec, cursor) = read_m31_row(proof, cursor, AGG_WIDTH)?;
    let mut pz_local_limbs = [[Mersenne31::ZERO; 3]; AGG_WIDTH];
    let mut cursor = cursor;
    for pz in &mut pz_local_limbs {
        let (pz_vec, next) = read_m31_row(proof, cursor, 3)?;
        pz.copy_from_slice(&pz_vec);
        cursor = next;
    }
    let mut pz_next_limbs = [[Mersenne31::ZERO; 3]; AGG_WIDTH];
    for pz in &mut pz_next_limbs {
        let (pz_vec, next) = read_m31_row(proof, cursor, 3)?;
        pz.copy_from_slice(&pz_vec);
        cursor = next;
    }
    let (lambda_vec, cursor) = read_m31_row(proof, cursor, 3)?;
    let (v_n_v, cursor) = read_m31_row(proof, cursor, 1)?;
    let (out_vec, cursor) = read_m31_row(proof, cursor, 3)?;
    let (log_n, cursor) = read_u32_le(proof, cursor)?;
    let (zeta_vec, cursor) = read_m31_row(proof, cursor, 3)?;
    let (zeta_next_vec, cursor) = read_m31_row(proof, cursor, 3)?;
    let (stark_len, cursor) = read_u32_le(proof, cursor)?;
    let end = cursor + stark_len as usize;
    let deep_stark = proof.get(cursor..end)?.to_vec();
    let mut alpha_limbs = [Mersenne31::ZERO; 3];
    let mut px = [Mersenne31::ZERO; AGG_WIDTH];
    let mut lambda_limbs = [Mersenne31::ZERO; 3];
    let mut out_limbs = [Mersenne31::ZERO; 3];
    let mut zeta_limbs = [Mersenne31::ZERO; 3];
    let mut zeta_next_limbs = [Mersenne31::ZERO; 3];
    alpha_limbs.copy_from_slice(&alpha_vec);
    px.copy_from_slice(&px_vec);
    lambda_limbs.copy_from_slice(&lambda_vec);
    out_limbs.copy_from_slice(&out_vec);
    zeta_limbs.copy_from_slice(&zeta_vec);
    zeta_next_limbs.copy_from_slice(&zeta_next_vec);
    Some((
        DeepRoTraceStepProof {
            sx: sx_v[0],
            sy: sy_v[0],
            alpha_limbs,
            px,
            pz_local_limbs,
            pz_next_limbs,
            lambda_limbs,
            v_n: v_n_v[0],
            out_limbs,
            log_n,
            zeta_limbs,
            zeta_next_limbs,
            deep_stark,
        },
        end,
    ))
}

fn encode_deep_ro_traces(out: &mut Vec<u8>, deeps: &[DeepRoTraceStepProof]) {
    out.extend_from_slice(&(deeps.len() as u32).to_le_bytes());
    for d in deeps {
        encode_deep_ro_trace(out, d);
    }
}

fn decode_deep_ro_traces(
    proof: &[u8],
    offset: usize,
    max: usize,
) -> Option<(Vec<DeepRoTraceStepProof>, usize)> {
    let (len, cursor) = read_u32_le(proof, offset)?;
    if len as usize == 0 || len as usize > max {
        return None;
    }
    let mut deeps = Vec::with_capacity(len as usize);
    let mut cursor = cursor;
    for _ in 0..len {
        let (d, next) = decode_deep_ro_trace(proof, cursor)?;
        deeps.push(d);
        cursor = next;
    }
    Some((deeps, cursor))
}

fn encode_fri_mmcs_path(out: &mut Vec<u8>, path: &FriMmcsPathProof) {
    out.extend_from_slice(&path.depth.to_le_bytes());
    out.extend_from_slice(&path.leaf_width.to_le_bytes());
    out.extend_from_slice(&path.leaf_digest);
    out.extend_from_slice(&(path.layer_digests.len() as u32).to_le_bytes());
    for d in &path.layer_digests {
        out.extend_from_slice(d);
    }
    out.extend_from_slice(&(path.fold_stark.len() as u32).to_le_bytes());
    out.extend_from_slice(&path.fold_stark);
    encode_keccak256_stark(out, &path.leaf_keccak);
    out.extend_from_slice(&(path.compress_starks.len() as u32).to_le_bytes());
    for c in &path.compress_starks {
        encode_keccak256_stark(out, c);
    }
}

fn decode_fri_mmcs_path(proof: &[u8], offset: usize) -> Option<(FriMmcsPathProof, usize)> {
    let (depth, cursor) = read_u32_le(proof, offset)?;
    let (leaf_width, cursor) = read_u32_le(proof, cursor)?;
    let (leaf_digest, cursor) = read_fixed::<32>(proof, cursor)?;
    let (layer_len, cursor) = read_u32_le(proof, cursor)?;
    if layer_len as usize != depth as usize || depth == 0 || depth as usize > FRI_MMCS_MAX_DEPTH {
        return None;
    }
    let mut layer_digests = Vec::with_capacity(layer_len as usize);
    let mut cursor = cursor;
    for _ in 0..layer_len {
        let (d, next) = read_fixed::<32>(proof, cursor)?;
        layer_digests.push(d);
        cursor = next;
    }
    let (stark_len, cursor) = read_u32_le(proof, cursor)?;
    let end = cursor + stark_len as usize;
    let fold_stark = proof.get(cursor..end)?.to_vec();
    let (leaf_keccak, cursor) = decode_keccak256_stark(proof, end)?;
    let (comp_len, cursor) = read_u32_le(proof, cursor)?;
    if comp_len != layer_len {
        return None;
    }
    let mut compress_starks = Vec::with_capacity(comp_len as usize);
    let mut cursor = cursor;
    for _ in 0..comp_len {
        let (c, next) = decode_keccak256_stark(proof, cursor)?;
        compress_starks.push(c);
        cursor = next;
    }
    Some((
        FriMmcsPathProof {
            depth,
            leaf_width,
            leaf_digest,
            layer_digests,
            fold_stark,
            leaf_keccak,
            compress_starks,
        },
        cursor,
    ))
}

fn encode_siblings(out: &mut Vec<u8>, siblings: &[[u8; 32]]) {
    out.extend_from_slice(&(siblings.len() as u32).to_le_bytes());
    for s in siblings {
        out.extend_from_slice(s);
    }
}

fn decode_siblings(proof: &[u8], offset: usize, max: usize) -> Option<(Vec<[u8; 32]>, usize)> {
    let (len, cursor) = read_u32_le(proof, offset)?;
    if len as usize == 0 || len as usize > max {
        return None;
    }
    let mut siblings = Vec::with_capacity(len as usize);
    let mut cursor = cursor;
    for _ in 0..len {
        let (s, next) = read_fixed::<32>(proof, cursor)?;
        siblings.push(s);
        cursor = next;
    }
    Some((siblings, cursor))
}

fn encode_fri_val_mmcs_query(out: &mut Vec<u8>, q: &FriValMmcsQueryProof) {
    out.extend_from_slice(&q.trace_index.to_le_bytes());
    out.extend_from_slice(&q.quot_index.to_le_bytes());
    encode_siblings(out, &q.trace_siblings);
    encode_siblings(out, &q.quot_siblings);
    encode_fri_mmcs_path(out, &q.trace_path);
    encode_fri_mmcs_path(out, &q.quot_path);
}

fn decode_fri_val_mmcs_query(proof: &[u8], offset: usize) -> Option<(FriValMmcsQueryProof, usize)> {
    let (trace_index, cursor) = read_u32_le(proof, offset)?;
    let (quot_index, cursor) = read_u32_le(proof, cursor)?;
    let (trace_siblings, cursor) = decode_siblings(proof, cursor, FRI_MMCS_MAX_DEPTH)?;
    let (quot_siblings, cursor) = decode_siblings(proof, cursor, FRI_MMCS_MAX_DEPTH)?;
    let (trace_path, cursor) = decode_fri_mmcs_path(proof, cursor)?;
    let (quot_path, cursor) = decode_fri_mmcs_path(proof, cursor)?;
    Some((
        FriValMmcsQueryProof {
            trace_index,
            quot_index,
            trace_siblings,
            quot_siblings,
            trace_path,
            quot_path,
        },
        cursor,
    ))
}

fn encode_fri_val_mmcs(out: &mut Vec<u8>, qs: &[FriValMmcsQueryProof]) {
    out.extend_from_slice(&(qs.len() as u32).to_le_bytes());
    for q in qs {
        encode_fri_val_mmcs_query(out, q);
    }
}

fn decode_fri_val_mmcs(proof: &[u8], offset: usize) -> Option<(Vec<FriValMmcsQueryProof>, usize)> {
    let (len, cursor) = read_u32_le(proof, offset)?;
    if len as usize != AGG_FRI_PROVEN_QUERIES {
        return None;
    }
    let mut qs = Vec::with_capacity(len as usize);
    let mut cursor = cursor;
    for _ in 0..len {
        let (q, next) = decode_fri_val_mmcs_query(proof, cursor)?;
        qs.push(q);
        cursor = next;
    }
    Some((qs, cursor))
}

fn encode_chal_batch(out: &mut Vec<u8>, b: &FriChalBatchPathProof) {
    out.extend_from_slice(&b.index.to_le_bytes());
    encode_siblings(out, &b.siblings);
    out.extend_from_slice(&(b.leaf_rows.len() as u32).to_le_bytes());
    for row in &b.leaf_rows {
        out.extend_from_slice(&(row.len() as u32).to_le_bytes());
        write_m31_row(out, row);
    }
    out.extend_from_slice(&(b.leaf_keccs.len() as u32).to_le_bytes());
    for k in &b.leaf_keccs {
        encode_keccak256_stark(out, k);
    }
    out.extend_from_slice(&(b.leaf_digests.len() as u32).to_le_bytes());
    for d in &b.leaf_digests {
        out.extend_from_slice(d);
    }
    out.extend_from_slice(&(b.sib_compresses.len() as u32).to_le_bytes());
    for c in &b.sib_compresses {
        encode_keccak256_stark(out, c);
    }
    out.extend_from_slice(&(b.sib_layer_digests.len() as u32).to_le_bytes());
    for d in &b.sib_layer_digests {
        out.extend_from_slice(d);
    }
    out.extend_from_slice(&(b.inject_compresses.len() as u32).to_le_bytes());
    for c in &b.inject_compresses {
        encode_keccak256_stark(out, c);
    }
    out.extend_from_slice(&(b.inject_digests.len() as u32).to_le_bytes());
    for d in &b.inject_digests {
        out.extend_from_slice(d);
    }
    out.extend_from_slice(&(b.inject_leaf_indices.len() as u32).to_le_bytes());
    for i in &b.inject_leaf_indices {
        out.extend_from_slice(&i.to_le_bytes());
    }
}

fn decode_chal_batch(proof: &[u8], offset: usize) -> Option<(FriChalBatchPathProof, usize)> {
    let (index, cursor) = read_u32_le(proof, offset)?;
    let (siblings, cursor) = decode_siblings(proof, cursor, FRI_MMCS_MAX_DEPTH)?;
    let (n_rows, cursor) = read_u32_le(proof, cursor)?;
    if n_rows == 0 || n_rows as usize > 8 {
        return None;
    }
    let mut leaf_rows = Vec::with_capacity(n_rows as usize);
    let mut cursor = cursor;
    for _ in 0..n_rows {
        let (w, next) = read_u32_le(proof, cursor)?;
        if w == 0 || w as usize > AGG_WIDTH * 2 {
            return None;
        }
        let (row, next) = read_m31_row(proof, next, w as usize)?;
        leaf_rows.push(row);
        cursor = next;
    }
    let (n_keccs, cursor) = read_u32_le(proof, cursor)?;
    if n_keccs as usize != leaf_rows.len() {
        return None;
    }
    let mut leaf_keccs = Vec::with_capacity(n_keccs as usize);
    let mut cursor = cursor;
    for _ in 0..n_keccs {
        let (k, next) = decode_keccak256_stark(proof, cursor)?;
        leaf_keccs.push(k);
        cursor = next;
    }
    let (n_dig, cursor) = read_u32_le(proof, cursor)?;
    if n_dig as usize != leaf_rows.len() {
        return None;
    }
    let mut leaf_digests = Vec::with_capacity(n_dig as usize);
    let mut cursor = cursor;
    for _ in 0..n_dig {
        let (d, next) = read_fixed::<32>(proof, cursor)?;
        leaf_digests.push(d);
        cursor = next;
    }
    let (n_sib_c, cursor) = read_u32_le(proof, cursor)?;
    if n_sib_c as usize != siblings.len() || n_sib_c as usize > FRI_MMCS_MAX_DEPTH {
        return None;
    }
    let mut sib_compresses = Vec::with_capacity(n_sib_c as usize);
    let mut cursor = cursor;
    for _ in 0..n_sib_c {
        let (c, next) = decode_keccak256_stark(proof, cursor)?;
        sib_compresses.push(c);
        cursor = next;
    }
    let (n_sib_d, cursor) = read_u32_le(proof, cursor)?;
    if n_sib_d != n_sib_c {
        return None;
    }
    let mut sib_layer_digests = Vec::with_capacity(n_sib_d as usize);
    let mut cursor = cursor;
    for _ in 0..n_sib_d {
        let (d, next) = read_fixed::<32>(proof, cursor)?;
        sib_layer_digests.push(d);
        cursor = next;
    }
    let (n_inj_c, cursor) = read_u32_le(proof, cursor)?;
    if n_inj_c as usize > FRI_MMCS_MAX_DEPTH {
        return None;
    }
    let mut inject_compresses = Vec::with_capacity(n_inj_c as usize);
    let mut cursor = cursor;
    for _ in 0..n_inj_c {
        let (c, next) = decode_keccak256_stark(proof, cursor)?;
        inject_compresses.push(c);
        cursor = next;
    }
    let (n_inj_d, cursor) = read_u32_le(proof, cursor)?;
    if n_inj_d != n_inj_c {
        return None;
    }
    let mut inject_digests = Vec::with_capacity(n_inj_d as usize);
    let mut cursor = cursor;
    for _ in 0..n_inj_d {
        let (d, next) = read_fixed::<32>(proof, cursor)?;
        inject_digests.push(d);
        cursor = next;
    }
    let (n_inj_i, cursor) = read_u32_le(proof, cursor)?;
    if n_inj_i != n_inj_c {
        return None;
    }
    let mut inject_leaf_indices = Vec::with_capacity(n_inj_i as usize);
    let mut cursor = cursor;
    for _ in 0..n_inj_i {
        let (i, next) = read_u32_le(proof, cursor)?;
        inject_leaf_indices.push(i);
        cursor = next;
    }
    Some((
        FriChalBatchPathProof {
            index,
            siblings,
            leaf_rows,
            leaf_keccs,
            leaf_digests,
            sib_compresses,
            sib_layer_digests,
            inject_compresses,
            inject_digests,
            inject_leaf_indices,
        },
        cursor,
    ))
}

fn encode_fri_chal_mmcs_query(out: &mut Vec<u8>, q: &FriChalMmcsQueryProof) {
    encode_chal_batch(out, &q.first_layer);
    out.extend_from_slice(&(q.commit_indices.len() as u32).to_le_bytes());
    for i in &q.commit_indices {
        out.extend_from_slice(&i.to_le_bytes());
    }
    out.extend_from_slice(&(q.commit_siblings.len() as u32).to_le_bytes());
    for sibs in &q.commit_siblings {
        encode_siblings(out, sibs);
    }
    out.extend_from_slice(&(q.commit_paths.len() as u32).to_le_bytes());
    for p in &q.commit_paths {
        encode_fri_mmcs_path(out, p);
    }
}

fn decode_fri_chal_mmcs_query(
    proof: &[u8],
    offset: usize,
) -> Option<(FriChalMmcsQueryProof, usize)> {
    let (first_layer, cursor) = decode_chal_batch(proof, offset)?;
    let (n_idx, cursor) = read_u32_le(proof, cursor)?;
    if n_idx as usize > AGG_FRI_MAX_ROUNDS {
        return None;
    }
    let mut commit_indices = Vec::with_capacity(n_idx as usize);
    let mut cursor = cursor;
    for _ in 0..n_idx {
        let (i, next) = read_u32_le(proof, cursor)?;
        commit_indices.push(i);
        cursor = next;
    }
    let (n_sib, cursor) = read_u32_le(proof, cursor)?;
    if n_sib != n_idx {
        return None;
    }
    let mut commit_siblings = Vec::with_capacity(n_sib as usize);
    let mut cursor = cursor;
    for _ in 0..n_sib {
        let (s, next) = decode_siblings(proof, cursor, FRI_MMCS_MAX_DEPTH)?;
        commit_siblings.push(s);
        cursor = next;
    }
    let (n_paths, cursor) = read_u32_le(proof, cursor)?;
    if n_paths != n_idx {
        return None;
    }
    let mut commit_paths = Vec::with_capacity(n_paths as usize);
    let mut cursor = cursor;
    for _ in 0..n_paths {
        let (p, next) = decode_fri_mmcs_path(proof, cursor)?;
        commit_paths.push(p);
        cursor = next;
    }
    Some((
        FriChalMmcsQueryProof {
            first_layer,
            commit_indices,
            commit_siblings,
            commit_paths,
        },
        cursor,
    ))
}

fn encode_fri_chal_mmcs(out: &mut Vec<u8>, qs: &[FriChalMmcsQueryProof]) {
    out.extend_from_slice(&(qs.len() as u32).to_le_bytes());
    for q in qs {
        encode_fri_chal_mmcs_query(out, q);
    }
}

fn decode_fri_chal_mmcs(
    proof: &[u8],
    offset: usize,
) -> Option<(Vec<FriChalMmcsQueryProof>, usize)> {
    let (len, cursor) = read_u32_le(proof, offset)?;
    if len as usize != AGG_FRI_PROVEN_QUERIES {
        return None;
    }
    let mut qs = Vec::with_capacity(len as usize);
    let mut cursor = cursor;
    for _ in 0..len {
        let (q, next) = decode_fri_chal_mmcs_query(proof, cursor)?;
        qs.push(q);
        cursor = next;
    }
    Some((qs, cursor))
}

fn encode_cert(out: &mut Vec<u8>, cert: &Option<AggPcsCertificate>) {
    match cert {
        None => out.push(0),
        Some(c) => {
            out.push(1);
            out.extend_from_slice(&c.stmt_left_hash);
            out.extend_from_slice(&c.stmt_right_hash);
            out.extend_from_slice(&c.trace_commitment);
            write_m31_row(out, &c.natural_row);
            out.extend_from_slice(&c.lde_index.to_le_bytes());
            out.extend_from_slice(&(c.lde_row.len() as u32).to_le_bytes());
            write_m31_row(out, &c.lde_row);
            out.extend_from_slice(&(c.siblings.len() as u32).to_le_bytes());
            for sib in &c.siblings {
                out.extend_from_slice(sib);
            }
            encode_merkle_fold(out, &c.merkle_fold);
            encode_fri_folds(out, &c.fri_fold_ys);
            encode_fri_folds(out, &c.fri_folds);
            encode_deep_ros(out, &c.deep_ros);
            encode_deep_ro_traces(out, &c.deep_ro_traces);
            encode_fri_val_mmcs(out, &c.fri_val_mmcs);
            encode_fri_chal_mmcs(out, &c.fri_chal_mmcs);
        }
    }
}

fn decode_cert(proof: &[u8], offset: usize) -> Option<(Option<AggPcsCertificate>, usize)> {
    let flag = *proof.get(offset)?;
    let cursor = offset + 1;
    if flag == 0 {
        return Some((None, cursor));
    }
    if flag != 1 {
        return None;
    }
    let (stmt_left_hash, cursor) = read_fixed::<{ CHILD_HASH_LEN }>(proof, cursor)?;
    let (stmt_right_hash, cursor) = read_fixed::<{ CHILD_HASH_LEN }>(proof, cursor)?;
    let (trace_commitment, cursor) = read_fixed::<32>(proof, cursor)?;
    let (natural_vec, cursor) = read_m31_row(proof, cursor, AGG_WIDTH)?;
    let mut natural_row = [Mersenne31::ZERO; AGG_WIDTH];
    natural_row.copy_from_slice(&natural_vec);
    let (lde_index, cursor) = read_u32_le(proof, cursor)?;
    let (lde_len, cursor) = read_u32_le(proof, cursor)?;
    if lde_len as usize != AGG_WIDTH {
        return None;
    }
    let (lde_row, cursor) = read_m31_row(proof, cursor, lde_len as usize)?;
    let (sib_len, cursor) = read_u32_le(proof, cursor)?;
    if sib_len as usize > AGG_PCS_MAX_SIBLINGS {
        return None;
    }
    let mut siblings = Vec::with_capacity(sib_len as usize);
    let mut cursor = cursor;
    for _ in 0..sib_len {
        let (sib, next) = read_fixed::<32>(proof, cursor)?;
        siblings.push(sib);
        cursor = next;
    }
    let (merkle_fold, cursor) = decode_merkle_fold(proof, cursor)?;
    let (fri_fold_ys, cursor) = decode_fri_folds(proof, cursor, AGG_FRI_MAX_FOLD_YS)?;
    let (fri_folds, cursor) =
        decode_fri_folds(proof, cursor, AGG_FRI_MAX_ROUNDS * AGG_FRI_PROVEN_QUERIES)?;
    let (deep_ros, cursor) = decode_deep_ros(proof, cursor, AGG_DEEP_RO_MAX)?;
    let (deep_ro_traces, cursor) = decode_deep_ro_traces(proof, cursor, AGG_DEEP_RO_TRACE_MAX)?;
    let (fri_val_mmcs, cursor) = decode_fri_val_mmcs(proof, cursor)?;
    let (fri_chal_mmcs, cursor) = decode_fri_chal_mmcs(proof, cursor)?;
    Some((
        Some(AggPcsCertificate {
            stmt_left_hash,
            stmt_right_hash,
            trace_commitment,
            natural_row,
            lde_index,
            lde_row,
            siblings,
            merkle_fold,
            fri_fold_ys,
            fri_folds,
            deep_ros,
            deep_ro_traces,
            fri_val_mmcs,
            fri_chal_mmcs,
        }),
        cursor,
    ))
}

fn locate_inner_marker(proof: &[u8]) -> Option<usize> {
    let pos = proof
        .windows(V6_REC_AGG_INNER_MARKER.len())
        .position(|w| w == V6_REC_AGG_INNER_MARKER)?;
    let prefix = &proof[..pos];
    if prefix.is_empty() || prefix.last() != Some(&0) {
        return None;
    }
    Some(pos)
}

pub fn encode_rec_agg_proof_v6(
    context: &RecursiveAggregationContext<'_>,
    plonky3_bytes: &[u8],
) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(context.parent_task_id.as_bytes());
    out.push(0);
    out.extend_from_slice(V6_REC_AGG_INNER_MARKER);
    out.extend_from_slice(context.compose_label.as_bytes());
    out.push(0);
    out.extend_from_slice(context.manifest_root_hash.as_bytes());
    out.push(0);
    out.extend_from_slice(&context.left_child_hash);
    out.extend_from_slice(&context.right_child_hash);
    out.extend_from_slice(&context.left_stark_digest);
    out.extend_from_slice(&context.right_stark_digest);
    out.push(context.left_kind);
    out.push(context.right_kind);
    encode_cert(&mut out, &context.left_agg_cert);
    encode_cert(&mut out, &context.right_agg_cert);
    out.extend_from_slice(&(plonky3_bytes.len() as u32).to_le_bytes());
    out.extend_from_slice(plonky3_bytes);
    out
}

pub fn decode_rec_agg_proof_owned_v6(
    proof: &[u8],
    expected: &RecursiveAggregationContext<'_>,
) -> Option<Vec<u8>> {
    if !proof.starts_with(expected.parent_task_id.as_bytes()) {
        return None;
    }
    let marker_pos = locate_inner_marker(proof)?;
    let parent_end = marker_pos.saturating_sub(1);
    let parent_task_id = std::str::from_utf8(&proof[..parent_end]).ok()?;
    if parent_task_id != expected.parent_task_id {
        return None;
    }

    let cursor = marker_pos + V6_REC_AGG_INNER_MARKER.len();
    let (compose_label, cursor) = read_cstr(proof, cursor)?;
    let (manifest_root_hash, cursor) = read_cstr(proof, cursor)?;
    let (left_hash, cursor) = read_fixed::<{ CHILD_HASH_LEN }>(proof, cursor)?;
    let (right_hash, cursor) = read_fixed::<{ CHILD_HASH_LEN }>(proof, cursor)?;
    let (left_stark, cursor) = read_fixed::<{ STARK_DIGEST_LEN }>(proof, cursor)?;
    let (right_stark, cursor) = read_fixed::<{ STARK_DIGEST_LEN }>(proof, cursor)?;
    let left_kind = *proof.get(cursor)?;
    let right_kind = *proof.get(cursor + 1)?;
    let cursor = cursor + 2;
    let (left_cert, cursor) = decode_cert(proof, cursor)?;
    let (right_cert, cursor) = decode_cert(proof, cursor)?;

    if compose_label != expected.compose_label
        || manifest_root_hash != expected.manifest_root_hash
        || left_hash != expected.left_child_hash
        || right_hash != expected.right_child_hash
        || left_stark != expected.left_stark_digest
        || right_stark != expected.right_stark_digest
        || left_kind != expected.left_kind
        || right_kind != expected.right_kind
        || left_cert != expected.left_agg_cert
        || right_cert != expected.right_agg_cert
    {
        return None;
    }
    if left_kind > REC_KIND_AGG || right_kind > REC_KIND_AGG {
        return None;
    }
    if left_kind == REC_KIND_LEAF && left_cert.is_some() {
        return None;
    }
    if right_kind == REC_KIND_LEAF && right_cert.is_some() {
        return None;
    }
    if left_kind == REC_KIND_AGG && left_cert.is_none() {
        return None;
    }
    if right_kind == REC_KIND_AGG && right_cert.is_none() {
        return None;
    }

    let (len, cursor) = read_u32_le(proof, cursor)?;
    let end = cursor + len as usize;
    let payload = proof.get(cursor..end)?.to_vec();
    if end != proof.len() {
        return None;
    }
    Some(payload)
}

pub fn append_rec_tail_v6(mut body: Vec<u8>, rec_proof: &[u8]) -> Vec<u8> {
    body.extend_from_slice(V6_REC_TAIL_MARKER);
    body.extend_from_slice(&(rec_proof.len() as u32).to_le_bytes());
    body.extend_from_slice(rec_proof);
    body
}

pub fn split_rec_tail_v6(proof: &[u8]) -> Option<(&[u8], &[u8])> {
    let pos = proof
        .windows(V6_REC_TAIL_MARKER.len())
        .rposition(|w| w == V6_REC_TAIL_MARKER)?;
    let body = &proof[..pos];
    let cursor = pos + V6_REC_TAIL_MARKER.len();
    let (len, cursor) = read_u32_le(proof, cursor)?;
    let end = cursor + len as usize;
    let rec = proof.get(cursor..end)?;
    if end != proof.len() {
        return None;
    }
    Some((body, rec))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rec_tail_v6_roundtrip() {
        let body = b"v3-bytes";
        let rec = b"rec-proof";
        let combined = append_rec_tail_v6(body.to_vec(), rec);
        let (left, right) = split_rec_tail_v6(&combined).expect("split");
        assert_eq!(left, body);
        assert_eq!(right, rec);
    }
}

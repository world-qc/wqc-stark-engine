//! V6 recursive aggregation transcript (R3-M2 … M3e / M4c): M1 fields +
//! AggregationAir PCS certs or leaf PCS bundles (M4c Mmcs group folds + FriFold + DeepRo + residual batch Mmcs).

use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_mersenne_31::Mersenne31;

use crate::aggregation::CHILD_HASH_LEN;
use crate::plonky3_stark::aggregation_air::AGG_WIDTH;

use super::air::{REC_KIND_AGG, REC_KIND_LEAF};
use super::context::RecursiveAggregationContext;
use super::deep_ro_air::DeepRoStepProof;
use super::deep_ro_bind::{AGG_DEEP_RO_MAX, AGG_DEEP_RO_TRACE_MAX};
use super::deep_ro_leaf_trace_air::DeepRoLeafTraceStepProof;
use super::deep_ro_trace_air::DeepRoTraceStepProof;
use super::fri_fold_air::FriFoldStepProof;
use super::fri_fold_bind::{
    AGG_FRI_MAX_FOLD_YS, AGG_FRI_MAX_ROUNDS, AGG_FRI_PROVEN_QUERIES, LEAF_FRI_MAX_ROUNDS,
    LEAF_FRI_PROVEN_QUERIES,
};
use super::fri_fold_group::{FriFoldGroupProof, FRI_FOLD_GROUP_MAX_STEPS};
use super::fri_fold_m4c::{LeafFriFoldGroups, LEAF_FRI_FOLD_V};
use super::fri_mmcs_bind::{FriChalBatchPathProof, FriChalMmcsQueryProof, FriValMmcsQueryProof};
use super::fri_mmcs_group_m4b::KeccakGroupFoldProof;
use super::fri_mmcs_m4c::{LeafMmcsFoldGroups, LEAF_MMCS_FOLD_V};
use super::fri_mmcs_path::{FriMmcsPathProof, FRI_MMCS_MAX_DEPTH};
use super::keccak256_air::Keccak256StarkProof;
use super::leaf_pcs_cert::{LeafPcsBundle, LeafPcsCertificate};
use super::ood_air::{OodAirKind, OodStepProof, OOD_MAX_TRACE_WIDTH};
use super::opening_cert::{AggPcsCertificate, AGG_PCS_MAX_SIBLINGS, LEAF_PCS_MAX_SIBLINGS};
use super::pcs_geom::{LeafKind, LEAF_DEEP_RO_MAX_WIDTH, MAX_QUOT_BATCH_LEAF_ROWS};
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

fn encode_ood(out: &mut Vec<u8>, ood: &OodStepProof) {
    out.push(ood.kind as u8);
    out.extend_from_slice(&ood.num_outcomes.to_le_bytes());
    out.extend_from_slice(&ood.width.to_le_bytes());
    out.extend_from_slice(&ood.degree_bits.to_le_bytes());
    write_m31_row(out, &ood.zeta_limbs);
    write_m31_row(out, &ood.alpha_limbs);
    write_m31_row(out, &ood.quotient_limbs);
    write_m31_row(out, &ood.inv_vanishing_limbs);
    write_m31_row(out, &ood.is_first_row_limbs);
    write_m31_row(out, &ood.is_last_row_limbs);
    write_m31_row(out, &ood.is_transition_limbs);
    write_m31_row(out, &ood.folded_limbs);
    out.extend_from_slice(&(ood.trace_local_limbs.len() as u32).to_le_bytes());
    for limbs in &ood.trace_local_limbs {
        write_m31_row(out, limbs);
    }
    out.extend_from_slice(&(ood.trace_next_limbs.len() as u32).to_le_bytes());
    for limbs in &ood.trace_next_limbs {
        write_m31_row(out, limbs);
    }
    out.extend_from_slice(&(ood.ood_stark.len() as u32).to_le_bytes());
    out.extend_from_slice(&ood.ood_stark);
}

fn decode_ood(proof: &[u8], offset: usize) -> Option<(OodStepProof, usize)> {
    let kind = OodAirKind::from_u8(*proof.get(offset)?)?;
    let cursor = offset + 1;
    let (num_outcomes, cursor) = read_u32_le(proof, cursor)?;
    let (width, cursor) = read_u32_le(proof, cursor)?;
    let (degree_bits, cursor) = read_u32_le(proof, cursor)?;
    if width as usize > OOD_MAX_TRACE_WIDTH {
        return None;
    }
    let (zeta_vec, cursor) = read_m31_row(proof, cursor, 3)?;
    let (alpha_vec, cursor) = read_m31_row(proof, cursor, 3)?;
    let (quotient_vec, cursor) = read_m31_row(proof, cursor, 3)?;
    let (inv_vec, cursor) = read_m31_row(proof, cursor, 3)?;
    let (first_vec, cursor) = read_m31_row(proof, cursor, 3)?;
    let (last_vec, cursor) = read_m31_row(proof, cursor, 3)?;
    let (trans_vec, cursor) = read_m31_row(proof, cursor, 3)?;
    let (folded_vec, cursor) = read_m31_row(proof, cursor, 3)?;
    let (local_len, cursor) = read_u32_le(proof, cursor)?;
    if local_len as usize > OOD_MAX_TRACE_WIDTH {
        return None;
    }
    let mut trace_local_limbs = Vec::with_capacity(local_len as usize);
    let mut cursor = cursor;
    for _ in 0..local_len {
        let (row, next) = read_m31_row(proof, cursor, 3)?;
        let mut limbs = [Mersenne31::ZERO; 3];
        limbs.copy_from_slice(&row);
        trace_local_limbs.push(limbs);
        cursor = next;
    }
    let (next_len, cursor) = read_u32_le(proof, cursor)?;
    if next_len != local_len || next_len as usize > OOD_MAX_TRACE_WIDTH {
        return None;
    }
    let mut trace_next_limbs = Vec::with_capacity(next_len as usize);
    let mut cursor = cursor;
    for _ in 0..next_len {
        let (row, next) = read_m31_row(proof, cursor, 3)?;
        let mut limbs = [Mersenne31::ZERO; 3];
        limbs.copy_from_slice(&row);
        trace_next_limbs.push(limbs);
        cursor = next;
    }
    let (stark_len, cursor) = read_u32_le(proof, cursor)?;
    let end = cursor + stark_len as usize;
    let ood_stark = proof.get(cursor..end)?.to_vec();
    let mut zeta_limbs = [Mersenne31::ZERO; 3];
    let mut alpha_limbs = [Mersenne31::ZERO; 3];
    let mut quotient_limbs = [Mersenne31::ZERO; 3];
    let mut inv_vanishing_limbs = [Mersenne31::ZERO; 3];
    let mut is_first_row_limbs = [Mersenne31::ZERO; 3];
    let mut is_last_row_limbs = [Mersenne31::ZERO; 3];
    let mut is_transition_limbs = [Mersenne31::ZERO; 3];
    let mut folded_limbs = [Mersenne31::ZERO; 3];
    zeta_limbs.copy_from_slice(&zeta_vec);
    alpha_limbs.copy_from_slice(&alpha_vec);
    quotient_limbs.copy_from_slice(&quotient_vec);
    inv_vanishing_limbs.copy_from_slice(&inv_vec);
    is_first_row_limbs.copy_from_slice(&first_vec);
    is_last_row_limbs.copy_from_slice(&last_vec);
    is_transition_limbs.copy_from_slice(&trans_vec);
    folded_limbs.copy_from_slice(&folded_vec);
    Some((
        OodStepProof {
            kind,
            num_outcomes,
            width,
            degree_bits,
            zeta_limbs,
            alpha_limbs,
            quotient_limbs,
            inv_vanishing_limbs,
            is_first_row_limbs,
            is_last_row_limbs,
            is_transition_limbs,
            folded_limbs,
            trace_local_limbs,
            trace_next_limbs,
            ood_stark,
        },
        end,
    ))
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

fn encode_keccak_group_fold(out: &mut Vec<u8>, g: &KeccakGroupFoldProof) {
    out.extend_from_slice(&g.path_count.to_le_bytes());
    out.extend_from_slice(&g.depth.to_le_bytes());
    out.extend_from_slice(&g.leaf_width.to_le_bytes());
    out.extend_from_slice(&(g.leaf_digests.len() as u32).to_le_bytes());
    for d in &g.leaf_digests {
        out.extend_from_slice(d);
    }
    out.extend_from_slice(&(g.layer_digests.len() as u32).to_le_bytes());
    for layers in &g.layer_digests {
        out.extend_from_slice(&(layers.len() as u32).to_le_bytes());
        for d in layers {
            out.extend_from_slice(d);
        }
    }
    out.extend_from_slice(&(g.group_stark.len() as u32).to_le_bytes());
    out.extend_from_slice(&g.group_stark);
}

fn decode_keccak_group_fold(proof: &[u8], offset: usize) -> Option<(KeccakGroupFoldProof, usize)> {
    let (path_count, cursor) = read_u32_le(proof, offset)?;
    let (depth, cursor) = read_u32_le(proof, cursor)?;
    let (leaf_width, cursor) = read_u32_le(proof, cursor)?;
    if path_count == 0 || depth == 0 || depth as usize > FRI_MMCS_MAX_DEPTH {
        return None;
    }
    let (digest_len, cursor) = read_u32_le(proof, cursor)?;
    if digest_len != path_count {
        return None;
    }
    let mut leaf_digests = Vec::with_capacity(digest_len as usize);
    let mut cursor = cursor;
    for _ in 0..digest_len {
        let (d, next) = read_fixed::<32>(proof, cursor)?;
        leaf_digests.push(d);
        cursor = next;
    }
    let (layer_outer, cursor) = read_u32_le(proof, cursor)?;
    if layer_outer != path_count {
        return None;
    }
    let mut layer_digests = Vec::with_capacity(layer_outer as usize);
    let mut cursor = cursor;
    for _ in 0..layer_outer {
        let (inner_len, next) = read_u32_le(proof, cursor)?;
        if inner_len != depth {
            return None;
        }
        let mut layers = Vec::with_capacity(inner_len as usize);
        let mut next = next;
        for _ in 0..inner_len {
            let (d, n) = read_fixed::<32>(proof, next)?;
            layers.push(d);
            next = n;
        }
        layer_digests.push(layers);
        cursor = next;
    }
    let (stark_len, cursor) = read_u32_le(proof, cursor)?;
    let end = cursor + stark_len as usize;
    let group_stark = proof.get(cursor..end)?.to_vec();
    Some((
        KeccakGroupFoldProof {
            path_count,
            depth,
            leaf_width,
            leaf_digests,
            layer_digests,
            group_stark,
        },
        end,
    ))
}

/// Upper bound on chunked group STARKs per single-height category (v3).
/// Each chunk has `path_count >= 1`, and a category folds at most
/// `LEAF_FRI_PROVEN_QUERIES` paths (one per proven FRI query).
const MAX_GROUPS_SINGLE: usize = LEAF_FRI_PROVEN_QUERIES;
/// Upper bound for the depth-keyed commit category (up to one group set per depth).
const MAX_GROUPS_COMMIT: usize = FRI_MMCS_MAX_DEPTH * LEAF_FRI_PROVEN_QUERIES;

fn encode_group_vec(out: &mut Vec<u8>, groups: &[KeccakGroupFoldProof]) {
    out.extend_from_slice(&(groups.len() as u32).to_le_bytes());
    for g in groups {
        encode_keccak_group_fold(out, g);
    }
}

fn decode_group_vec(
    proof: &[u8],
    offset: usize,
    max_count: usize,
) -> Option<(Vec<KeccakGroupFoldProof>, usize)> {
    let (len, mut cursor) = read_u32_le(proof, offset)?;
    if len as usize > max_count {
        return None;
    }
    let mut groups = Vec::with_capacity(len as usize);
    for _ in 0..len {
        let (g, next) = decode_keccak_group_fold(proof, cursor)?;
        groups.push(g);
        cursor = next;
    }
    Some((groups, cursor))
}

fn encode_mmcs_groups(out: &mut Vec<u8>, groups: &LeafMmcsFoldGroups) {
    encode_group_vec(out, &groups.val_trace);
    encode_group_vec(out, &groups.val_quot);
    encode_group_vec(out, &groups.val_quot_batch);
    encode_group_vec(out, &groups.chal_first_layer);
    encode_group_vec(out, &groups.chal_commit);
}

fn decode_mmcs_groups(proof: &[u8], offset: usize) -> Option<(LeafMmcsFoldGroups, usize)> {
    let (val_trace, cursor) = decode_group_vec(proof, offset, MAX_GROUPS_SINGLE)?;
    let (val_quot, cursor) = decode_group_vec(proof, cursor, MAX_GROUPS_SINGLE)?;
    let (val_quot_batch, cursor) = decode_group_vec(proof, cursor, MAX_GROUPS_SINGLE)?;
    let (chal_first_layer, cursor) = decode_group_vec(proof, cursor, MAX_GROUPS_SINGLE)?;
    let (chal_commit, cursor) = decode_group_vec(proof, cursor, MAX_GROUPS_COMMIT)?;
    Some((
        LeafMmcsFoldGroups {
            val_trace,
            val_quot,
            val_quot_batch,
            chal_first_layer,
            chal_commit,
        },
        cursor,
    ))
}

fn encode_fri_fold_group(out: &mut Vec<u8>, g: &FriFoldGroupProof) {
    out.push(g.kind);
    out.extend_from_slice(&g.step_count.to_le_bytes());
    out.extend_from_slice(&g.log_folded_height.to_le_bytes());
    out.extend_from_slice(&(g.group_stark.len() as u32).to_le_bytes());
    out.extend_from_slice(&g.group_stark);
}

fn decode_fri_fold_group(proof: &[u8], offset: usize) -> Option<(FriFoldGroupProof, usize)> {
    let kind = *proof.get(offset)?;
    let (step_count, cursor) = read_u32_le(proof, offset + 1)?;
    if step_count == 0 || step_count as usize > FRI_FOLD_GROUP_MAX_STEPS {
        return None;
    }
    let (log_folded_height, cursor) = read_u32_le(proof, cursor)?;
    let (stark_len, cursor) = read_u32_le(proof, cursor)?;
    let end = cursor + stark_len as usize;
    let group_stark = proof.get(cursor..end)?.to_vec();
    Some((
        FriFoldGroupProof {
            kind,
            step_count,
            log_folded_height,
            group_stark,
        },
        end,
    ))
}

fn encode_opt_fri_fold_group(out: &mut Vec<u8>, g: &Option<FriFoldGroupProof>) {
    match g {
        Some(g) => {
            out.push(1);
            encode_fri_fold_group(out, g);
        }
        None => out.push(0),
    }
}

fn decode_opt_fri_fold_group(
    proof: &[u8],
    offset: usize,
) -> Option<(Option<FriFoldGroupProof>, usize)> {
    let flag = *proof.get(offset)?;
    let cursor = offset + 1;
    match flag {
        0 => Some((None, cursor)),
        1 => {
            let (g, cursor) = decode_fri_fold_group(proof, cursor)?;
            Some((Some(g), cursor))
        }
        _ => None,
    }
}

fn encode_fri_fold_groups(out: &mut Vec<u8>, groups: &LeafFriFoldGroups) {
    encode_opt_fri_fold_group(out, &groups.fold_ys);
    out.extend_from_slice(&(groups.fold_xs_by_log_h.len() as u32).to_le_bytes());
    for g in &groups.fold_xs_by_log_h {
        encode_fri_fold_group(out, g);
    }
}

fn decode_fri_fold_groups(proof: &[u8], offset: usize) -> Option<(LeafFriFoldGroups, usize)> {
    let (fold_ys, cursor) = decode_opt_fri_fold_group(proof, offset)?;
    let (xs_len, cursor) = read_u32_le(proof, cursor)?;
    if xs_len as usize > LEAF_FRI_MAX_ROUNDS {
        return None;
    }
    let mut fold_xs_by_log_h = Vec::with_capacity(xs_len as usize);
    let mut cursor = cursor;
    for _ in 0..xs_len {
        let (g, next) = decode_fri_fold_group(proof, cursor)?;
        fold_xs_by_log_h.push(g);
        cursor = next;
    }
    Some((
        LeafFriFoldGroups {
            fold_ys,
            fold_xs_by_log_h,
        },
        cursor,
    ))
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
    if len as usize > max {
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
    match &q.quot_batch {
        Some(batch) => {
            out.push(1);
            encode_chal_batch(out, batch);
        }
        None => out.push(0),
    }
}

fn decode_fri_val_mmcs_query(proof: &[u8], offset: usize) -> Option<(FriValMmcsQueryProof, usize)> {
    let (trace_index, cursor) = read_u32_le(proof, offset)?;
    let (quot_index, cursor) = read_u32_le(proof, cursor)?;
    let (trace_siblings, cursor) = decode_siblings(proof, cursor, FRI_MMCS_MAX_DEPTH)?;
    let (quot_siblings, cursor) = decode_siblings(proof, cursor, FRI_MMCS_MAX_DEPTH)?;
    let (trace_path, cursor) = decode_fri_mmcs_path(proof, cursor)?;
    let (quot_path, cursor) = decode_fri_mmcs_path(proof, cursor)?;
    let has_quot_batch = *proof.get(cursor)?;
    let cursor = cursor + 1;
    let (quot_batch, cursor) = match has_quot_batch {
        0 => (None, cursor),
        1 => {
            let (batch, cursor) = decode_chal_batch(proof, cursor)?;
            (Some(batch), cursor)
        }
        _ => return None,
    };
    Some((
        FriValMmcsQueryProof {
            trace_index,
            quot_index,
            trace_siblings,
            quot_siblings,
            trace_path,
            quot_path,
            quot_batch,
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
    if n_rows == 0 || n_rows as usize > MAX_QUOT_BATCH_LEAF_ROWS {
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

fn encode_deep_ro_leaf_trace(out: &mut Vec<u8>, deep: &DeepRoLeafTraceStepProof) {
    out.extend_from_slice(&deep.sx.as_canonical_u32().to_le_bytes());
    out.extend_from_slice(&deep.sy.as_canonical_u32().to_le_bytes());
    write_m31_row(out, &deep.alpha_limbs);
    out.extend_from_slice(&deep.width.to_le_bytes());
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

fn decode_deep_ro_leaf_trace(
    proof: &[u8],
    offset: usize,
) -> Option<(DeepRoLeafTraceStepProof, usize)> {
    let (sx_v, cursor) = read_m31_row(proof, offset, 1)?;
    let (sy_v, cursor) = read_m31_row(proof, cursor, 1)?;
    let (alpha_vec, cursor) = read_m31_row(proof, cursor, 3)?;
    let (width, cursor) = read_u32_le(proof, cursor)?;
    if width == 0 || width as usize > LEAF_DEEP_RO_MAX_WIDTH {
        return None;
    }
    let w = width as usize;
    let (px_vec, cursor) = read_m31_row(proof, cursor, w)?;
    let mut pz_local_limbs = Vec::with_capacity(w);
    let mut cursor = cursor;
    for _ in 0..w {
        let (pz_vec, next) = read_m31_row(proof, cursor, 3)?;
        let mut pz = [Mersenne31::ZERO; 3];
        pz.copy_from_slice(&pz_vec);
        pz_local_limbs.push(pz);
        cursor = next;
    }
    let mut pz_next_limbs = Vec::with_capacity(w);
    for _ in 0..w {
        let (pz_vec, next) = read_m31_row(proof, cursor, 3)?;
        let mut pz = [Mersenne31::ZERO; 3];
        pz.copy_from_slice(&pz_vec);
        pz_next_limbs.push(pz);
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
    let mut lambda_limbs = [Mersenne31::ZERO; 3];
    let mut out_limbs = [Mersenne31::ZERO; 3];
    let mut zeta_limbs = [Mersenne31::ZERO; 3];
    let mut zeta_next_limbs = [Mersenne31::ZERO; 3];
    alpha_limbs.copy_from_slice(&alpha_vec);
    lambda_limbs.copy_from_slice(&lambda_vec);
    out_limbs.copy_from_slice(&out_vec);
    zeta_limbs.copy_from_slice(&zeta_vec);
    zeta_next_limbs.copy_from_slice(&zeta_next_vec);
    Some((
        DeepRoLeafTraceStepProof {
            sx: sx_v[0],
            sy: sy_v[0],
            alpha_limbs,
            width,
            px: px_vec,
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

fn encode_deep_ro_leaf_traces(out: &mut Vec<u8>, deeps: &[DeepRoLeafTraceStepProof]) {
    out.extend_from_slice(&(deeps.len() as u32).to_le_bytes());
    for d in deeps {
        encode_deep_ro_leaf_trace(out, d);
    }
}

fn decode_deep_ro_leaf_traces(
    proof: &[u8],
    offset: usize,
    max: usize,
) -> Option<(Vec<DeepRoLeafTraceStepProof>, usize)> {
    let (len, cursor) = read_u32_le(proof, offset)?;
    if len as usize > max {
        return None;
    }
    let mut deeps = Vec::with_capacity(len as usize);
    let mut cursor = cursor;
    for _ in 0..len {
        let (d, next) = decode_deep_ro_leaf_trace(proof, cursor)?;
        deeps.push(d);
        cursor = next;
    }
    Some((deeps, cursor))
}

fn decode_leaf_deep_ros(proof: &[u8], offset: usize) -> Option<(Vec<DeepRoStepProof>, usize)> {
    let (len, cursor) = read_u32_le(proof, offset)?;
    if len as usize > LEAF_FRI_PROVEN_QUERIES {
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

fn encode_leaf_cert(out: &mut Vec<u8>, c: &LeafPcsCertificate) {
    out.push(c.kind as u8);
    out.push(LEAF_MMCS_FOLD_V);
    encode_mmcs_groups(out, &c.mmcs_groups);
    out.push(LEAF_FRI_FOLD_V);
    encode_fri_fold_groups(out, &c.fri_fold_groups);
    out.extend_from_slice(&c.trace_width.to_le_bytes());
    out.extend_from_slice(&c.degree_bits.to_le_bytes());
    out.extend_from_slice(&c.stmt_digest);
    out.extend_from_slice(&c.trace_commitment);
    out.extend_from_slice(&c.lde_index.to_le_bytes());
    out.extend_from_slice(&(c.lde_row.len() as u32).to_le_bytes());
    write_m31_row(out, &c.lde_row);
    out.extend_from_slice(&(c.siblings.len() as u32).to_le_bytes());
    for sib in &c.siblings {
        out.extend_from_slice(sib);
    }
    encode_fri_mmcs_path(out, &c.merkle_fold);
    encode_fri_folds(out, &c.fri_fold_ys);
    encode_fri_folds(out, &c.fri_folds);
    encode_deep_ros(out, &c.deep_ros);
    encode_deep_ro_leaf_traces(out, &c.deep_ro_traces);
    encode_ood(out, &c.ood);
    encode_fri_val_mmcs(out, &c.fri_val_mmcs);
    encode_fri_chal_mmcs(out, &c.fri_chal_mmcs);
}

fn decode_leaf_cert(proof: &[u8], offset: usize) -> Option<(LeafPcsCertificate, usize)> {
    let kind = LeafKind::from_u8(*proof.get(offset)?)?;
    let fold_v = *proof.get(offset + 1)?;
    if fold_v != LEAF_MMCS_FOLD_V {
        return None;
    }
    let cursor = offset + 2;
    let (mmcs_groups, cursor) = decode_mmcs_groups(proof, cursor)?;
    let fri_fold_v = *proof.get(cursor)?;
    if fri_fold_v != LEAF_FRI_FOLD_V {
        return None;
    }
    let cursor = cursor + 1;
    let (fri_fold_groups, cursor) = decode_fri_fold_groups(proof, cursor)?;
    let (trace_width, cursor) = read_u32_le(proof, cursor)?;
    let (degree_bits, cursor) = read_u32_le(proof, cursor)?;
    let (stmt_digest, cursor) = read_fixed::<32>(proof, cursor)?;
    let (trace_commitment, cursor) = read_fixed::<32>(proof, cursor)?;
    let (lde_index, cursor) = read_u32_le(proof, cursor)?;
    let (lde_len, cursor) = read_u32_le(proof, cursor)?;
    let (lde_row, cursor) = read_m31_row(proof, cursor, lde_len as usize)?;
    let (sib_len, cursor) = read_u32_le(proof, cursor)?;
    if sib_len as usize > LEAF_PCS_MAX_SIBLINGS {
        return None;
    }
    let mut siblings = Vec::with_capacity(sib_len as usize);
    let mut cursor = cursor;
    for _ in 0..sib_len {
        let (sib, next) = read_fixed::<32>(proof, cursor)?;
        siblings.push(sib);
        cursor = next;
    }
    let (merkle_fold, cursor) = decode_fri_mmcs_path(proof, cursor)?;
    let (fri_fold_ys, cursor) = decode_fri_folds(proof, cursor, AGG_FRI_MAX_FOLD_YS)?;
    let (fri_folds, cursor) =
        decode_fri_folds(proof, cursor, LEAF_FRI_MAX_ROUNDS * LEAF_FRI_PROVEN_QUERIES)?;
    let (deep_ros, cursor) = decode_leaf_deep_ros(proof, cursor)?;
    let (deep_ro_traces, cursor) =
        decode_deep_ro_leaf_traces(proof, cursor, LEAF_FRI_PROVEN_QUERIES)?;
    let (ood, cursor) = decode_ood(proof, cursor)?;
    let (fri_val_mmcs, cursor) = decode_fri_val_mmcs(proof, cursor)?;
    let (fri_chal_mmcs, cursor) = decode_fri_chal_mmcs(proof, cursor)?;
    Some((
        LeafPcsCertificate {
            kind,
            trace_width,
            degree_bits,
            stmt_digest,
            trace_commitment,
            lde_index,
            lde_row,
            siblings,
            merkle_fold,
            mmcs_groups,
            fri_fold_groups,
            fri_fold_ys,
            fri_folds,
            deep_ros,
            deep_ro_traces,
            ood,
            fri_val_mmcs,
            fri_chal_mmcs,
        },
        cursor,
    ))
}

/// Encodes a leaf PCS bundle (cert count + certificates) into `out`.
pub fn encode_leaf_bundle(out: &mut Vec<u8>, bundle: &LeafPcsBundle) {
    out.extend_from_slice(&(bundle.certs.len() as u32).to_le_bytes());
    for cert in &bundle.certs {
        encode_leaf_cert(out, cert);
    }
}

/// Decodes a leaf PCS bundle starting at `offset`.
pub fn decode_leaf_bundle(proof: &[u8], offset: usize) -> Option<(LeafPcsBundle, usize)> {
    let (len, cursor) = read_u32_le(proof, offset)?;
    if len == 0 || len as usize > 64 {
        return None;
    }
    let mut certs = Vec::with_capacity(len as usize);
    let mut cursor = cursor;
    for _ in 0..len {
        let (cert, next) = decode_leaf_cert(proof, cursor)?;
        certs.push(cert);
        cursor = next;
    }
    Some((LeafPcsBundle { certs }, cursor))
}

/// Serializes a standalone leaf PCS bundle (no surrounding RecAgg framing).
pub fn encode_leaf_pcs_bundle_bytes(bundle: &LeafPcsBundle) -> Vec<u8> {
    let mut out = Vec::new();
    encode_leaf_bundle(&mut out, bundle);
    out
}

/// Deserializes a standalone leaf PCS bundle produced by [`encode_leaf_pcs_bundle_bytes`].
pub fn decode_leaf_pcs_bundle_bytes(bytes: &[u8]) -> Option<LeafPcsBundle> {
    let (bundle, end) = decode_leaf_bundle(bytes, 0)?;
    if end != bytes.len() {
        return None;
    }
    Some(bundle)
}

const SIDE_NONE: u8 = 0;
const SIDE_AGG: u8 = 1;
const SIDE_LEAF: u8 = 2;

fn encode_side(
    out: &mut Vec<u8>,
    agg_cert: &Option<AggPcsCertificate>,
    leaf_bundle: &Option<LeafPcsBundle>,
) {
    match (agg_cert, leaf_bundle) {
        (None, None) => out.push(SIDE_NONE),
        (Some(c), None) => {
            out.push(SIDE_AGG);
            encode_agg_cert(out, c);
        }
        (None, Some(b)) => {
            out.push(SIDE_LEAF);
            encode_leaf_bundle(out, b);
        }
        (Some(_), Some(_)) => unreachable!("agg cert and leaf bundle are mutually exclusive"),
    }
}

fn decode_side(
    proof: &[u8],
    offset: usize,
) -> Option<(Option<AggPcsCertificate>, Option<LeafPcsBundle>, usize)> {
    let flag = *proof.get(offset)?;
    let cursor = offset + 1;
    match flag {
        SIDE_NONE => Some((None, None, cursor)),
        SIDE_AGG => {
            let (cert, cursor) = decode_agg_cert(proof, cursor)?;
            Some((Some(cert), None, cursor))
        }
        SIDE_LEAF => {
            let (bundle, cursor) = decode_leaf_bundle(proof, cursor)?;
            Some((None, Some(bundle), cursor))
        }
        _ => None,
    }
}

#[cfg(test)]
fn diagnose_decode_leaf_cert(
    proof: &[u8],
    offset: usize,
) -> Result<(LeafPcsCertificate, usize), String> {
    let kind = LeafKind::from_u8(*proof.get(offset).ok_or("kind byte")?).ok_or("invalid kind")?;
    let fold_v = *proof.get(offset + 1).ok_or("mmcs_fold_v")?;
    if fold_v != LEAF_MMCS_FOLD_V {
        return Err(format!("unsupported mmcs_fold_v {fold_v}"));
    }
    let cursor = offset + 2;
    let (mmcs_groups, cursor) = decode_mmcs_groups(proof, cursor).ok_or("mmcs_groups")?;
    let fri_fold_v = *proof.get(cursor).ok_or("fri_fold_v")?;
    if fri_fold_v != LEAF_FRI_FOLD_V {
        return Err(format!("unsupported fri_fold_v {fri_fold_v}"));
    }
    let cursor = cursor + 1;
    let (fri_fold_groups, cursor) =
        decode_fri_fold_groups(proof, cursor).ok_or("fri_fold_groups")?;
    let (trace_width, cursor) = read_u32_le(proof, cursor).ok_or("trace_width")?;
    let (degree_bits, cursor) = read_u32_le(proof, cursor).ok_or("degree_bits")?;
    let (stmt_digest, cursor) = read_fixed::<32>(proof, cursor).ok_or("stmt_digest")?;
    let (trace_commitment, cursor) = read_fixed::<32>(proof, cursor).ok_or("trace_commitment")?;
    let (lde_index, cursor) = read_u32_le(proof, cursor).ok_or("lde_index")?;
    let (lde_len, cursor) = read_u32_le(proof, cursor).ok_or("lde_len")?;
    let (lde_row, cursor) = read_m31_row(proof, cursor, lde_len as usize).ok_or("lde_row")?;
    let (sib_len, cursor) = read_u32_le(proof, cursor).ok_or("sib_len")?;
    if sib_len as usize > LEAF_PCS_MAX_SIBLINGS {
        return Err(format!("sib_len {sib_len} > max"));
    }
    let mut siblings = Vec::with_capacity(sib_len as usize);
    let mut cursor = cursor;
    for i in 0..sib_len {
        let (sib, next) = read_fixed::<32>(proof, cursor).ok_or(format!("sibling {i}"))?;
        siblings.push(sib);
        cursor = next;
    }
    let (merkle_fold, cursor) = decode_fri_mmcs_path(proof, cursor).ok_or("merkle_fold")?;
    let (fri_fold_ys, cursor) =
        decode_fri_folds(proof, cursor, AGG_FRI_MAX_FOLD_YS).ok_or("fri_fold_ys")?;
    let (fri_folds, cursor) =
        decode_fri_folds(proof, cursor, LEAF_FRI_MAX_ROUNDS * LEAF_FRI_PROVEN_QUERIES)
            .ok_or("fri_folds")?;
    let (deep_ros, cursor) = decode_leaf_deep_ros(proof, cursor).ok_or("deep_ros")?;
    let (deep_ro_traces, cursor) =
        decode_deep_ro_leaf_traces(proof, cursor, LEAF_FRI_PROVEN_QUERIES)
            .ok_or("deep_ro_traces")?;
    let (ood, cursor) = decode_ood(proof, cursor).ok_or("ood")?;
    let (fri_val_mmcs, cursor) = decode_fri_val_mmcs(proof, cursor).ok_or("fri_val_mmcs")?;
    let (fri_chal_mmcs, cursor) = decode_fri_chal_mmcs(proof, cursor).ok_or("fri_chal_mmcs")?;
    Ok((
        LeafPcsCertificate {
            kind,
            trace_width,
            degree_bits,
            stmt_digest,
            trace_commitment,
            lde_index,
            lde_row,
            siblings,
            merkle_fold,
            mmcs_groups,
            fri_fold_groups,
            fri_fold_ys,
            fri_folds,
            deep_ros,
            deep_ro_traces,
            ood,
            fri_val_mmcs,
            fri_chal_mmcs,
        },
        cursor,
    ))
}

#[cfg(test)]
fn diagnose_decode_side(
    proof: &[u8],
    offset: usize,
    side: &str,
) -> Result<(Option<AggPcsCertificate>, Option<LeafPcsBundle>, usize), String> {
    let flag = *proof.get(offset).ok_or(format!("{side} flag"))?;
    let cursor = offset + 1;
    match flag {
        SIDE_NONE => Ok((None, None, cursor)),
        SIDE_AGG => {
            let (cert, cursor) =
                decode_agg_cert(proof, cursor).ok_or(format!("{side} agg cert"))?;
            Ok((Some(cert), None, cursor))
        }
        SIDE_LEAF => {
            let (len, cursor) = read_u32_le(proof, cursor).ok_or(format!("{side} bundle len"))?;
            if len == 0 || len as usize > 64 {
                return Err(format!("{side} bundle len {len}"));
            }
            let mut certs = Vec::with_capacity(len as usize);
            let mut cursor = cursor;
            for i in 0..len {
                let (cert, next) = diagnose_decode_leaf_cert(proof, cursor)
                    .map_err(|e| format!("{side} cert {i}: {e}"))?;
                certs.push(cert);
                cursor = next;
            }
            Ok((None, Some(LeafPcsBundle { certs }), cursor))
        }
        other => Err(format!("{side} unknown flag {other}")),
    }
}

fn encode_agg_cert(out: &mut Vec<u8>, c: &AggPcsCertificate) {
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
    out.push(LEAF_MMCS_FOLD_V);
    encode_mmcs_groups(out, &c.mmcs_groups);
    out.push(LEAF_FRI_FOLD_V);
    encode_fri_fold_groups(out, &c.fri_fold_groups);
    encode_fri_mmcs_path(out, &c.merkle_fold);
    encode_fri_folds(out, &c.fri_fold_ys);
    encode_fri_folds(out, &c.fri_folds);
    encode_deep_ros(out, &c.deep_ros);
    encode_deep_ro_traces(out, &c.deep_ro_traces);
    encode_ood(out, &c.ood);
    encode_fri_val_mmcs(out, &c.fri_val_mmcs);
    encode_fri_chal_mmcs(out, &c.fri_chal_mmcs);
}

fn decode_agg_cert(proof: &[u8], offset: usize) -> Option<(AggPcsCertificate, usize)> {
    let (stmt_left_hash, cursor) = read_fixed::<{ CHILD_HASH_LEN }>(proof, offset)?;
    let (stmt_right_hash, cursor) = read_fixed::<{ CHILD_HASH_LEN }>(proof, cursor)?;
    let (trace_commitment, cursor) = read_fixed::<32>(proof, cursor)?;
    let (natural_vec, cursor) = read_m31_row(proof, cursor, AGG_WIDTH)?;
    let mut natural_row = [Mersenne31::ZERO; AGG_WIDTH];
    natural_row.copy_from_slice(&natural_vec);
    let (lde_index, cursor) = read_u32_le(proof, cursor)?;
    let (lde_len, cursor) = read_u32_le(proof, cursor)?;
    let (lde_row, cursor) = match lde_len as usize {
        0 => (Vec::new(), cursor),
        AGG_WIDTH => read_m31_row(proof, cursor, lde_len as usize)?,
        _ => return None,
    };
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
    let fold_v = *proof.get(cursor)?;
    if fold_v != LEAF_MMCS_FOLD_V {
        return None;
    }
    let cursor = cursor + 1;
    let (mmcs_groups, cursor) = decode_mmcs_groups(proof, cursor)?;
    let fri_fold_v = *proof.get(cursor)?;
    if fri_fold_v != LEAF_FRI_FOLD_V {
        return None;
    }
    let cursor = cursor + 1;
    let (fri_fold_groups, cursor) = decode_fri_fold_groups(proof, cursor)?;
    let (merkle_fold, cursor) = decode_fri_mmcs_path(proof, cursor)?;
    let (fri_fold_ys, cursor) = decode_fri_folds(proof, cursor, AGG_FRI_MAX_FOLD_YS)?;
    let (fri_folds, cursor) =
        decode_fri_folds(proof, cursor, AGG_FRI_MAX_ROUNDS * AGG_FRI_PROVEN_QUERIES)?;
    let (deep_ros, cursor) = decode_deep_ros(proof, cursor, AGG_DEEP_RO_MAX)?;
    let (deep_ro_traces, cursor) = decode_deep_ro_traces(proof, cursor, AGG_DEEP_RO_TRACE_MAX)?;
    let (ood, cursor) = decode_ood(proof, cursor)?;
    let (fri_val_mmcs, cursor) = decode_fri_val_mmcs(proof, cursor)?;
    let (fri_chal_mmcs, cursor) = decode_fri_chal_mmcs(proof, cursor)?;
    Some((
        AggPcsCertificate {
            stmt_left_hash,
            stmt_right_hash,
            trace_commitment,
            natural_row,
            lde_index,
            lde_row,
            siblings,
            merkle_fold,
            mmcs_groups,
            fri_fold_groups,
            fri_fold_ys,
            fri_folds,
            deep_ros,
            deep_ro_traces,
            ood,
            fri_val_mmcs,
            fri_chal_mmcs,
        },
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
    encode_side(&mut out, &context.left_agg_cert, &context.left_leaf_bundle);
    encode_side(
        &mut out,
        &context.right_agg_cert,
        &context.right_leaf_bundle,
    );
    out.extend_from_slice(&(plonky3_bytes.len() as u32).to_le_bytes());
    out.extend_from_slice(plonky3_bytes);
    out
}

/// Parsed RecAgg V6 header + side PCS payloads (before matching an expected context).
///
/// Verify paths use this to reuse the leaf/agg PCS already encoded in the proof
/// instead of re-proving them from the child STARKs.
#[derive(Debug, Clone)]
pub struct RecAggSidesV6 {
    pub parent_task_id: String,
    pub compose_label: String,
    pub manifest_root_hash: String,
    pub left_child_hash: [u8; CHILD_HASH_LEN],
    pub right_child_hash: [u8; CHILD_HASH_LEN],
    pub left_stark_digest: [u8; STARK_DIGEST_LEN],
    pub right_stark_digest: [u8; STARK_DIGEST_LEN],
    pub left_kind: u8,
    pub right_kind: u8,
    pub left_agg_cert: Option<AggPcsCertificate>,
    pub right_agg_cert: Option<AggPcsCertificate>,
    pub left_leaf_bundle: Option<LeafPcsBundle>,
    pub right_leaf_bundle: Option<LeafPcsBundle>,
}

/// Decode RecAgg V6 sides without requiring a pre-built expected context.
pub fn parse_rec_agg_sides_v6(proof: &[u8]) -> Option<RecAggSidesV6> {
    let marker_pos = locate_inner_marker(proof)?;
    let parent_end = marker_pos.saturating_sub(1);
    let parent_task_id = std::str::from_utf8(&proof[..parent_end]).ok()?.to_string();

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
    let (left_cert, left_leaf, cursor) = decode_side(proof, cursor)?;
    let (right_cert, right_leaf, cursor) = decode_side(proof, cursor)?;

    // Ensure the trailing Plonky3 payload is well-formed even though callers may
    // ignore it (they re-decode via [`decode_rec_agg_proof_owned_v6`]).
    let (len, cursor) = read_u32_le(proof, cursor)?;
    let end = cursor + len as usize;
    let _ = proof.get(cursor..end)?;
    if end != proof.len() {
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
    if left_kind == REC_KIND_AGG && (left_cert.is_none() || left_leaf.is_some()) {
        return None;
    }
    if right_kind == REC_KIND_AGG && (right_cert.is_none() || right_leaf.is_some()) {
        return None;
    }

    Some(RecAggSidesV6 {
        parent_task_id,
        compose_label: compose_label.to_string(),
        manifest_root_hash: manifest_root_hash.to_string(),
        left_child_hash: left_hash,
        right_child_hash: right_hash,
        left_stark_digest: left_stark,
        right_stark_digest: right_stark,
        left_kind,
        right_kind,
        left_agg_cert: left_cert,
        right_agg_cert: right_cert,
        left_leaf_bundle: left_leaf,
        right_leaf_bundle: right_leaf,
    })
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
    let (left_cert, left_leaf, cursor) = decode_side(proof, cursor)?;
    let (right_cert, right_leaf, cursor) = decode_side(proof, cursor)?;

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
        || left_leaf != expected.left_leaf_bundle
        || right_leaf != expected.right_leaf_bundle
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
    if left_kind == REC_KIND_AGG && (left_cert.is_none() || left_leaf.is_some()) {
        return None;
    }
    if right_kind == REC_KIND_AGG && (right_cert.is_none() || right_leaf.is_some()) {
        return None;
    }
    if left_kind == REC_KIND_LEAF
        && expected.left_leaf_bundle.is_some()
        && left_leaf.as_ref() != expected.left_leaf_bundle.as_ref()
    {
        return None;
    }
    if right_kind == REC_KIND_LEAF
        && expected.right_leaf_bundle.is_some()
        && right_leaf.as_ref() != expected.right_leaf_bundle.as_ref()
    {
        return None;
    }
    if left_kind == REC_KIND_LEAF && expected.left_leaf_bundle.is_none() && left_leaf.is_some() {
        return None;
    }
    if right_kind == REC_KIND_LEAF && expected.right_leaf_bundle.is_none() && right_leaf.is_some() {
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

/// Test-only: pinpoints why [`decode_rec_agg_proof_owned_v6`] would return `None`.
#[cfg(test)]
pub fn diagnose_decode_rec_agg_v6(
    proof: &[u8],
    expected: &RecursiveAggregationContext<'_>,
) -> Result<Vec<u8>, String> {
    if !proof.starts_with(expected.parent_task_id.as_bytes()) {
        return Err("parent_task_id prefix mismatch".into());
    }
    let marker_pos = locate_inner_marker(proof).ok_or("inner marker not found")?;
    let parent_end = marker_pos.saturating_sub(1);
    let parent_task_id =
        std::str::from_utf8(&proof[..parent_end]).map_err(|_| "parent_task_id utf8")?;
    if parent_task_id != expected.parent_task_id {
        return Err(format!(
            "parent_task_id mismatch: {parent_task_id} != {}",
            expected.parent_task_id
        ));
    }

    let cursor = marker_pos + V6_REC_AGG_INNER_MARKER.len();
    let (compose_label, cursor) = read_cstr(proof, cursor).ok_or("compose_label cstr")?;
    let (manifest_root_hash, cursor) = read_cstr(proof, cursor).ok_or("manifest_root_hash cstr")?;
    let (left_hash, cursor) = read_fixed::<{ CHILD_HASH_LEN }>(proof, cursor).ok_or("left_hash")?;
    let (right_hash, cursor) =
        read_fixed::<{ CHILD_HASH_LEN }>(proof, cursor).ok_or("right_hash")?;
    let (left_stark, cursor) =
        read_fixed::<{ STARK_DIGEST_LEN }>(proof, cursor).ok_or("left_stark")?;
    let (right_stark, cursor) =
        read_fixed::<{ STARK_DIGEST_LEN }>(proof, cursor).ok_or("right_stark")?;
    let left_kind = *proof.get(cursor).ok_or("left_kind")?;
    let right_kind = *proof.get(cursor + 1).ok_or("right_kind")?;
    let cursor = cursor + 2;
    let (left_cert, left_leaf, cursor) = diagnose_decode_side(proof, cursor, "left")?;
    let (right_cert, right_leaf, cursor) = diagnose_decode_side(proof, cursor, "right")?;

    if compose_label != expected.compose_label {
        return Err(format!(
            "compose_label: {compose_label} != {}",
            expected.compose_label
        ));
    }
    if manifest_root_hash != expected.manifest_root_hash {
        return Err(format!(
            "manifest_root_hash: {manifest_root_hash} != {}",
            expected.manifest_root_hash
        ));
    }
    if left_hash != expected.left_child_hash {
        return Err("left_child_hash mismatch".into());
    }
    if right_hash != expected.right_child_hash {
        return Err("right_child_hash mismatch".into());
    }
    if left_stark != expected.left_stark_digest {
        return Err("left_stark_digest mismatch".into());
    }
    if right_stark != expected.right_stark_digest {
        return Err("right_stark_digest mismatch".into());
    }
    if left_kind != expected.left_kind {
        return Err(format!("left_kind: {left_kind} != {}", expected.left_kind));
    }
    if right_kind != expected.right_kind {
        return Err(format!(
            "right_kind: {right_kind} != {}",
            expected.right_kind
        ));
    }
    if left_cert != expected.left_agg_cert {
        return Err("left_agg_cert mismatch".into());
    }
    if right_cert != expected.right_agg_cert {
        return Err("right_agg_cert mismatch".into());
    }
    if left_leaf != expected.left_leaf_bundle {
        return Err(format!(
            "left_leaf_bundle mismatch (expected_some={}, decoded_some={})",
            expected.left_leaf_bundle.is_some(),
            left_leaf.is_some()
        ));
    }
    if right_leaf != expected.right_leaf_bundle {
        return Err(format!(
            "right_leaf_bundle mismatch (expected_some={}, decoded_some={})",
            expected.right_leaf_bundle.is_some(),
            right_leaf.is_some()
        ));
    }

    let (len, cursor) = read_u32_le(proof, cursor).ok_or("plonky3 len")?;
    let end = cursor + len as usize;
    let payload = proof
        .get(cursor..end)
        .ok_or("plonky3 payload bounds")?
        .to_vec();
    if end != proof.len() {
        return Err(format!("trailing bytes: end={end} len={}", proof.len()));
    }
    Ok(payload)
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
    use crate::generate_plonky3_stark_proof;
    use crate::plonky3_stark::recursion::build_leaf_pcs_bundle_from_child;
    use crate::trace_spec::idle_qubit0_trace;
    use crate::transcript::StarkContext;

    #[test]
    fn parse_rec_agg_sides_v6_roundtrip_none_sides() {
        let ctx = RecursiveAggregationContext {
            parent_task_id: "parent-parse",
            compose_label: "root",
            manifest_root_hash: "manifest",
            left_child_hash: [1u8; CHILD_HASH_LEN],
            right_child_hash: [2u8; CHILD_HASH_LEN],
            left_stark_digest: [3u8; STARK_DIGEST_LEN],
            right_stark_digest: [4u8; STARK_DIGEST_LEN],
            left_kind: REC_KIND_LEAF,
            right_kind: REC_KIND_LEAF,
            left_agg_cert: None,
            right_agg_cert: None,
            left_leaf_bundle: None,
            right_leaf_bundle: None,
        };
        let encoded = encode_rec_agg_proof_v6(&ctx, b"plonky3-bytes");
        let sides = parse_rec_agg_sides_v6(&encoded).expect("parse sides");
        assert_eq!(sides.parent_task_id, "parent-parse");
        assert_eq!(sides.compose_label, "root");
        assert_eq!(sides.manifest_root_hash, "manifest");
        assert_eq!(sides.left_child_hash, [1u8; CHILD_HASH_LEN]);
        assert_eq!(sides.right_child_hash, [2u8; CHILD_HASH_LEN]);
        assert_eq!(sides.left_kind, REC_KIND_LEAF);
        assert_eq!(sides.right_kind, REC_KIND_LEAF);
        assert!(sides.left_leaf_bundle.is_none());
        assert!(sides.right_leaf_bundle.is_none());
    }

    #[test]
    fn rec_tail_v6_roundtrip() {
        let body = b"v3-bytes";
        let rec = b"rec-proof";
        let combined = append_rec_tail_v6(body.to_vec(), rec);
        let (left, right) = split_rec_tail_v6(&combined).expect("split");
        assert_eq!(left, body);
        assert_eq!(right, rec);
    }

    #[test]
    #[ignore = "slow; local only — not run in CI"]
    fn agg_cert_v6_codec_roundtrip() {
        use crate::aggregation::CHILD_HASH_LEN;
        use crate::plonky3_stark::aggregation::AggregationContext;
        use crate::plonky3_stark::generate_aggregation_proof;
        use crate::plonky3_stark::recursion::opening_cert::build_agg_pcs_certificate;

        let ctx = AggregationContext {
            parent_task_id: "parent-codec",
            compose_label: "L1:0",
            manifest_root_hash: "",
            left_child_hash: [9u8; CHILD_HASH_LEN],
            right_child_hash: [10u8; CHILD_HASH_LEN],
        };
        let agg = generate_aggregation_proof(&ctx).expect("prove");
        let cert = build_agg_pcs_certificate(&ctx, &agg).expect("cert");
        let mut out = Vec::new();
        encode_agg_cert(&mut out, &cert);
        let (decoded, end) = decode_agg_cert(&out, 0).expect("decode agg cert");
        assert_eq!(end, out.len());
        assert_eq!(decoded, cert);
    }

    #[test]
    #[ignore = "slow; local only — not run in CI"]
    fn unitary_leaf_bundle_v6_codec_roundtrip() {
        let ctx = StarkContext {
            circuit_id: "c-codec",
            sub_task_id: "sub-codec",
            node_id: "n1",
            slice_id: "0",
            output_hash: "out",
            terminal_statevector_digest: "",
            measurement_spec_hash: "",
        };
        let trace = idle_qubit0_trace();
        let transcript = generate_plonky3_stark_proof(&ctx, &trace).expect("prove");
        let bundle = build_leaf_pcs_bundle_from_child(&transcript).expect("bundle");
        let mut out = Vec::new();
        encode_leaf_bundle(&mut out, &bundle);
        let (decoded, end) = decode_leaf_bundle(&out, 0).expect("decode leaf bundle");
        assert_eq!(end, out.len());
        assert_eq!(decoded, bundle);
    }

    #[test]
    fn m4c_group_fold_codec_roundtrip() {
        use crate::plonky3_stark::recursion::fri_mmcs_group_m4b::generate_keccak_group_fold_proof;
        use crate::plonky3_stark::recursion::fri_mmcs_group_m4b::MmcsPathStatement;
        use crate::plonky3_stark::recursion::keccak_f_native::keccak256_compress;
        use crate::plonky3_stark::recursion::merkle_keccak::hash_val_leaf;
        use p3_field::PrimeCharacteristicRing;

        let row = vec![
            Mersenne31::from_u32(1),
            Mersenne31::from_u32(2),
            Mersenne31::from_u32(3),
        ];
        let leaf = hash_val_leaf(&row);
        let sib = [9u8; 32];
        let root = keccak256_compress(leaf, sib);
        let stmts = vec![
            MmcsPathStatement {
                row: row.clone(),
                siblings: vec![sib],
                index: 0,
                root,
            },
            MmcsPathStatement {
                row: vec![
                    Mersenne31::from_u32(4),
                    Mersenne31::from_u32(5),
                    Mersenne31::from_u32(6),
                ],
                siblings: vec![[3u8; 32]],
                index: 1,
                root: {
                    let l = hash_val_leaf(&[
                        Mersenne31::from_u32(4),
                        Mersenne31::from_u32(5),
                        Mersenne31::from_u32(6),
                    ]);
                    keccak256_compress([3u8; 32], l)
                },
            },
        ];
        let g = generate_keccak_group_fold_proof(&stmts).expect("group");
        let groups = LeafMmcsFoldGroups {
            val_trace: vec![g],
            val_quot: vec![],
            val_quot_batch: vec![],
            chal_first_layer: vec![],
            chal_commit: vec![],
        };
        let mut out = Vec::new();
        encode_mmcs_groups(&mut out, &groups);
        let (decoded, end) = decode_mmcs_groups(&out, 0).expect("decode groups");
        assert_eq!(end, out.len());
        assert_eq!(decoded, groups);
    }
}

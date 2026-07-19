//! V6 recursive aggregation transcript (R3-M2): M1 fields + AggregationAir PCS certs.

use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_mersenne_31::Mersenne31;

use crate::aggregation::CHILD_HASH_LEN;
use crate::plonky3_stark::aggregation_air::AGG_WIDTH;

use super::air::{REC_KIND_AGG, REC_KIND_LEAF};
use super::context::RecursiveAggregationContext;
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
    Some((
        Some(AggPcsCertificate {
            stmt_left_hash,
            stmt_right_hash,
            trace_commitment,
            natural_row,
            lde_index,
            lde_row,
            siblings,
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

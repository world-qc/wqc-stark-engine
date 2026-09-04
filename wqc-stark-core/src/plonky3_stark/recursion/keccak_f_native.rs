//! Native Keccak-f[1600] / Keccak-256 matching tiny_keccak `Keccak::v256` (delim `0x01`).
//!
//! Used as the witness oracle and golden reference for R3-M2.5b in-circuit gadgets.

#![allow(clippy::needless_range_loop)]

use p3_field::PrimeField32;
use p3_mersenne_31::Mersenne31;

use crate::plonky3_stark::aggregation_air::AGG_WIDTH;

pub const KECCAK_ROUNDS: usize = 24;
pub const KECCAK_RATE: usize = 136; // 1088-bit rate for 256-bit security
pub const KECCAK_STATE_BYTES: usize = 200;
pub const KECCAK_STATE_BITS: usize = 1600;
pub const KECCAK_LANES: usize = 25;
pub const KECCAK_DELIM: u8 = 0x01;
pub const KECCAK256_OUT: usize = 32;

pub const RC: [u64; KECCAK_ROUNDS] = [
    0x0000_0000_0000_0001,
    0x0000_0000_0000_8082,
    0x8000_0000_0000_808A,
    0x8000_0000_8000_8000,
    0x0000_0000_0000_808B,
    0x0000_0000_8000_0001,
    0x8000_0000_8000_8081,
    0x8000_0000_0000_8009,
    0x0000_0000_0000_008A,
    0x0000_0000_0000_0088,
    0x0000_0000_8000_8009,
    0x0000_0000_8000_000A,
    0x0000_0000_8000_808B,
    0x8000_0000_0000_008B,
    0x8000_0000_0000_8089,
    0x8000_0000_0000_8003,
    0x8000_0000_0000_8002,
    0x8000_0000_0000_0080,
    0x0000_0000_0000_800A,
    0x8000_0000_8000_000A,
    0x8000_0000_8000_8081,
    0x8000_0000_0000_8080,
    0x0000_0000_8000_0001,
    0x8000_0000_8000_8008,
];

const RHO: [u32; 24] = [
    1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14, 27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20, 44,
];

const PI: [usize; 24] = [
    10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4, 15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1,
];

/// One Keccak-f round (θ, ρ, π, χ, ι) matching tiny_keccak.
pub fn keccak_round(a: &mut [u64; KECCAK_LANES], rc: u64) {
    let mut array = [0u64; 5];

    // Theta
    for x in 0..5 {
        array[x] = a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20];
    }
    for x in 0..5 {
        let d = array[(x + 4) % 5] ^ array[(x + 1) % 5].rotate_left(1);
        for y in 0..5 {
            a[y * 5 + x] ^= d;
        }
    }

    // Rho and pi
    let mut last = a[1];
    for x in 0..24 {
        let tmp = a[PI[x]];
        a[PI[x]] = last.rotate_left(RHO[x]);
        last = tmp;
    }

    // Chi
    for y in 0..5 {
        let base = y * 5;
        let t0 = a[base];
        let t1 = a[base + 1];
        let t2 = a[base + 2];
        let t3 = a[base + 3];
        let t4 = a[base + 4];
        a[base] = t0 ^ ((!t1) & t2);
        a[base + 1] = t1 ^ ((!t2) & t3);
        a[base + 2] = t2 ^ ((!t3) & t4);
        a[base + 3] = t3 ^ ((!t4) & t0);
        a[base + 4] = t4 ^ ((!t0) & t1);
    }

    // Iota
    a[0] ^= rc;
}

pub fn keccak_f(state: &mut [u64; KECCAK_LANES]) {
    for &rc in &RC {
        keccak_round(state, rc);
    }
}

pub fn state_to_bytes(state: &[u64; KECCAK_LANES]) -> [u8; KECCAK_STATE_BYTES] {
    let mut out = [0u8; KECCAK_STATE_BYTES];
    for (i, lane) in state.iter().enumerate() {
        out[i * 8..(i + 1) * 8].copy_from_slice(&lane.to_le_bytes());
    }
    out
}

pub fn bytes_to_state(bytes: &[u8; KECCAK_STATE_BYTES]) -> [u64; KECCAK_LANES] {
    core::array::from_fn(|i| {
        let mut buf = [0u8; 8];
        buf.copy_from_slice(&bytes[i * 8..(i + 1) * 8]);
        u64::from_le_bytes(buf)
    })
}

pub fn state_to_bits(state: &[u64; KECCAK_LANES]) -> [bool; KECCAK_STATE_BITS] {
    let mut bits = [false; KECCAK_STATE_BITS];
    for (lane_i, lane) in state.iter().enumerate() {
        for b in 0..64 {
            bits[lane_i * 64 + b] = ((lane >> b) & 1) == 1;
        }
    }
    bits
}

pub fn bits_to_state(bits: &[bool; KECCAK_STATE_BITS]) -> [u64; KECCAK_LANES] {
    core::array::from_fn(|lane_i| {
        let mut lane = 0u64;
        for b in 0..64 {
            if bits[lane_i * 64 + b] {
                lane |= 1u64 << b;
            }
        }
        lane
    })
}

fn xor_bytes_into_state(state: &mut [u64; KECCAK_LANES], offset: usize, src: &[u8]) {
    let mut bytes = state_to_bytes(state);
    for (i, &b) in src.iter().enumerate() {
        bytes[offset + i] ^= b;
    }
    *state = bytes_to_state(&bytes);
}

fn pad_state(state: &mut [u64; KECCAK_LANES], offset: usize) {
    let mut bytes = state_to_bytes(state);
    bytes[offset] ^= KECCAK_DELIM;
    bytes[KECCAK_RATE - 1] ^= 0x80;
    *state = bytes_to_state(&bytes);
}

/// Keccak-256 (original Keccak, delim 0x01) over an arbitrary message.
pub fn keccak256(msg: &[u8]) -> [u8; KECCAK256_OUT] {
    let mut state = [0u64; KECCAK_LANES];
    let mut offset = 0usize;
    let mut ip = 0usize;
    let mut remaining = msg.len();

    while remaining >= KECCAK_RATE - offset {
        let take = KECCAK_RATE - offset;
        xor_bytes_into_state(&mut state, offset, &msg[ip..ip + take]);
        keccak_f(&mut state);
        ip += take;
        remaining -= take;
        offset = 0;
    }
    if remaining > 0 {
        xor_bytes_into_state(&mut state, offset, &msg[ip..ip + remaining]);
        offset += remaining;
    }
    pad_state(&mut state, offset);
    keccak_f(&mut state);

    let bytes = state_to_bytes(&state);
    let mut out = [0u8; KECCAK256_OUT];
    out.copy_from_slice(&bytes[..KECCAK256_OUT]);
    out
}

/// LE serialization of an M31 row (ValMmcs leaf input).
pub fn val_row_to_bytes(row: &[Mersenne31]) -> Vec<u8> {
    row.iter()
        .flat_map(|x| x.as_canonical_u32().to_le_bytes())
        .collect()
}

/// LE serialization of an AggregationAir LDE row (ValMmcs leaf input).
pub fn lde_row_to_bytes(row: &[Mersenne31]) -> Vec<u8> {
    debug_assert_eq!(row.len(), AGG_WIDTH);
    val_row_to_bytes(row)
}

pub fn keccak256_lde_leaf(row: &[Mersenne31]) -> [u8; KECCAK256_OUT] {
    keccak256(&lde_row_to_bytes(row))
}

pub fn keccak256_val_leaf(row: &[Mersenne31]) -> [u8; KECCAK256_OUT] {
    keccak256(&val_row_to_bytes(row))
}

pub fn keccak256_compress(left: [u8; 32], right: [u8; 32]) -> [u8; KECCAK256_OUT] {
    let mut msg = [0u8; 64];
    msg[..32].copy_from_slice(&left);
    msg[32..].copy_from_slice(&right);
    keccak256(&msg)
}

/// Number of Keccak-f permutations for a message of length `msg_len` (single finalize squeeze).
pub fn num_permutations(msg_len: usize) -> usize {
    // Full absorb blocks + one final padded block.
    msg_len / KECCAK_RATE + 1
}

/// Pre-round states for every round of every permutation, plus the final post-perm state.
///
/// Layout for `n = num_permutations(msg.len())`:
/// - `pre_rounds.len() == n * 24`
/// - `final_state` is the state after the last permutation (squeeze source).
pub fn sponge_witness(msg: &[u8]) -> (Vec<[u64; KECCAK_LANES]>, [u64; KECCAK_LANES]) {
    let n = num_permutations(msg.len());
    let mut pre_rounds = Vec::with_capacity(n * KECCAK_ROUNDS);
    let mut state = [0u64; KECCAK_LANES];
    let mut offset = 0usize;
    let mut ip = 0usize;
    let mut remaining = msg.len();
    let mut perms_done = 0usize;

    while remaining >= KECCAK_RATE - offset {
        let take = KECCAK_RATE - offset;
        xor_bytes_into_state(&mut state, offset, &msg[ip..ip + take]);
        for r in 0..KECCAK_ROUNDS {
            pre_rounds.push(state);
            keccak_round(&mut state, RC[r]);
        }
        perms_done += 1;
        ip += take;
        remaining -= take;
        offset = 0;
    }
    if remaining > 0 {
        xor_bytes_into_state(&mut state, offset, &msg[ip..ip + remaining]);
        offset += remaining;
    }
    pad_state(&mut state, offset);
    for r in 0..KECCAK_ROUNDS {
        pre_rounds.push(state);
        keccak_round(&mut state, RC[r]);
    }
    perms_done += 1;
    debug_assert_eq!(perms_done, n);
    debug_assert_eq!(pre_rounds.len(), n * KECCAK_ROUNDS);
    (pre_rounds, state)
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_field::PrimeCharacteristicRing;
    use p3_keccak::Keccak256Hash;
    use p3_symmetric::CryptographicHasher;

    use crate::plonky3_stark::recursion::merkle_keccak::{compress_digests_keccak, hash_lde_leaf};

    #[test]
    fn keccak256_matches_p3() {
        for msg in [
            &[][..],
            b"abc",
            &[0u8; 64],
            &[1u8; 136],
            &[2u8; 264],
            &[3u8; 200],
        ] {
            let ours = keccak256(msg);
            let theirs = Keccak256Hash.hash_iter(msg.iter().copied());
            assert_eq!(ours, theirs, "len={}", msg.len());
        }
    }

    #[test]
    fn compress_and_leaf_match_val_mmcs() {
        let left = [9u8; 32];
        let right = [7u8; 32];
        assert_eq!(
            keccak256_compress(left, right),
            compress_digests_keccak(left, right)
        );

        let row: Vec<_> = (0..AGG_WIDTH)
            .map(|i| Mersenne31::from_u32(i as u32))
            .collect();
        assert_eq!(keccak256_lde_leaf(&row), hash_lde_leaf(&row));
    }

    #[test]
    fn sponge_witness_roundtrip() {
        let msg = [5u8; 64];
        let (pre, final_state) = sponge_witness(&msg);
        assert_eq!(pre.len(), 24);
        let mut s = pre[0];
        for r in 0..24 {
            assert_eq!(s, pre[r]);
            keccak_round(&mut s, RC[r]);
        }
        assert_eq!(s, final_state);
        let bytes = state_to_bytes(&final_state);
        assert_eq!(&bytes[..32], &keccak256(&msg));
    }

    #[test]
    fn sponge_witness_two_blocks() {
        let msg = [6u8; 264];
        let (pre, final_state) = sponge_witness(&msg);
        assert_eq!(pre.len(), 48);
        assert_eq!(&state_to_bytes(&final_state)[..32], &keccak256(&msg));
    }
}

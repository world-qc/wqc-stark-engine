//! R3-M2.5b: fixed-length Keccak-256 sponge STARK (tiny_keccak v256 / ValMmcs).
//!
//! Message lengths: **12** (quot W=3), **24** (Challenge width-2 flattened),
//! **64** (compress), **264** (AggregationAir LDE / trace W=66).
//!
//! Trace columns: 1600 state bits + `live` + 5 round bits (0..23).
//! Publics: `msg_len` byte values + 32 digest bytes. Absorb/pad bind via bit packing.

#![allow(clippy::needless_range_loop)]

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::dense::RowMajorMatrix;
use p3_mersenne_31::Mersenne31;
use p3_uni_stark::{prove, verify};

use crate::plonky3_stark::aggregation_air::AGG_WIDTH;
use crate::plonky3_stark::config::{keccak_circle_config, WqcStarkConfig};

use super::keccak_f_air::{constrain_keccak_round_with_rc, LIVE_COL};
use super::keccak_f_native::{
    keccak256, lde_row_to_bytes, num_permutations, sponge_witness, state_to_bits, val_row_to_bytes,
    KECCAK256_OUT, KECCAK_DELIM, KECCAK_RATE, KECCAK_ROUNDS, KECCAK_STATE_BITS, RC,
};

pub const ROUND_BITS: usize = 5;
pub const ROUND_BIT_COL: usize = LIVE_COL + 1;
pub const SPONGE_WIDTH: usize = KECCAK_STATE_BITS + 1 + ROUND_BITS;

pub const COMPRESS_MSG_LEN: usize = 64;
pub const LEAF_MSG_LEN: usize = AGG_WIDTH * 4; // 264
/// Quotient ValMmcs leaf (width 3 × 4 bytes).
pub const QUOT_LEAF_MSG_LEN: usize = 3 * 4; // 12
/// ChallengeMmcs leaf for EF width-2 flattened to 6 M31 (× 4 bytes).
pub const CHAL_LEAF_MSG_LEN: usize = 6 * 4; // 24

const fn supported_msg_len(len: usize) -> bool {
    len == QUOT_LEAF_MSG_LEN
        || len == CHAL_LEAF_MSG_LEN
        || len == COMPRESS_MSG_LEN
        || len == LEAF_MSG_LEN
}

#[derive(Copy, Clone, Debug)]
pub struct Keccak256SpongeAir {
    pub msg_len: usize,
}

impl Keccak256SpongeAir {
    pub const fn compress() -> Self {
        Self {
            msg_len: COMPRESS_MSG_LEN,
        }
    }

    pub const fn leaf() -> Self {
        Self {
            msg_len: LEAF_MSG_LEN,
        }
    }

    pub fn num_public(&self) -> usize {
        self.msg_len + KECCAK256_OUT
    }
}

impl<F: Field> BaseAir<F> for Keccak256SpongeAir {
    fn width(&self) -> usize {
        SPONGE_WIDTH
    }

    fn max_constraint_degree(&self) -> Option<usize> {
        // Auto-infer: round selectors × χ produce high degree; use keccak_circle_config blowup.
        None
    }

    fn num_public_values(&self) -> usize {
        self.msg_len + KECCAK256_OUT
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

/// Expected rate-byte value after XOR-absorb + pad for the first permutation block.
fn first_block_rate_byte<AB: AirBuilder>(pv: &[AB::Expr], msg_len: usize, byte_i: usize) -> AB::Expr
where
    AB::F: PrimeCharacteristicRing,
{
    if msg_len <= KECCAK_RATE {
        let is_msg = byte_i < msg_len;
        let is_delim = byte_i == msg_len;
        let is_end = byte_i == KECCAK_RATE - 1;
        if is_msg && is_end {
            // Message byte XOR 0x80 (only if msg_len == rate).
            let d: AB::Expr = AB::F::from_u32(0x80).into();
            // Bitwise XOR on u8 values is not field mul; our fixed lengths avoid this case.
            // Supported single-block lengths are < rate, so is_msg && is_end is false.
            let _ = d;
            pv[byte_i].clone()
        } else if is_delim && is_end {
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
        pv[byte_i].clone()
    }
}

/// Rate-byte XOR mask absorbed between permutation 0 and 1 (leaf only).
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

impl<AB: AirBuilder> Air<AB> for Keccak256SpongeAir
where
    AB::F: Field + PrimeCharacteristicRing,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let curr: Vec<AB::Var> = main.current_slice().to_vec();
        let next: Vec<AB::Var> = main.next_slice().to_vec();
        let one = AB::Expr::ONE;
        let pv: Vec<AB::Expr> = builder
            .public_values()
            .iter()
            .map(|v| (*v).into())
            .collect();

        for i in 0..SPONGE_WIDTH {
            let b: AB::Expr = curr[i].into();
            builder.assert_zero(b.clone() * (b - one.clone()));
        }

        let live_c: AB::Expr = curr[LIVE_COL].into();
        let live_n: AB::Expr = next[LIVE_COL].into();
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
        let cont = both_live.clone() * (one.clone() - wrap.clone());

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

        let to_final = live_c.clone() * (one.clone() - live_n.clone());
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
            builder.assert_zero(is_tr.clone() * idle.clone() * (n - c));
        }

        if self.msg_len > KECCAK_RATE {
            // next_state XOR absorb_rate = round(curr); capacity absorb = 0.
            let wrap_en = is_tr * both_live * wrap;
            let expected = super::keccak_f_air::keccak_round_bits_expr_with_rc::<AB>(
                &curr[..KECCAK_STATE_BITS],
                &rc_bits,
            );
            // Constrain rate bytes of (next XOR expected) equal second-block absorb bytes;
            // capacity bits of next equal expected (XOR 0).
            for byte_i in 0..KECCAK_RATE {
                let mut xor_pack = AB::Expr::ZERO;
                let mut pow = AB::Expr::ONE;
                let two = AB::Expr::TWO;
                for bit in 0..8 {
                    let idx = byte_i * 8 + bit;
                    let nb: AB::Expr = next[idx].into();
                    let eb = expected[idx].clone();
                    let x = nb.clone() + eb.clone() - two.clone() * nb * eb;
                    xor_pack += x * pow.clone();
                    pow *= two.clone();
                }
                let want = second_block_rate_byte::<AB>(&pv, self.msg_len, byte_i);
                builder.assert_zero(wrap_en.clone() * (xor_pack - want));
            }
            for i in KECCAK_RATE * 8..KECCAK_STATE_BITS {
                let nb: AB::Expr = next[i].into();
                builder.assert_zero(wrap_en.clone() * (nb - expected[i].clone()));
            }
            builder.assert_zero(wrap_en * round_val_n);
        }

        // First row: pack rate bytes to absorb pattern; capacity bits zero; live=1, round=0.
        for byte_i in 0..KECCAK_RATE {
            let packed = pack_byte_from_state_bits::<AB>(&curr[..KECCAK_STATE_BITS], byte_i);
            let want = first_block_rate_byte::<AB>(&pv, self.msg_len, byte_i);
            builder.when_first_row().assert_zero(packed - want);
        }
        for i in KECCAK_RATE * 8..KECCAK_STATE_BITS {
            let b: AB::Expr = curr[i].into();
            builder.when_first_row().assert_zero(b);
        }
        builder
            .when_first_row()
            .assert_zero(live_c.clone() - one.clone());
        builder.when_first_row().assert_zero(round_val_c);

        // Final rows (live=0): pack first 32 state bytes to digest publics.
        for byte_i in 0..KECCAK256_OUT {
            let packed = pack_byte_from_state_bits::<AB>(&curr[..KECCAK_STATE_BITS], byte_i);
            builder.assert_zero(idle.clone() * (packed - pv[self.msg_len + byte_i].clone()));
        }
    }
}

fn push_round_bits(values: &mut Vec<Mersenne31>, round: usize) {
    for k in 0..ROUND_BITS {
        values.push(bool_m31(((round >> k) & 1) == 1));
    }
}

fn push_state_row(
    values: &mut Vec<Mersenne31>,
    bits: &[bool; KECCAK_STATE_BITS],
    live: bool,
    round: usize,
) {
    for &b in bits.iter() {
        values.push(bool_m31(b));
    }
    values.push(bool_m31(live));
    if live {
        push_round_bits(values, round);
    } else {
        for _ in 0..ROUND_BITS {
            values.push(Mersenne31::ZERO);
        }
    }
}

/// Build a power-of-two sponge trace from the native witness.
pub fn build_sponge_matrix(msg: &[u8]) -> RowMajorMatrix<Mersenne31> {
    let n_perm = num_permutations(msg.len());
    let (pre_rounds, final_state) = sponge_witness(msg);
    debug_assert_eq!(pre_rounds.len(), n_perm * KECCAK_ROUNDS);

    let live_rows = n_perm * KECCAK_ROUNDS;
    let target = (live_rows + 1).next_power_of_two().max(32);

    let mut values = Vec::with_capacity(target * SPONGE_WIDTH);
    for (i, st) in pre_rounds.iter().enumerate() {
        let bits = state_to_bits(st);
        let round = i % KECCAK_ROUNDS;
        push_state_row(&mut values, &bits, true, round);
    }
    let final_bits = state_to_bits(&final_state);
    push_state_row(&mut values, &final_bits, false, 0);
    while values.len() / SPONGE_WIDTH < target {
        push_state_row(&mut values, &final_bits, false, 0);
    }
    RowMajorMatrix::new(values, SPONGE_WIDTH)
}

fn build_public_values(msg: &[u8], digest: &[u8; KECCAK256_OUT]) -> Vec<Mersenne31> {
    let mut pv = Vec::with_capacity(msg.len() + KECCAK256_OUT);
    for &b in msg {
        pv.push(Mersenne31::from_u32(b as u32));
    }
    for &b in digest {
        pv.push(Mersenne31::from_u32(b as u32));
    }
    pv
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Keccak256StarkProof {
    pub msg_len: u32,
    pub digest: [u8; KECCAK256_OUT],
    pub stark: Vec<u8>,
}

pub fn prove_keccak256(msg: &[u8]) -> Result<Keccak256StarkProof, String> {
    if !supported_msg_len(msg.len()) {
        return Err(format!(
            "unsupported keccak256 msg len {} (want {QUOT_LEAF_MSG_LEN}/{CHAL_LEAF_MSG_LEN}/{COMPRESS_MSG_LEN}/{LEAF_MSG_LEN})",
            msg.len()
        ));
    }
    let digest = keccak256(msg);
    let air = Keccak256SpongeAir { msg_len: msg.len() };
    let matrix = build_sponge_matrix(msg);
    let pv = build_public_values(msg, &digest);
    p3_air::check_constraints(&air, &matrix, &pv);
    let config = keccak_circle_config();
    let proof = prove(&config, &air, matrix, &pv);
    let stark =
        postcard::to_allocvec(&proof).map_err(|e| format!("postcard encode keccak256: {e}"))?;
    Ok(Keccak256StarkProof {
        msg_len: msg.len() as u32,
        digest,
        stark,
    })
}

pub fn verify_keccak256(msg: &[u8], proof: &Keccak256StarkProof) -> bool {
    if msg.len() as u32 != proof.msg_len {
        eprintln!("[Keccak256] msg_len mismatch");
        return false;
    }
    if !supported_msg_len(msg.len()) {
        return false;
    }
    let air = Keccak256SpongeAir { msg_len: msg.len() };
    let pv = build_public_values(msg, &proof.digest);
    let stark: p3_uni_stark::Proof<WqcStarkConfig> = match postcard::from_bytes(&proof.stark) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("[Keccak256] postcard: {e}");
            return false;
        }
    };
    let config = keccak_circle_config();
    match verify(&config, &air, &stark, &pv) {
        Ok(()) => true,
        Err(e) => {
            eprintln!("[Keccak256] verify: {e:?}");
            false
        }
    }
}

pub fn prove_compress(left: [u8; 32], right: [u8; 32]) -> Result<Keccak256StarkProof, String> {
    let mut msg = [0u8; 64];
    msg[..32].copy_from_slice(&left);
    msg[32..].copy_from_slice(&right);
    prove_keccak256(&msg)
}

pub fn verify_compress(left: [u8; 32], right: [u8; 32], proof: &Keccak256StarkProof) -> bool {
    let mut msg = [0u8; 64];
    msg[..32].copy_from_slice(&left);
    msg[32..].copy_from_slice(&right);
    if !verify_keccak256(&msg, proof) {
        return false;
    }
    // Output digest is the public statement.
    true
}

pub fn prove_lde_leaf(row: &[Mersenne31]) -> Result<Keccak256StarkProof, String> {
    if row.len() != AGG_WIDTH {
        return Err("LDE row width mismatch".into());
    }
    prove_keccak256(&lde_row_to_bytes(row))
}

/// Prove ValMmcs leaf hash for an arbitrary-width M31 row (must be a supported byte length).
pub fn prove_val_leaf(row: &[Mersenne31]) -> Result<Keccak256StarkProof, String> {
    let bytes = val_row_to_bytes(row);
    if !supported_msg_len(bytes.len()) {
        return Err(format!(
            "unsupported val leaf width {} (bytes {})",
            row.len(),
            bytes.len()
        ));
    }
    prove_keccak256(&bytes)
}

pub fn verify_lde_leaf(row: &[Mersenne31], proof: &Keccak256StarkProof) -> bool {
    if row.len() != AGG_WIDTH {
        return false;
    }
    verify_keccak256(&lde_row_to_bytes(row), proof)
}

pub fn verify_val_leaf(row: &[Mersenne31], proof: &Keccak256StarkProof) -> bool {
    verify_keccak256(&val_row_to_bytes(row), proof)
}

/// Compress verify that also checks the claimed digest equals `expected`.
pub fn verify_compress_digest(
    left: [u8; 32],
    right: [u8; 32],
    expected: &[u8; 32],
    proof: &Keccak256StarkProof,
) -> bool {
    if &proof.digest != expected {
        eprintln!("[Keccak256] compress digest mismatch");
        return false;
    }
    verify_compress(left, right, proof)
}

pub fn verify_lde_leaf_digest(
    row: &[Mersenne31],
    expected: &[u8; 32],
    proof: &Keccak256StarkProof,
) -> bool {
    if &proof.digest != expected {
        eprintln!("[Keccak256] leaf digest mismatch");
        return false;
    }
    verify_lde_leaf(row, proof)
}

pub fn verify_val_leaf_digest(
    row: &[Mersenne31],
    expected: &[u8; 32],
    proof: &Keccak256StarkProof,
) -> bool {
    if &proof.digest != expected {
        eprintln!("[Keccak256] val leaf digest mismatch");
        return false;
    }
    verify_val_leaf(row, proof)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sponge_matrix_constraints_compress() {
        let msg = [9u8; 64];
        let digest = keccak256(&msg);
        let air = Keccak256SpongeAir::compress();
        let matrix = build_sponge_matrix(&msg);
        let pv = build_public_values(&msg, &digest);
        p3_air::check_constraints(&air, &matrix, &pv);
    }

    #[test]
    fn sponge_matrix_constraints_leaf() {
        let msg = [3u8; 264];
        let digest = keccak256(&msg);
        let air = Keccak256SpongeAir::leaf();
        let matrix = build_sponge_matrix(&msg);
        let pv = build_public_values(&msg, &digest);
        p3_air::check_constraints(&air, &matrix, &pv);
    }

    #[test]
    fn prove_verify_compress_roundtrip() {
        let left = [1u8; 32];
        let right = [2u8; 32];
        let proof = prove_compress(left, right).expect("prove");
        assert!(verify_compress_digest(left, right, &proof.digest, &proof));
        assert_eq!(
            proof.digest,
            keccak256(&{
                let mut m = [0u8; 64];
                m[..32].copy_from_slice(&left);
                m[32..].copy_from_slice(&right);
                m
            })
        );
    }
}

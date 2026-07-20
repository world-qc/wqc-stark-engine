//! Native DEEP reduced-opening helpers (R3-M3c1).
//!
//! Mirrors Circle PCS `deep_quotient_reduce_row` + λ correction used by
//! [`super::fri_ro`].

use p3_field::{Field, PrimeCharacteristicRing};

use crate::plonky3_stark::config::{Challenge, Val};

use super::fri_fold_native::point_v_n;

/// Projective-line → circle point over Challenge (mirrors `Point::from_projective_line`).
pub fn ef_from_projective_line(t: Challenge) -> (Challenge, Challenge) {
    let t2 = t.square();
    let inv_denom = (Challenge::ONE + t2).try_inverse().expect("t^2 = -1");
    ((Challenge::ONE - t2) * inv_denom, t.double() * inv_denom)
}

/// `Point::v_p` for base point `(sx,sy)` at extension point `at`.
pub fn v_p(sx: Val, sy: Val, at_x: Challenge, at_y: Challenge) -> (Challenge, Challenge) {
    // diff = -at + self  (Neg flips y; Add is complex multiply)
    let neg_at_x = at_x;
    let neg_at_y = -at_y;
    let diff_x = neg_at_x * Challenge::from(sx) - neg_at_y * Challenge::from(sy);
    let diff_y = neg_at_x * Challenge::from(sy) + neg_at_y * Challenge::from(sx);
    (Challenge::ONE - diff_x, -diff_y)
}

/// Circle PCS DEEP row reduction at one evaluation point.
pub fn deep_quotient_reduce_row(
    alpha: Challenge,
    sx: Val,
    sy: Val,
    zeta: Challenge,
    ps_at_x: &[Val],
    ps_at_zeta: &[Challenge],
) -> Challenge {
    let (at_x, at_y) = ef_from_projective_line(zeta);
    let alpha_pow_width = alpha.exp_u64(ps_at_x.len() as u64);
    let (re_v_zeta, im_v_zeta) = v_p(sx, sy, at_x, at_y);
    let numerator = re_v_zeta - alpha_pow_width * im_v_zeta;
    let denominator = re_v_zeta.square() + im_v_zeta.square();
    let mut constraint = Challenge::ZERO;
    let mut a = Challenge::ONE;
    for (&px, &pz) in ps_at_x.iter().zip(ps_at_zeta.iter()) {
        constraint += a * (Challenge::from(px) - pz);
        a *= alpha;
    }
    (numerator / denominator) * constraint
}

/// λ correction: `ro - λ · v_n(x)`.
#[cfg(test)]
fn lambda_correct(ro: Challenge, lambda: Challenge, sx: Val, log_n: usize) -> Challenge {
    ro - lambda * Challenge::from(point_v_n(sx, log_n))
}

/// Intermediate witnesses for DeepRoAir publics (W=3).
#[derive(Debug, Clone)]
pub struct DeepRoW3Witness {
    pub at_x: Challenge,
    pub at_y: Challenge,
    pub alpha2: Challenge,
    pub alpha3: Challenge,
    pub re: Challenge,
    pub im: Challenge,
    pub numer: Challenge,
    pub denom: Challenge,
    pub linear: Challenge,
    pub out_pre: Challenge,
    pub v_n: Val,
    pub out: Challenge,
}

/// Builds intermediate witnesses matching DeepRoAir constraints for W=3.
#[allow(clippy::too_many_arguments)]
pub fn deep_ro_w3_witness(
    alpha: Challenge,
    sx: Val,
    sy: Val,
    zeta: Challenge,
    px: [Val; 3],
    pz: [Challenge; 3],
    lambda: Challenge,
    log_n: usize,
) -> DeepRoW3Witness {
    let (at_x, at_y) = ef_from_projective_line(zeta);
    let alpha2 = alpha.square();
    let alpha3 = alpha2 * alpha;
    let (re, im) = v_p(sx, sy, at_x, at_y);
    let numer = re - alpha3 * im;
    let denom = re.square() + im.square();
    let c0 = Challenge::from(px[0]) - pz[0];
    let c1 = Challenge::from(px[1]) - pz[1];
    let c2 = Challenge::from(px[2]) - pz[2];
    let linear = c0 + alpha * c1 + alpha2 * c2;
    let out_pre = (numer / denom) * linear;
    let v_n = point_v_n(sx, log_n);
    let out = out_pre - lambda * Challenge::from(v_n);
    DeepRoW3Witness {
        at_x,
        at_y,
        alpha2,
        alpha3,
        re,
        im,
        numer,
        denom,
        linear,
        out_pre,
        v_n,
        out,
    }
}

/// One deep reduction's intermediates (shared by W=3 and W=66 paths).
#[derive(Debug, Clone)]
pub struct DeepPartialWitness {
    pub re: Challenge,
    pub im: Challenge,
    pub numer: Challenge,
    pub denom: Challenge,
    pub linear: Challenge,
    pub out_pre: Challenge,
}

#[allow(clippy::too_many_arguments)]
fn deep_partial(
    alpha: Challenge,
    sx: Val,
    sy: Val,
    at_x: Challenge,
    at_y: Challenge,
    alpha_pow_w: Challenge,
    px: &[Val],
    pz: &[Challenge],
) -> DeepPartialWitness {
    let (re, im) = v_p(sx, sy, at_x, at_y);
    let numer = re - alpha_pow_w * im;
    let denom = re.square() + im.square();
    let mut linear = Challenge::ZERO;
    let mut a = Challenge::ONE;
    for (&p_x, &p_z) in px.iter().zip(pz.iter()) {
        linear += a * (Challenge::from(p_x) - p_z);
        a *= alpha;
    }
    let out_pre = (numer / denom) * linear;
    DeepPartialWitness {
        re,
        im,
        numer,
        denom,
        linear,
        out_pre,
    }
}

/// Trace-batch DEEP + λ witness (W=66 @ ζ and ζ_next).
#[derive(Debug, Clone)]
pub struct DeepRoTraceWitness {
    pub at_x: Challenge,
    pub at_y: Challenge,
    pub atn_x: Challenge,
    pub atn_y: Challenge,
    pub alpha2: Challenge,
    pub alpha4: Challenge,
    pub alpha8: Challenge,
    pub alpha16: Challenge,
    pub alpha32: Challenge,
    pub alpha64: Challenge,
    pub alpha66: Challenge,
    pub alpha132: Challenge,
    pub deep0: DeepPartialWitness,
    pub deep1: DeepPartialWitness,
    pub combined: Challenge,
    pub v_n: Val,
    pub out: Challenge,
}

/// Variable-width leaf DeepRo + λ witness (pad-ready; uses actual `px.len()`).
#[derive(Debug, Clone)]
pub struct DeepRoLeafTraceWitness {
    pub at_x: Challenge,
    pub at_y: Challenge,
    pub atn_x: Challenge,
    pub atn_y: Challenge,
    pub alpha_w: Challenge,
    pub alpha_w2: Challenge,
    pub deep0: DeepPartialWitness,
    pub deep1: DeepPartialWitness,
    pub combined: Challenge,
    pub v_n: Val,
    pub out: Challenge,
}

/// Builds intermediates for leaf DeepRoTrace (any width in `1..=LEAF_DEEP_RO_MAX_WIDTH`).
#[allow(clippy::too_many_arguments)]
pub fn deep_ro_leaf_trace_witness(
    alpha: Challenge,
    sx: Val,
    sy: Val,
    zeta: Challenge,
    zeta_next: Challenge,
    px: &[Val],
    pz_local: &[Challenge],
    pz_next: &[Challenge],
    lambda: Challenge,
    log_n: usize,
) -> Result<DeepRoLeafTraceWitness, String> {
    let w = px.len();
    if w == 0 || w > super::pcs_geom::LEAF_DEEP_RO_MAX_WIDTH {
        return Err(format!(
            "leaf deep_ro width {w} out of 1..={}",
            super::pcs_geom::LEAF_DEEP_RO_MAX_WIDTH
        ));
    }
    if pz_local.len() != w || pz_next.len() != w {
        return Err("leaf deep_ro pz width mismatch".into());
    }
    let (at_x, at_y) = ef_from_projective_line(zeta);
    let (atn_x, atn_y) = ef_from_projective_line(zeta_next);
    let alpha_w = alpha.exp_u64(w as u64);
    let alpha_w2 = alpha_w.square();
    let deep0 = deep_partial(alpha, sx, sy, at_x, at_y, alpha_w, px, pz_local);
    let deep1 = deep_partial(alpha, sx, sy, atn_x, atn_y, alpha_w, px, pz_next);
    let combined = deep0.out_pre + alpha_w2 * deep1.out_pre;
    let v_n = point_v_n(sx, log_n);
    let out = combined - lambda * Challenge::from(v_n);
    Ok(DeepRoLeafTraceWitness {
        at_x,
        at_y,
        atn_x,
        atn_y,
        alpha_w,
        alpha_w2,
        deep0,
        deep1,
        combined,
        v_n,
        out,
    })
}

/// Builds intermediates for DeepRoTraceAir (AggregationAir width 66).
#[allow(clippy::too_many_arguments)]
pub fn deep_ro_trace_witness(
    alpha: Challenge,
    sx: Val,
    sy: Val,
    zeta: Challenge,
    zeta_next: Challenge,
    px: &[Val; 66],
    pz_local: &[Challenge; 66],
    pz_next: &[Challenge; 66],
    lambda: Challenge,
    log_n: usize,
) -> DeepRoTraceWitness {
    let leaf = deep_ro_leaf_trace_witness(
        alpha,
        sx,
        sy,
        zeta,
        zeta_next,
        px.as_slice(),
        pz_local.as_slice(),
        pz_next.as_slice(),
        lambda,
        log_n,
    )
    .expect("W=66 is in range");
    let alpha2 = alpha.square();
    let alpha4 = alpha2.square();
    let alpha8 = alpha4.square();
    let alpha16 = alpha8.square();
    let alpha32 = alpha16.square();
    let alpha64 = alpha32.square();
    DeepRoTraceWitness {
        at_x: leaf.at_x,
        at_y: leaf.at_y,
        atn_x: leaf.atn_x,
        atn_y: leaf.atn_y,
        alpha2,
        alpha4,
        alpha8,
        alpha16,
        alpha32,
        alpha64,
        alpha66: leaf.alpha_w,
        alpha132: leaf.alpha_w2,
        deep0: leaf.deep0,
        deep1: leaf.deep1,
        combined: leaf.combined,
        v_n: leaf.v_n,
        out: leaf.out,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_field::PrimeCharacteristicRing;
    use rand::{Rng, SeedableRng};

    #[test]
    fn deep_ro_w3_matches_reduce_plus_lambda() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let alpha = Challenge::new([
            Val::from_u32(rng.gen()),
            Val::from_u32(rng.gen()),
            Val::from_u32(rng.gen()),
        ]);
        let zeta = Challenge::new([
            Val::from_u32(rng.gen()),
            Val::from_u32(rng.gen()),
            Val::from_u32(rng.gen()),
        ]);
        let sx = Val::from_u32(3);
        let sy = Val::from_u32(5);
        let px = [Val::from_u32(1), Val::from_u32(2), Val::from_u32(3)];
        let pz = [
            Challenge::new([Val::ONE, Val::ZERO, Val::ZERO]),
            Challenge::new([Val::ZERO, Val::ONE, Val::ZERO]),
            Challenge::new([Val::ZERO, Val::ZERO, Val::ONE]),
        ];
        let lambda = Challenge::new([Val::from_u32(7), Val::from_u32(8), Val::from_u32(9)]);
        let log_n = 2usize;
        let w = deep_ro_w3_witness(alpha, sx, sy, zeta, px, pz, lambda, log_n);
        let expect = {
            let ro = deep_quotient_reduce_row(alpha, sx, sy, zeta, &px, &pz);
            lambda_correct(ro, lambda, sx, log_n)
        };
        assert_eq!(w.out, expect);
    }

    #[test]
    fn deep_ro_trace_matches_fri_ro_formula() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(99);
        let alpha = Challenge::new([
            Val::from_u32(rng.gen()),
            Val::from_u32(rng.gen()),
            Val::from_u32(rng.gen()),
        ]);
        let zeta = Challenge::new([
            Val::from_u32(rng.gen()),
            Val::from_u32(rng.gen()),
            Val::from_u32(rng.gen()),
        ]);
        let zeta_next = Challenge::new([
            Val::from_u32(rng.gen()),
            Val::from_u32(rng.gen()),
            Val::from_u32(rng.gen()),
        ]);
        let sx = Val::from_u32(3);
        let sy = Val::from_u32(5);
        let mut px = [Val::ZERO; 66];
        let mut pz_local = [Challenge::ZERO; 66];
        let mut pz_next = [Challenge::ZERO; 66];
        for i in 0..66 {
            px[i] = Val::from_u32(rng.gen::<u32>() % 100);
            pz_local[i] = Challenge::from(Val::from_u32(rng.gen::<u32>() % 100));
            pz_next[i] = Challenge::from(Val::from_u32(rng.gen::<u32>() % 100));
        }
        let lambda = Challenge::new([Val::from_u32(1), Val::from_u32(2), Val::from_u32(3)]);
        let log_n = 3usize;
        let w = deep_ro_trace_witness(
            alpha, sx, sy, zeta, zeta_next, &px, &pz_local, &pz_next, lambda, log_n,
        );
        let ro0 = deep_quotient_reduce_row(alpha, sx, sy, zeta, &px, &pz_local);
        let ro1 = deep_quotient_reduce_row(alpha, sx, sy, zeta_next, &px, &pz_next);
        let alpha132 = alpha.exp_u64(66).square();
        let expect = ro0 + alpha132 * ro1 - lambda * Challenge::from(point_v_n(sx, log_n));
        assert_eq!(w.out, expect);
        assert_eq!(w.deep0.out_pre, ro0);
        assert_eq!(w.deep1.out_pre, ro1);
    }
}

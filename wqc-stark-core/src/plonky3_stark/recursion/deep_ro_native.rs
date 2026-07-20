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
}

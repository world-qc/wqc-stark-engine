//! Host-side overlap check: site-order env contraction binds claimed MPS tensors → amplitude.
//!
//! This is host f64 re-contraction, not field arithmetic. Tensor entries stay at their
//! published f64 values (no M31 snap). The published amplitude uses the 1e-6 grid.

use crate::overlap::{OverlapSegment, OverlapSiteTensor, OVERLAP_ENV_LIMIT, OVERLAP_MAX_BOND};

/// Absolute tolerance vs the published amplitude (1e-6 grid). A few grid steps.
pub const OVERLAP_AMP_EPSILON: f64 = 5e-6;

fn site_shape_ok(site: &OverlapSiteTensor) -> bool {
    let left = site.left_dim as usize;
    let right = site.right_dim as usize;
    if left == 0 || right == 0 || left > OVERLAP_MAX_BOND || right > OVERLAP_MAX_BOND {
        return false;
    }
    site.values.len() == left * 2 * right
}

fn get_site(site: &OverlapSiteTensor, left: usize, phys: usize, right: usize) -> (f64, f64) {
    let r = site.right_dim as usize;
    let idx = (left * 2 + phys) * r + right;
    site.values[idx]
}

fn cmul(a: (f64, f64), b: (f64, f64)) -> (f64, f64) {
    (a.0 * b.0 - a.1 * b.1, a.0 * b.1 + a.1 * b.0)
}

fn cadd(a: (f64, f64), b: (f64, f64)) -> (f64, f64) {
    (a.0 + b.0, a.1 + b.1)
}

fn cconj(a: (f64, f64)) -> (f64, f64) {
    (a.0, -a.1)
}

/// Contract one site: `E' = contract(E, ket, conj(bra))` in host f64.
fn contract_site(
    env: &[(f64, f64)],
    ket: &OverlapSiteTensor,
    bra: &OverlapSiteTensor,
    ket_left: usize,
    bra_left: usize,
) -> Result<Vec<(f64, f64)>, String> {
    let k_left = ket.left_dim as usize;
    let k_right = ket.right_dim as usize;
    let b_left = bra.left_dim as usize;
    let b_right = bra.right_dim as usize;
    if k_left != ket_left || b_left != bra_left {
        return Err("overlap site left bond does not match env".into());
    }
    if env.len() != ket_left * bra_left {
        return Err("overlap env length mismatch".into());
    }
    let env_dim = k_right.saturating_mul(b_right);
    if env_dim == 0 || env_dim > OVERLAP_ENV_LIMIT {
        return Err("overlap environment exceeds limit".into());
    }
    let mut next = vec![(0.0, 0.0); env_dim];
    for a in 0..k_left {
        for b in 0..b_left {
            let coeff = env[a * bra_left + b];
            if coeff.0 == 0.0 && coeff.1 == 0.0 {
                continue;
            }
            for s in 0..2 {
                for a_right in 0..k_right {
                    let kv = cmul(coeff, get_site(ket, a, s, a_right));
                    if kv.0 == 0.0 && kv.1 == 0.0 {
                        continue;
                    }
                    for b_out in 0..b_right {
                        let term = cmul(kv, cconj(get_site(bra, b, s, b_out)));
                        let idx = a_right * b_right + b_out;
                        next[idx] = cadd(next[idx], term);
                    }
                }
            }
        }
    }
    Ok(next)
}

/// Reason the overlap check fails. `None` when constraints hold.
pub fn overlap_constraint_failure(segment: &OverlapSegment) -> Option<(u32, String)> {
    let n = segment.qubit_count as usize;
    if n == 0 {
        return Some((1, "qubit_count is zero".into()));
    }
    if segment.ket_sites.len() != n || segment.bra_sites.len() != n {
        return Some((2, "site count does not match qubit_count".into()));
    }
    for site in segment.ket_sites.iter().chain(segment.bra_sites.iter()) {
        if !site_shape_ok(site) {
            return Some((3, "invalid site tensor shape or bond".into()));
        }
    }

    // Open bonds start at 1.
    if segment.ket_sites[0].left_dim != 1 || segment.bra_sites[0].left_dim != 1 {
        return Some((4, "open left bonds must start at 1".into()));
    }
    let last = n - 1;
    if segment.ket_sites[last].right_dim != 1 || segment.bra_sites[last].right_dim != 1 {
        return Some((5, "open right bonds must end at 1".into()));
    }

    let mut env = vec![(1.0, 0.0)];
    let mut ket_left = 1usize;
    let mut bra_left = 1usize;
    for site in 0..n {
        let ket = &segment.ket_sites[site];
        let bra = &segment.bra_sites[site];
        match contract_site(&env, ket, bra, ket_left, bra_left) {
            Ok(next) => {
                ket_left = ket.right_dim as usize;
                bra_left = bra.right_dim as usize;
                env = next;
            }
            Err(msg) => return Some((6, msg)),
        }
    }
    if env.len() != 1 {
        return Some((7, "overlap left an open bond".into()));
    }

    let claimed_re = segment.amplitude_re;
    let claimed_im = segment.amplitude_im;
    let (env_re, env_im) = env[0];
    if (claimed_re - env_re).abs() > OVERLAP_AMP_EPSILON
        || (claimed_im - env_im).abs() > OVERLAP_AMP_EPSILON
    {
        return Some((
            8,
            format!(
                "final env ({env_re},{env_im}) does not match claimed amplitude ({claimed_re},{claimed_im})"
            ),
        ));
    }
    None
}

/// Returns `0` when overlap constraints hold; nonzero error code otherwise.
pub fn evaluate_overlap_constraint_sum(segment: &OverlapSegment) -> u32 {
    match overlap_constraint_failure(segment) {
        None => 0,
        Some((code, _)) => code,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::overlap::{calculate_amplitude_digest, OverlapSegment, OverlapSiteTensor};

    fn product_one_site(amp0: (f64, f64), amp1: (f64, f64)) -> OverlapSiteTensor {
        OverlapSiteTensor {
            left_dim: 1,
            right_dim: 1,
            values: vec![amp0, amp1],
        }
    }

    #[test]
    fn bond1_h_ket_bra_overlap_is_one() {
        // |+⟩ = H|0⟩; ⟨+|+\rangle = 1 with identical ket/bra product tensors.
        let s = 1.0 / 2.0f64.sqrt();
        let site = product_one_site((s, 0.0), (s, 0.0));
        let amp_re = 1.0;
        let amp_im = 0.0;
        let segment = OverlapSegment {
            qubit_count: 1,
            amplitude_re: amp_re,
            amplitude_im: amp_im,
            amplitude_digest: calculate_amplitude_digest(amp_re, amp_im),
            ket_sites: vec![site.clone()],
            bra_sites: vec![site],
        };
        assert_eq!(evaluate_overlap_constraint_sum(&segment), 0);
    }

    #[test]
    fn bond1_tampered_amplitude_fails() {
        let site = product_one_site((1.0, 0.0), (0.0, 0.0));
        let segment = OverlapSegment {
            qubit_count: 1,
            amplitude_re: 0.5,
            amplitude_im: 0.0,
            amplitude_digest: calculate_amplitude_digest(0.5, 0.0),
            ket_sites: vec![site.clone()],
            bra_sites: vec![site],
        };
        assert_ne!(evaluate_overlap_constraint_sum(&segment), 0);
    }

    #[test]
    fn near_1e4_grid_boundary_amplitude_accepts() {
        // Regression: M31 1e-4 snap + 1e-5 eps rejected honest amps like 0.946027.
        let amp: f64 = 0.946027;
        let site = product_one_site((amp.sqrt(), 0.0), (0.0, 0.0));
        let claimed = (amp * 1e6).round() / 1e6;
        let segment = OverlapSegment {
            qubit_count: 1,
            amplitude_re: claimed,
            amplitude_im: 0.0,
            amplitude_digest: calculate_amplitude_digest(claimed, 0.0),
            ket_sites: vec![site.clone()],
            bra_sites: vec![site],
        };
        assert_eq!(
            evaluate_overlap_constraint_sum(&segment),
            0,
            "claimed {claimed}"
        );
    }
}

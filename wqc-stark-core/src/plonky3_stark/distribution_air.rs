//! Plonky3 `Air` for C2b/C2c Born-rule zk binding (streaming, fixed-width).
//!
//! One active row per computational-basis amplitude. Accumulators fold `|ψ|²` into
//! each outcome bucket so qubit width no longer explodes the AIR column count
//! (`O(num_outcomes)` instead of `O(2^n)`).

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_field::{Field, PrimeCharacteristicRing};

/// Maximum qubit width for Plonky3 Born / marginal zk (matches algebraic `BORN_AIR_MAX_QUBITS`).
pub const BORN_ZK_MAX_QUBITS: usize = 16;

/// Soft cap on distinct outcomes encoded as one-hot + mass + claim columns.
pub const BORN_ZK_MAX_OUTCOMES: usize = 64;

/// Max trace width W for R3 in-circuit ValMmcs Keccak (≤ 2× rate = 272 bytes = 68 M31).
pub const BORN_RECURSION_MAX_TRACE_WIDTH: usize = 68;
/// Max outcome buckets K with W = 2 + 3K + 1 ≤ [`BORN_RECURSION_MAX_TRACE_WIDTH`].
pub const BORN_RECURSION_MAX_OUTCOMES: usize = (BORN_RECURSION_MAX_TRACE_WIDTH - 3) / 3;

/// DistributionAir trace width for K outcome buckets.
pub fn born_distribution_width(num_outcomes: usize) -> usize {
    2 + 3 * num_outcomes + 1
}

/// Inverse of [`born_distribution_width`] when W uses the Born layout.
pub fn born_num_outcomes_from_width(width: usize) -> Option<usize> {
    if width < 3 || !(width - 3).is_multiple_of(3) {
        return None;
    }
    Some((width - 3) / 3)
}

/// True when K is valid for R3 leaf PCS (in-circuit Keccak sponge over W M31 limbs).
pub fn born_recursion_outcomes_ok(num_outcomes: usize) -> bool {
    num_outcomes > 0 && born_distribution_width(num_outcomes) <= BORN_RECURSION_MAX_TRACE_WIDTH
}

pub fn validate_born_recursion_outcomes(num_outcomes: usize) -> Result<(), String> {
    if born_recursion_outcomes_ok(num_outcomes) {
        return Ok(());
    }
    Err(format!(
        "Born K={num_outcomes} exceeds recursion cap K≤{BORN_RECURSION_MAX_OUTCOMES} \
         (W=2+3K+1≤{BORN_RECURSION_MAX_TRACE_WIDTH} for in-circuit Keccak)"
    ))
}

pub fn validate_born_recursion_width(width: usize) -> Result<usize, String> {
    let k = born_num_outcomes_from_width(width)
        .ok_or_else(|| format!("invalid DistributionAir trace width {width}"))?;
    validate_born_recursion_outcomes(k)?;
    Ok(k)
}

/// Fixed-point scale — matches quantum execution AIR (`10_000`).
pub const BORN_ZK_SCALE: u32 = 10_000;

/// Column: real amplitude for this basis.
pub const COL_RE: usize = 0;
/// Column: imag amplitude for this basis.
pub const COL_IM: usize = 1;

/// Streaming Born AIR: `dim` active basis rows, `num_outcomes` probability buckets.
#[derive(Clone, Debug)]
pub struct DistributionAir {
    pub dim: usize,
    pub num_outcomes: usize,
}

impl DistributionAir {
    pub fn width(&self) -> usize {
        // re, im, sel[K], mass[K], claim[K], is_pad
        2 + 3 * self.num_outcomes + 1
    }

    pub fn col_sel(&self, k: usize) -> usize {
        2 + k
    }

    pub fn col_mass(&self, k: usize) -> usize {
        2 + self.num_outcomes + k
    }

    pub fn col_claim(&self, k: usize) -> usize {
        2 + 2 * self.num_outcomes + k
    }

    pub fn col_is_pad(&self) -> usize {
        2 + 3 * self.num_outcomes
    }

    /// Host-side check that an active row's local selectors / booleans look sane.
    pub fn evaluate_active_row_local<FR>(&self, row: &[FR]) -> FR
    where
        FR: Field + PrimeCharacteristicRing + Copy,
    {
        debug_assert_eq!(row.len(), self.width());
        let is_pad = row[self.col_is_pad()];
        let mut acc = is_pad * (is_pad - FR::ONE);
        let active = FR::ONE - is_pad;
        let mut sel_sum = FR::ZERO;
        for k in 0..self.num_outcomes {
            let sel = row[self.col_sel(k)];
            acc += active * sel * (sel - FR::ONE);
            sel_sum += sel;
        }
        acc += active * (sel_sum - FR::ONE);
        acc
    }
}

impl<F: Field> BaseAir<F> for DistributionAir {
    fn width(&self) -> usize {
        DistributionAir::width(self)
    }

    fn max_constraint_degree(&self) -> Option<usize> {
        // sel * (re² + im²) is degree 3.
        Some(6)
    }
}

impl<AB: AirBuilder> Air<AB> for DistributionAir
where
    AB::F: Field,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let curr = main.current_slice();
        let next = main.next_slice();
        debug_assert_eq!(curr.len(), self.width());

        let is_pad: AB::Expr = curr[self.col_is_pad()].into();
        let next_is_pad: AB::Expr = next[self.col_is_pad()].into();
        let active = AB::Expr::ONE - is_pad.clone();
        let next_active = AB::Expr::ONE - next_is_pad.clone();
        builder.assert_bool(curr[self.col_is_pad()]);

        let re: AB::Expr = curr[COL_RE].into();
        let im: AB::Expr = curr[COL_IM].into();
        let amp2 = re.clone() * re + im.clone() * im;
        let scale: AB::Expr = AB::F::from_u32(BORN_ZK_SCALE).into();

        let mut sel_sum = AB::Expr::ZERO;
        for k in 0..self.num_outcomes {
            let sel = curr[self.col_sel(k)];
            builder.when(active.clone()).assert_bool(sel);
            sel_sum += sel.into();
        }
        builder
            .when(active.clone())
            .assert_zero(sel_sum - AB::Expr::ONE);

        // First row: mass_k = sel_k * |amp|²
        for k in 0..self.num_outcomes {
            let mass: AB::Expr = curr[self.col_mass(k)].into();
            let sel: AB::Expr = curr[self.col_sel(k)].into();
            builder
                .when_first_row()
                .when(active.clone())
                .assert_zero(mass - sel * amp2.clone());
        }

        // Transitions.
        for k in 0..self.num_outcomes {
            let claim: AB::Expr = curr[self.col_claim(k)].into();
            let next_claim: AB::Expr = next[self.col_claim(k)].into();
            builder
                .when_transition()
                .assert_zero(next_claim - claim.clone());

            let mass: AB::Expr = curr[self.col_mass(k)].into();
            let next_mass: AB::Expr = next[self.col_mass(k)].into();
            let next_sel: AB::Expr = next[self.col_sel(k)].into();
            let next_re: AB::Expr = next[COL_RE].into();
            let next_im: AB::Expr = next[COL_IM].into();
            let next_amp2 = next_re.clone() * next_re + next_im.clone() * next_im;

            // Active → active: accumulate.
            builder
                .when_transition()
                .when(next_active.clone())
                .assert_zero(next_mass.clone() - mass.clone() - next_sel * next_amp2);

            // Any → pad: mass frozen (and finalised below when leaving active).
            builder
                .when_transition()
                .when(next_is_pad.clone())
                .assert_zero(next_mass - mass.clone());

            // Active → pad: final Born check.
            let entering_pad = next_is_pad.clone() * active.clone();
            builder
                .when_transition()
                .when(entering_pad)
                .assert_zero(mass.clone() - claim.clone() * scale.clone());
        }

        // No padding (height == dim power-of-two): last active row must match claims.
        for k in 0..self.num_outcomes {
            let mass: AB::Expr = curr[self.col_mass(k)].into();
            let claim: AB::Expr = curr[self.col_claim(k)].into();
            builder
                .when_last_row()
                .when(active.clone())
                .assert_zero(mass - claim * scale.clone());
        }

        // Pad rows: selectors and amplitudes zero.
        builder.when(is_pad.clone()).assert_zero(curr[COL_RE]);
        builder.when(is_pad.clone()).assert_zero(curr[COL_IM]);
        for k in 0..self.num_outcomes {
            builder
                .when(is_pad.clone())
                .assert_zero(curr[self.col_sel(k)]);
        }
    }
}

#[cfg(test)]
mod born_recursion_width_tests {
    use super::*;

    #[test]
    fn born_recursion_k21_fits_keccak_cap() {
        assert_eq!(BORN_RECURSION_MAX_OUTCOMES, 21);
        assert_eq!(born_distribution_width(21), 66);
        assert!(born_recursion_outcomes_ok(21));
        validate_born_recursion_outcomes(21).expect("K=21");
        validate_born_recursion_width(66).expect("W=66");
    }

    #[test]
    fn born_recursion_k22_exceeds_keccak_cap() {
        assert_eq!(born_distribution_width(22), 69);
        assert!(!born_recursion_outcomes_ok(22));
        assert!(validate_born_recursion_outcomes(22).is_err());
        assert!(validate_born_recursion_width(69).is_err());
    }
}

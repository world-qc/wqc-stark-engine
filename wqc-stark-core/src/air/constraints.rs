//! Shared quantum execution transition constraints (numeric and symbolic).

use p3_field::{Field, PrimeCharacteristicRing};
use p3_mersenne_31::Mersenne31;

/// One expanded AIR row parameterized over a ring type.
#[derive(Debug, Clone)]
pub struct AirRow<FR> {
    pub gate_type: FR,
    pub sel_x: FR,
    pub sel_y: FR,
    pub sel_z: FR,
    pub sel_h: FR,
    pub sel_s: FR,
    pub sel_t: FR,
    pub sel_ctrl: FR,
    pub sel_cz: FR,
    pub sel_ccnot: FR,
    pub sel_rot: FR,
    pub ctrl_active: FR,
    pub ctrl_active_2: FR,
    pub p_cos: FR,
    pub p_sin: FR,
    pub v0_re: FR,
    pub v0_im: FR,
    pub v1_re: FR,
    pub v1_im: FR,
    pub target_qubit: FR,
    pub transition_link: FR,
}

impl<FR: Copy> AirRow<FR> {
    pub fn from_columns(cols: &[FR]) -> Self {
        Self {
            gate_type: cols[0],
            sel_x: cols[1],
            sel_y: cols[2],
            sel_z: cols[3],
            sel_h: cols[4],
            sel_s: cols[5],
            sel_t: cols[6],
            sel_ctrl: cols[7],
            sel_cz: cols[8],
            sel_ccnot: cols[9],
            sel_rot: cols[10],
            ctrl_active: cols[11],
            ctrl_active_2: cols[12],
            p_cos: cols[13],
            p_sin: cols[14],
            v0_re: cols[15],
            v0_im: cols[16],
            v1_re: cols[17],
            v1_im: cols[18],
            target_qubit: cols[19],
            transition_link: cols[20],
        }
    }
}

/// Fixed-point constants used by Hadamard / rotation constraints.
#[derive(Clone)]
pub struct AirConstants<FR> {
    pub inv_sqrt2: FR,
    pub scale_factor: FR,
    pub scale_inverse: FR,
    pub two: FR,
    pub one: FR,
}

impl AirConstants<Mersenne31> {
    pub fn mersenne31_defaults() -> Self {
        let scale_factor = Mersenne31::new(10_000);
        Self {
            inv_sqrt2: Mersenne31::new(7071),
            scale_factor,
            scale_inverse: scale_factor.inverse(),
            two: Mersenne31::new(2),
            one: Mersenne31::ONE,
        }
    }
}

/// Accumulates transition constraints between adjacent AIR rows.
pub fn transition_accumulator<FR: Field>(
    constants: &AirConstants<FR>,
    curr: &AirRow<FR>,
    next: &AirRow<FR>,
) -> FR {
    let AirConstants {
        inv_sqrt2,
        scale_factor,
        scale_inverse,
        two,
        one,
    } = *constants;

    let v0_unchanged_re = next.v0_re - curr.v0_re;
    let v0_unchanged_im = next.v0_im - curr.v0_im;
    let v1_unchanged_re = next.v1_re - curr.v1_re;
    let v1_unchanged_im = next.v1_im - curr.v1_im;
    let identity_cost = v0_unchanged_re * v0_unchanged_re
        + v0_unchanged_im * v0_unchanged_im
        + v1_unchanged_re * v1_unchanged_re
        + v1_unchanged_im * v1_unchanged_im;

    let cost_x = (next.v0_re - curr.v1_re).square()
        + (next.v0_im - curr.v1_im).square()
        + (next.v1_re - curr.v0_re).square()
        + (next.v1_im - curr.v0_im).square();

    let cost_y = (next.v0_re - curr.v1_im).square()
        + (next.v0_im + curr.v1_re).square()
        + (next.v1_re + curr.v0_im).square()
        + (next.v1_im - curr.v0_re).square();

    let cost_z = (next.v0_re - curr.v0_re).square()
        + (next.v0_im - curr.v0_im).square()
        + (next.v1_re + curr.v1_re).square()
        + (next.v1_im + curr.v1_im).square();

    let h_0 = (next.v0_re * scale_factor) - (curr.v0_re + curr.v1_re) * inv_sqrt2;
    let h_1 = (next.v0_im * scale_factor) - (curr.v0_im + curr.v1_im) * inv_sqrt2;
    let h_2 = (next.v1_re * scale_factor) - (curr.v0_re - curr.v1_re) * inv_sqrt2;
    let h_3 = (next.v1_im * scale_factor) - (curr.v0_im - curr.v1_im) * inv_sqrt2;
    let cost_h = (h_0 * scale_inverse).square()
        + (h_1 * scale_inverse).square()
        + (h_2 * scale_inverse).square()
        + (h_3 * scale_inverse).square();

    let cost_s = (next.v0_re - curr.v0_re).square()
        + (next.v0_im - curr.v0_im).square()
        + (next.v1_re + curr.v1_im).square()
        + (next.v1_im - curr.v1_re).square();

    let t_2 = (next.v1_re * scale_factor) - (curr.v1_re - curr.v1_im) * inv_sqrt2;
    let t_3 = (next.v1_im * scale_factor) - (curr.v1_re + curr.v1_im) * inv_sqrt2;
    let cost_t = (next.v0_re - curr.v0_re).square()
        + (next.v0_im - curr.v0_im).square()
        + (t_2 * scale_inverse).square()
        + (t_3 * scale_inverse).square();

    let ctrl_active = curr.ctrl_active;
    let ctrl_inactive = one - ctrl_active;
    let expected_c_v0_re = (ctrl_inactive * curr.v0_re) + (ctrl_active * curr.v1_re);
    let expected_c_v0_im = (ctrl_inactive * curr.v0_im) + (ctrl_active * curr.v1_im);
    let expected_c_v1_re = (ctrl_inactive * curr.v1_re) + (ctrl_active * curr.v0_re);
    let expected_c_v1_im = (ctrl_inactive * curr.v1_im) + (ctrl_active * curr.v0_im);
    let cost_ctrl = (next.v0_re - expected_c_v0_re).square()
        + (next.v0_im - expected_c_v0_im).square()
        + (next.v1_re - expected_c_v1_re).square()
        + (next.v1_im - expected_c_v1_im).square();

    let phase = one - (two * ctrl_active);
    let expected_cz_v1_re = curr.v1_re * phase;
    let expected_cz_v1_im = curr.v1_im * phase;
    let cost_cz = (next.v0_re - curr.v0_re).square()
        + (next.v0_im - curr.v0_im).square()
        + (next.v1_re - expected_cz_v1_re).square()
        + (next.v1_im - expected_cz_v1_im).square();

    let cc_active = curr.ctrl_active * curr.ctrl_active_2;
    let cc_inactive = one - cc_active;
    let expected_cc_v0_re = (cc_inactive * curr.v0_re) + (cc_active * curr.v1_re);
    let expected_cc_v0_im = (cc_inactive * curr.v0_im) + (cc_active * curr.v1_im);
    let expected_cc_v1_re = (cc_inactive * curr.v1_re) + (cc_active * curr.v0_re);
    let expected_cc_v1_im = (cc_inactive * curr.v1_im) + (cc_active * curr.v0_im);
    let cost_ccnot = (next.v0_re - expected_cc_v0_re).square()
        + (next.v0_im - expected_cc_v0_im).square()
        + (next.v1_re - expected_cc_v1_re).square()
        + (next.v1_im - expected_cc_v1_im).square();

    let rot_0 = (next.v0_re * scale_factor) - (curr.v0_re * curr.p_cos - curr.v1_re * curr.p_sin);
    let rot_1 = (next.v0_im * scale_factor) - (curr.v0_im * curr.p_cos - curr.v1_im * curr.p_sin);
    let rot_2 = (next.v1_re * scale_factor) - (curr.v1_re * curr.p_cos + curr.v0_re * curr.p_sin);
    let rot_3 = (next.v1_im * scale_factor) - (curr.v1_im * curr.p_cos + curr.v0_im * curr.p_sin);
    let cost_rot = (rot_0 * scale_inverse).square()
        + (rot_1 * scale_inverse).square()
        + (rot_2 * scale_inverse).square()
        + (rot_3 * scale_inverse).square();

    let gate_costs = curr.sel_x * cost_x
        + curr.sel_y * cost_y
        + curr.sel_z * cost_z
        + curr.sel_h * cost_h
        + curr.sel_s * cost_s
        + curr.sel_t * cost_t
        + curr.sel_ctrl * cost_ctrl
        + curr.sel_cz * cost_cz
        + curr.sel_ccnot * cost_ccnot
        + curr.sel_rot * cost_rot;

    let gate_active = curr.sel_x
        + curr.sel_y
        + curr.sel_z
        + curr.sel_h
        + curr.sel_s
        + curr.sel_t
        + curr.sel_ctrl
        + curr.sel_cz
        + curr.sel_ccnot
        + curr.sel_rot;

    // Amplitude columns are sampled on each row's target qubit. Cross-wire transitions
    // set `transition_link = 0` on the current row so gate / identity constraints are skipped.
    if curr.transition_link == FR::ZERO {
        return FR::ZERO;
    }

    gate_active * gate_costs + (one - gate_active) * identity_cost
}

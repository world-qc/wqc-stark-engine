//! Plonky3 `Air` implementation for the quantum execution matrix.

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_field::{Field, PrimeCharacteristicRing};

use crate::trace_spec::AIR_WIDTH;

/// Quantum execution AIR used by Plonky3 uni-STARK.
#[derive(Copy, Clone, Debug)]
pub struct QuantumExecutionAir;

impl<F: Field> BaseAir<F> for QuantumExecutionAir {
    fn width(&self) -> usize {
        AIR_WIDTH
    }

    fn max_constraint_degree(&self) -> Option<usize> {
        // Selector (deg 1) * amplitude squares (deg 2) * gate_active weight (deg 1).
        Some(8)
    }
}

/// Symbolic transition constraints using `Copy` trace vars (see `AirBuilder::Var`).
fn transition_constraint_expr<AB: AirBuilder>(
    curr: &[AB::Var],
    next: &[AB::Var],
) -> AB::Expr
where
    AB::F: Field,
{
    let inv_sqrt2: AB::Expr = AB::F::from_u32(7071).into();
    let scale_factor: AB::Expr = AB::F::from_u32(10_000).into();
    let scale_inverse: AB::Expr = AB::F::from_u32(10_000).inverse().into();
    let two: AB::Expr = AB::F::from_u32(2).into();
    let one = AB::Expr::ONE;

    let identity_cost = (next[15].into() - curr[15].into()).square()
        + (next[16].into() - curr[16].into()).square()
        + (next[17].into() - curr[17].into()).square()
        + (next[18].into() - curr[18].into()).square();

    let cost_x = (next[15].into() - curr[17].into()).square()
        + (next[16].into() - curr[18].into()).square()
        + (next[17].into() - curr[15].into()).square()
        + (next[18].into() - curr[16].into()).square();

    let cost_y = (next[15].into() - curr[18].into()).square()
        + (next[16].into() + curr[17].into()).square()
        + (next[17].into() + curr[16].into()).square()
        + (next[18].into() - curr[15].into()).square();

    let cost_z = (next[15].into() - curr[15].into()).square()
        + (next[16].into() - curr[16].into()).square()
        + (next[17].into() + curr[17].into()).square()
        + (next[18].into() + curr[18].into()).square();

    let h_0 = (next[15].into() * scale_factor.clone())
        - (curr[15].into() + curr[17].into()) * inv_sqrt2.clone();
    let h_1 = (next[16].into() * scale_factor.clone())
        - (curr[16].into() + curr[18].into()) * inv_sqrt2.clone();
    let h_2 = (next[17].into() * scale_factor.clone())
        - (curr[15].into() - curr[17].into()) * inv_sqrt2.clone();
    let h_3 = (next[18].into() * scale_factor.clone())
        - (curr[16].into() - curr[18].into()) * inv_sqrt2.clone();
    let cost_h = (h_0 * scale_inverse.clone()).square()
        + (h_1 * scale_inverse.clone()).square()
        + (h_2 * scale_inverse.clone()).square()
        + (h_3 * scale_inverse.clone()).square();

    let cost_s = (next[15].into() - curr[15].into()).square()
        + (next[16].into() - curr[16].into()).square()
        + (next[17].into() + curr[18].into()).square()
        + (next[18].into() - curr[17].into()).square();

    let t_2 = (next[17].into() * scale_factor.clone())
        - (curr[17].into() - curr[18].into()) * inv_sqrt2.clone();
    let t_3 = (next[18].into() * scale_factor.clone())
        - (curr[17].into() + curr[18].into()) * inv_sqrt2.clone();
    let cost_t = (next[15].into() - curr[15].into()).square()
        + (next[16].into() - curr[16].into()).square()
        + (t_2 * scale_inverse.clone()).square()
        + (t_3 * scale_inverse.clone()).square();

    let ctrl_active = curr[11].into();
    let ctrl_inactive = one.clone() - ctrl_active.clone();
    let expected_c_v0_re =
        (ctrl_inactive.clone() * curr[15].into()) + (ctrl_active.clone() * curr[17].into());
    let expected_c_v0_im =
        (ctrl_inactive.clone() * curr[16].into()) + (ctrl_active.clone() * curr[18].into());
    let expected_c_v1_re =
        (ctrl_inactive.clone() * curr[17].into()) + (ctrl_active.clone() * curr[15].into());
    let expected_c_v1_im =
        (ctrl_inactive * curr[18].into()) + (ctrl_active * curr[16].into());
    let cost_ctrl = (next[15].into() - expected_c_v0_re).square()
        + (next[16].into() - expected_c_v0_im).square()
        + (next[17].into() - expected_c_v1_re).square()
        + (next[18].into() - expected_c_v1_im).square();

    let phase = one.clone() - (two.clone() * curr[11].into());
    let expected_cz_v1_re = curr[17].into() * phase.clone();
    let expected_cz_v1_im = curr[18].into() * phase;
    let cost_cz = (next[15].into() - curr[15].into()).square()
        + (next[16].into() - curr[16].into()).square()
        + (next[17].into() - expected_cz_v1_re).square()
        + (next[18].into() - expected_cz_v1_im).square();

    let cc_active = curr[11].into() * curr[12].into();
    let cc_inactive = one.clone() - cc_active.clone();
    let expected_cc_v0_re =
        (cc_inactive.clone() * curr[15].into()) + (cc_active.clone() * curr[17].into());
    let expected_cc_v0_im =
        (cc_inactive.clone() * curr[16].into()) + (cc_active.clone() * curr[18].into());
    let expected_cc_v1_re =
        (cc_inactive.clone() * curr[17].into()) + (cc_active.clone() * curr[15].into());
    let expected_cc_v1_im =
        (cc_inactive * curr[18].into()) + (cc_active * curr[16].into());
    let cost_ccnot = (next[15].into() - expected_cc_v0_re).square()
        + (next[16].into() - expected_cc_v0_im).square()
        + (next[17].into() - expected_cc_v1_re).square()
        + (next[18].into() - expected_cc_v1_im).square();

    let rot_0 = (next[15].into() * scale_factor.clone())
        - (curr[15].into() * curr[13].into() - curr[17].into() * curr[14].into());
    let rot_1 = (next[16].into() * scale_factor.clone())
        - (curr[16].into() * curr[13].into() - curr[18].into() * curr[14].into());
    let rot_2 = (next[17].into() * scale_factor.clone())
        - (curr[17].into() * curr[13].into() + curr[15].into() * curr[14].into());
    let rot_3 = (next[18].into() * scale_factor.clone())
        - (curr[18].into() * curr[13].into() + curr[16].into() * curr[14].into());
    let cost_rot = (rot_0 * scale_inverse.clone()).square()
        + (rot_1 * scale_inverse.clone()).square()
        + (rot_2 * scale_inverse.clone()).square()
        + (rot_3 * scale_inverse).square();

    let gate_costs = curr[1].into() * cost_x
        + curr[2].into() * cost_y
        + curr[3].into() * cost_z
        + curr[4].into() * cost_h
        + curr[5].into() * cost_s
        + curr[6].into() * cost_t
        + curr[7].into() * cost_ctrl
        + curr[8].into() * cost_cz
        + curr[9].into() * cost_ccnot
        + curr[10].into() * cost_rot;

    let gate_active = curr[1].into()
        + curr[2].into()
        + curr[3].into()
        + curr[4].into()
        + curr[5].into()
        + curr[6].into()
        + curr[7].into()
        + curr[8].into()
        + curr[9].into()
        + curr[10].into();

    gate_active.clone() * gate_costs + (one - gate_active) * identity_cost
}

impl<AB: AirBuilder> Air<AB> for QuantumExecutionAir
where
    AB::F: Field,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let curr = main.current_slice();
        let next = main.next_slice();
        debug_assert_eq!(curr.len(), AIR_WIDTH);
        debug_assert_eq!(next.len(), AIR_WIDTH);

        let acc = transition_constraint_expr::<AB>(curr, next);
        builder.when_transition().assert_zero(acc);
    }
}

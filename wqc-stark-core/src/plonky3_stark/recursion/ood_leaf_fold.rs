//! In-circuit OOD constraint fold for leaf AIRs (Unitary / Distribution / ShotSampling).

use p3_air::AirBuilder;
use p3_field::{Field, PrimeCharacteristicRing};

use crate::air::shot_sampling::{SHOT_SAMPLING_GAP_BITS, SHOT_SAMPLING_SCALE};
use crate::plonky3_stark::distribution_air::{
    DistributionAir, BORN_ZK_MAX_OUTCOMES, BORN_ZK_SCALE, COL_IM, COL_RE,
};
use crate::plonky3_stark::shot_sampling_air::{
    SHOT_SAMPLING_COL_GAP, SHOT_SAMPLING_COL_GAP_BITS, SHOT_SAMPLING_COL_IS_PAD,
    SHOT_SAMPLING_COL_OUTCOME, SHOT_SAMPLING_COL_P0, SHOT_SAMPLING_COL_P1, SHOT_SAMPLING_COL_U,
};
use crate::trace_spec::AIR_WIDTH;

use super::ef_limbs::{
    ef_add_limbs, ef_bool_check_limbs, ef_embed_base, ef_mul_limbs, ef_one, ef_square_limbs,
    ef_sub_limbs,
};

struct FoldAcc<AB: AirBuilder> {
    acc: [AB::Expr; 3],
    alpha: [AB::Expr; 3],
}

impl<AB: AirBuilder> FoldAcc<AB>
where
    AB::F: Field + PrimeCharacteristicRing,
    AB::Expr: Clone,
{
    fn new(alpha: &[AB::Expr; 3]) -> Self {
        Self {
            acc: ef_embed_base::<AB>(AB::Expr::ZERO),
            alpha: alpha.clone(),
        }
    }

    fn push(&mut self, selector: &[AB::Expr; 3], constraint: &[AB::Expr; 3]) {
        self.acc = ef_mul_limbs::<AB>(&self.acc, &self.alpha);
        self.acc = ef_add_limbs::<AB>(&self.acc, &ef_mul_limbs::<AB>(selector, constraint));
    }

    fn push_unfiltered(&mut self, constraint: &[AB::Expr; 3]) {
        self.push(&ef_one::<AB>(), constraint);
    }

    fn finish(self) -> [AB::Expr; 3] {
        self.acc
    }
}

fn col<AB: AirBuilder>(rows: &[[AB::Expr; 3]], i: usize) -> &[AB::Expr; 3] {
    &rows[i]
}

fn unitary_transition_cost<AB: AirBuilder>(
    local: &[[AB::Expr; 3]],
    next: &[[AB::Expr; 3]],
) -> [AB::Expr; 3]
where
    AB::F: Field + PrimeCharacteristicRing,
    AB::Expr: Clone,
{
    let inv_sqrt2 = ef_embed_base::<AB>(AB::F::from_u32(7071).into());
    let scale_factor = ef_embed_base::<AB>(AB::F::from_u32(10_000).into());
    let scale_inverse = ef_embed_base::<AB>(AB::F::from_u32(10_000).inverse().into());
    let two = ef_embed_base::<AB>(AB::F::from_u32(2).into());
    let one = ef_one::<AB>();

    let identity_cost = ef_add_limbs::<AB>(
        &ef_add_limbs::<AB>(
            &ef_square_limbs::<AB>(&ef_sub_limbs::<AB>(
                col::<AB>(next, 15),
                col::<AB>(local, 15),
            )),
            &ef_square_limbs::<AB>(&ef_sub_limbs::<AB>(
                col::<AB>(next, 16),
                col::<AB>(local, 16),
            )),
        ),
        &ef_add_limbs::<AB>(
            &ef_square_limbs::<AB>(&ef_sub_limbs::<AB>(
                col::<AB>(next, 17),
                col::<AB>(local, 17),
            )),
            &ef_square_limbs::<AB>(&ef_sub_limbs::<AB>(
                col::<AB>(next, 18),
                col::<AB>(local, 18),
            )),
        ),
    );

    let cost_x = ef_add_limbs::<AB>(
        &ef_add_limbs::<AB>(
            &ef_square_limbs::<AB>(&ef_sub_limbs::<AB>(
                col::<AB>(next, 15),
                col::<AB>(local, 17),
            )),
            &ef_square_limbs::<AB>(&ef_sub_limbs::<AB>(
                col::<AB>(next, 16),
                col::<AB>(local, 18),
            )),
        ),
        &ef_add_limbs::<AB>(
            &ef_square_limbs::<AB>(&ef_sub_limbs::<AB>(
                col::<AB>(next, 17),
                col::<AB>(local, 15),
            )),
            &ef_square_limbs::<AB>(&ef_sub_limbs::<AB>(
                col::<AB>(next, 18),
                col::<AB>(local, 16),
            )),
        ),
    );

    let cost_y = ef_add_limbs::<AB>(
        &ef_add_limbs::<AB>(
            &ef_square_limbs::<AB>(&ef_sub_limbs::<AB>(
                col::<AB>(next, 15),
                col::<AB>(local, 18),
            )),
            &ef_square_limbs::<AB>(&ef_add_limbs::<AB>(
                col::<AB>(next, 16),
                col::<AB>(local, 17),
            )),
        ),
        &ef_add_limbs::<AB>(
            &ef_square_limbs::<AB>(&ef_add_limbs::<AB>(
                col::<AB>(next, 17),
                col::<AB>(local, 16),
            )),
            &ef_square_limbs::<AB>(&ef_sub_limbs::<AB>(
                col::<AB>(next, 18),
                col::<AB>(local, 15),
            )),
        ),
    );

    let cost_z = ef_add_limbs::<AB>(
        &ef_add_limbs::<AB>(
            &ef_square_limbs::<AB>(&ef_sub_limbs::<AB>(
                col::<AB>(next, 15),
                col::<AB>(local, 15),
            )),
            &ef_square_limbs::<AB>(&ef_sub_limbs::<AB>(
                col::<AB>(next, 16),
                col::<AB>(local, 16),
            )),
        ),
        &ef_add_limbs::<AB>(
            &ef_square_limbs::<AB>(&ef_add_limbs::<AB>(
                col::<AB>(next, 17),
                col::<AB>(local, 17),
            )),
            &ef_square_limbs::<AB>(&ef_add_limbs::<AB>(
                col::<AB>(next, 18),
                col::<AB>(local, 18),
            )),
        ),
    );

    let h_0 = ef_sub_limbs::<AB>(
        &ef_mul_limbs::<AB>(col::<AB>(next, 15), &scale_factor),
        &ef_mul_limbs::<AB>(
            &ef_add_limbs::<AB>(col::<AB>(local, 15), col::<AB>(local, 17)),
            &inv_sqrt2,
        ),
    );
    let h_1 = ef_sub_limbs::<AB>(
        &ef_mul_limbs::<AB>(col::<AB>(next, 16), &scale_factor),
        &ef_mul_limbs::<AB>(
            &ef_add_limbs::<AB>(col::<AB>(local, 16), col::<AB>(local, 18)),
            &inv_sqrt2,
        ),
    );
    let h_2 = ef_sub_limbs::<AB>(
        &ef_mul_limbs::<AB>(col::<AB>(next, 17), &scale_factor),
        &ef_mul_limbs::<AB>(
            &ef_sub_limbs::<AB>(col::<AB>(local, 15), col::<AB>(local, 17)),
            &inv_sqrt2,
        ),
    );
    let h_3 = ef_sub_limbs::<AB>(
        &ef_mul_limbs::<AB>(col::<AB>(next, 18), &scale_factor),
        &ef_mul_limbs::<AB>(
            &ef_sub_limbs::<AB>(col::<AB>(local, 16), col::<AB>(local, 18)),
            &inv_sqrt2,
        ),
    );
    let cost_h = ef_add_limbs::<AB>(
        &ef_add_limbs::<AB>(
            &ef_square_limbs::<AB>(&ef_mul_limbs::<AB>(&h_0, &scale_inverse)),
            &ef_square_limbs::<AB>(&ef_mul_limbs::<AB>(&h_1, &scale_inverse)),
        ),
        &ef_add_limbs::<AB>(
            &ef_square_limbs::<AB>(&ef_mul_limbs::<AB>(&h_2, &scale_inverse)),
            &ef_square_limbs::<AB>(&ef_mul_limbs::<AB>(&h_3, &scale_inverse)),
        ),
    );

    let cost_s = ef_add_limbs::<AB>(
        &ef_add_limbs::<AB>(
            &ef_square_limbs::<AB>(&ef_sub_limbs::<AB>(
                col::<AB>(next, 15),
                col::<AB>(local, 15),
            )),
            &ef_square_limbs::<AB>(&ef_sub_limbs::<AB>(
                col::<AB>(next, 16),
                col::<AB>(local, 16),
            )),
        ),
        &ef_add_limbs::<AB>(
            &ef_square_limbs::<AB>(&ef_add_limbs::<AB>(
                col::<AB>(next, 17),
                col::<AB>(local, 18),
            )),
            &ef_square_limbs::<AB>(&ef_sub_limbs::<AB>(
                col::<AB>(next, 18),
                col::<AB>(local, 17),
            )),
        ),
    );

    let t_2 = ef_sub_limbs::<AB>(
        &ef_mul_limbs::<AB>(col::<AB>(next, 17), &scale_factor),
        &ef_mul_limbs::<AB>(
            &ef_sub_limbs::<AB>(col::<AB>(local, 17), col::<AB>(local, 18)),
            &inv_sqrt2,
        ),
    );
    let t_3 = ef_sub_limbs::<AB>(
        &ef_mul_limbs::<AB>(col::<AB>(next, 18), &scale_factor),
        &ef_mul_limbs::<AB>(
            &ef_add_limbs::<AB>(col::<AB>(local, 17), col::<AB>(local, 18)),
            &inv_sqrt2,
        ),
    );
    let cost_t = ef_add_limbs::<AB>(
        &ef_add_limbs::<AB>(
            &ef_square_limbs::<AB>(&ef_sub_limbs::<AB>(
                col::<AB>(next, 15),
                col::<AB>(local, 15),
            )),
            &ef_square_limbs::<AB>(&ef_sub_limbs::<AB>(
                col::<AB>(next, 16),
                col::<AB>(local, 16),
            )),
        ),
        &ef_add_limbs::<AB>(
            &ef_square_limbs::<AB>(&ef_mul_limbs::<AB>(&t_2, &scale_inverse)),
            &ef_square_limbs::<AB>(&ef_mul_limbs::<AB>(&t_3, &scale_inverse)),
        ),
    );

    let ctrl_active = col::<AB>(local, 11);
    let ctrl_inactive = ef_sub_limbs::<AB>(&one, ctrl_active);
    let expected_c_v0_re = ef_add_limbs::<AB>(
        &ef_mul_limbs::<AB>(&ctrl_inactive, col::<AB>(local, 15)),
        &ef_mul_limbs::<AB>(ctrl_active, col::<AB>(local, 17)),
    );
    let expected_c_v0_im = ef_add_limbs::<AB>(
        &ef_mul_limbs::<AB>(&ctrl_inactive, col::<AB>(local, 16)),
        &ef_mul_limbs::<AB>(ctrl_active, col::<AB>(local, 18)),
    );
    let expected_c_v1_re = ef_add_limbs::<AB>(
        &ef_mul_limbs::<AB>(&ctrl_inactive, col::<AB>(local, 17)),
        &ef_mul_limbs::<AB>(ctrl_active, col::<AB>(local, 15)),
    );
    let expected_c_v1_im = ef_add_limbs::<AB>(
        &ef_mul_limbs::<AB>(&ctrl_inactive, col::<AB>(local, 18)),
        &ef_mul_limbs::<AB>(ctrl_active, col::<AB>(local, 16)),
    );
    let cost_ctrl = ef_add_limbs::<AB>(
        &ef_add_limbs::<AB>(
            &ef_square_limbs::<AB>(&ef_sub_limbs::<AB>(col::<AB>(next, 15), &expected_c_v0_re)),
            &ef_square_limbs::<AB>(&ef_sub_limbs::<AB>(col::<AB>(next, 16), &expected_c_v0_im)),
        ),
        &ef_add_limbs::<AB>(
            &ef_square_limbs::<AB>(&ef_sub_limbs::<AB>(col::<AB>(next, 17), &expected_c_v1_re)),
            &ef_square_limbs::<AB>(&ef_sub_limbs::<AB>(col::<AB>(next, 18), &expected_c_v1_im)),
        ),
    );

    let phase = ef_sub_limbs::<AB>(&one, &ef_mul_limbs::<AB>(&two, col::<AB>(local, 11)));
    let expected_cz_v1_re = ef_mul_limbs::<AB>(col::<AB>(local, 17), &phase);
    let expected_cz_v1_im = ef_mul_limbs::<AB>(col::<AB>(local, 18), &phase);
    let cost_cz = ef_add_limbs::<AB>(
        &ef_add_limbs::<AB>(
            &ef_square_limbs::<AB>(&ef_sub_limbs::<AB>(
                col::<AB>(next, 15),
                col::<AB>(local, 15),
            )),
            &ef_square_limbs::<AB>(&ef_sub_limbs::<AB>(
                col::<AB>(next, 16),
                col::<AB>(local, 16),
            )),
        ),
        &ef_add_limbs::<AB>(
            &ef_square_limbs::<AB>(&ef_sub_limbs::<AB>(col::<AB>(next, 17), &expected_cz_v1_re)),
            &ef_square_limbs::<AB>(&ef_sub_limbs::<AB>(col::<AB>(next, 18), &expected_cz_v1_im)),
        ),
    );

    let cc_active = ef_mul_limbs::<AB>(col::<AB>(local, 11), col::<AB>(local, 12));
    let cc_inactive = ef_sub_limbs::<AB>(&one, &cc_active);
    let expected_cc_v0_re = ef_add_limbs::<AB>(
        &ef_mul_limbs::<AB>(&cc_inactive, col::<AB>(local, 15)),
        &ef_mul_limbs::<AB>(&cc_active, col::<AB>(local, 17)),
    );
    let expected_cc_v0_im = ef_add_limbs::<AB>(
        &ef_mul_limbs::<AB>(&cc_inactive, col::<AB>(local, 16)),
        &ef_mul_limbs::<AB>(&cc_active, col::<AB>(local, 18)),
    );
    let expected_cc_v1_re = ef_add_limbs::<AB>(
        &ef_mul_limbs::<AB>(&cc_inactive, col::<AB>(local, 17)),
        &ef_mul_limbs::<AB>(&cc_active, col::<AB>(local, 15)),
    );
    let expected_cc_v1_im = ef_add_limbs::<AB>(
        &ef_mul_limbs::<AB>(&cc_inactive, col::<AB>(local, 18)),
        &ef_mul_limbs::<AB>(&cc_active, col::<AB>(local, 16)),
    );
    let cost_ccnot = ef_add_limbs::<AB>(
        &ef_add_limbs::<AB>(
            &ef_square_limbs::<AB>(&ef_sub_limbs::<AB>(col::<AB>(next, 15), &expected_cc_v0_re)),
            &ef_square_limbs::<AB>(&ef_sub_limbs::<AB>(col::<AB>(next, 16), &expected_cc_v0_im)),
        ),
        &ef_add_limbs::<AB>(
            &ef_square_limbs::<AB>(&ef_sub_limbs::<AB>(col::<AB>(next, 17), &expected_cc_v1_re)),
            &ef_square_limbs::<AB>(&ef_sub_limbs::<AB>(col::<AB>(next, 18), &expected_cc_v1_im)),
        ),
    );

    let rot_0 = ef_sub_limbs::<AB>(
        &ef_mul_limbs::<AB>(col::<AB>(next, 15), &scale_factor),
        &ef_sub_limbs::<AB>(
            &ef_mul_limbs::<AB>(col::<AB>(local, 15), col::<AB>(local, 13)),
            &ef_mul_limbs::<AB>(col::<AB>(local, 17), col::<AB>(local, 14)),
        ),
    );
    let rot_1 = ef_sub_limbs::<AB>(
        &ef_mul_limbs::<AB>(col::<AB>(next, 16), &scale_factor),
        &ef_sub_limbs::<AB>(
            &ef_mul_limbs::<AB>(col::<AB>(local, 16), col::<AB>(local, 13)),
            &ef_mul_limbs::<AB>(col::<AB>(local, 18), col::<AB>(local, 14)),
        ),
    );
    let rot_2 = ef_sub_limbs::<AB>(
        &ef_mul_limbs::<AB>(col::<AB>(next, 17), &scale_factor),
        &ef_add_limbs::<AB>(
            &ef_mul_limbs::<AB>(col::<AB>(local, 17), col::<AB>(local, 13)),
            &ef_mul_limbs::<AB>(col::<AB>(local, 15), col::<AB>(local, 14)),
        ),
    );
    let rot_3 = ef_sub_limbs::<AB>(
        &ef_mul_limbs::<AB>(col::<AB>(next, 18), &scale_factor),
        &ef_add_limbs::<AB>(
            &ef_mul_limbs::<AB>(col::<AB>(local, 18), col::<AB>(local, 13)),
            &ef_mul_limbs::<AB>(col::<AB>(local, 16), col::<AB>(local, 14)),
        ),
    );
    let cost_rot = ef_add_limbs::<AB>(
        &ef_add_limbs::<AB>(
            &ef_square_limbs::<AB>(&ef_mul_limbs::<AB>(&rot_0, &scale_inverse)),
            &ef_square_limbs::<AB>(&ef_mul_limbs::<AB>(&rot_1, &scale_inverse)),
        ),
        &ef_add_limbs::<AB>(
            &ef_square_limbs::<AB>(&ef_mul_limbs::<AB>(&rot_2, &scale_inverse)),
            &ef_square_limbs::<AB>(&ef_mul_limbs::<AB>(&rot_3, &scale_inverse)),
        ),
    );

    let gate_costs = ef_add_limbs::<AB>(
        &ef_add_limbs::<AB>(
            &ef_add_limbs::<AB>(
                &ef_mul_limbs::<AB>(col::<AB>(local, 1), &cost_x),
                &ef_mul_limbs::<AB>(col::<AB>(local, 2), &cost_y),
            ),
            &ef_add_limbs::<AB>(
                &ef_mul_limbs::<AB>(col::<AB>(local, 3), &cost_z),
                &ef_mul_limbs::<AB>(col::<AB>(local, 4), &cost_h),
            ),
        ),
        &ef_add_limbs::<AB>(
            &ef_add_limbs::<AB>(
                &ef_add_limbs::<AB>(
                    &ef_mul_limbs::<AB>(col::<AB>(local, 5), &cost_s),
                    &ef_mul_limbs::<AB>(col::<AB>(local, 6), &cost_t),
                ),
                &ef_add_limbs::<AB>(
                    &ef_mul_limbs::<AB>(col::<AB>(local, 7), &cost_ctrl),
                    &ef_mul_limbs::<AB>(col::<AB>(local, 8), &cost_cz),
                ),
            ),
            &ef_add_limbs::<AB>(
                &ef_mul_limbs::<AB>(col::<AB>(local, 9), &cost_ccnot),
                &ef_mul_limbs::<AB>(col::<AB>(local, 10), &cost_rot),
            ),
        ),
    );

    let gate_active = ef_add_limbs::<AB>(
        &ef_add_limbs::<AB>(
            &ef_add_limbs::<AB>(
                &ef_add_limbs::<AB>(col::<AB>(local, 1), col::<AB>(local, 2)),
                &ef_add_limbs::<AB>(col::<AB>(local, 3), col::<AB>(local, 4)),
            ),
            &ef_add_limbs::<AB>(
                &ef_add_limbs::<AB>(col::<AB>(local, 5), col::<AB>(local, 6)),
                &ef_add_limbs::<AB>(col::<AB>(local, 7), col::<AB>(local, 8)),
            ),
        ),
        &ef_add_limbs::<AB>(col::<AB>(local, 9), col::<AB>(local, 10)),
    );

    let full_cost = ef_add_limbs::<AB>(
        &ef_mul_limbs::<AB>(&gate_active, &gate_costs),
        &ef_mul_limbs::<AB>(&ef_sub_limbs::<AB>(&one, &gate_active), &identity_cost),
    );

    ef_mul_limbs::<AB>(&full_cost, col::<AB>(local, 20))
}

pub fn fold_unitary_in_circuit<AB: AirBuilder>(
    local: &[[AB::Expr; 3]],
    next: &[[AB::Expr; 3]],
    is_transition: &[AB::Expr; 3],
    alpha: &[AB::Expr; 3],
) -> [AB::Expr; 3]
where
    AB::F: Field + PrimeCharacteristicRing,
    AB::Expr: Clone,
{
    debug_assert_eq!(local.len(), AIR_WIDTH);
    debug_assert_eq!(next.len(), AIR_WIDTH);
    let mut folder = FoldAcc::<AB>::new(alpha);
    let cost = unitary_transition_cost::<AB>(local, next);
    folder.push(is_transition, &cost);
    folder.finish()
}

pub fn fold_distribution_in_circuit<AB: AirBuilder>(
    num_outcomes: usize,
    local: &[[AB::Expr; 3]],
    next: &[[AB::Expr; 3]],
    is_first_row: &[AB::Expr; 3],
    is_last_row: &[AB::Expr; 3],
    is_transition: &[AB::Expr; 3],
    alpha: &[AB::Expr; 3],
) -> [AB::Expr; 3]
where
    AB::F: Field + PrimeCharacteristicRing,
    AB::Expr: Clone,
{
    assert!(num_outcomes > 0 && num_outcomes <= BORN_ZK_MAX_OUTCOMES);
    let air = DistributionAir {
        dim: 1,
        num_outcomes,
    };
    debug_assert_eq!(local.len(), air.width());
    debug_assert_eq!(next.len(), air.width());

    let one = ef_one::<AB>();
    let scale = ef_embed_base::<AB>(AB::F::from_u32(BORN_ZK_SCALE).into());
    let is_pad = col::<AB>(local, air.col_is_pad());
    let next_is_pad = col::<AB>(next, air.col_is_pad());
    let active = ef_sub_limbs::<AB>(&one, is_pad);
    let next_active = ef_sub_limbs::<AB>(&one, next_is_pad);

    let re = col::<AB>(local, COL_RE);
    let im = col::<AB>(local, COL_IM);
    let amp2 = ef_add_limbs::<AB>(&ef_square_limbs::<AB>(re), &ef_square_limbs::<AB>(im));

    let mut folder = FoldAcc::<AB>::new(alpha);

    folder.push_unfiltered(&ef_bool_check_limbs::<AB>(is_pad));

    let mut sel_sum = ef_embed_base::<AB>(AB::Expr::ZERO);
    for k in 0..num_outcomes {
        let sel = col::<AB>(local, air.col_sel(k));
        folder.push(&active, &ef_bool_check_limbs::<AB>(sel));
        sel_sum = ef_add_limbs::<AB>(&sel_sum, sel);
    }
    folder.push(&active, &ef_sub_limbs::<AB>(&sel_sum, &one));

    for k in 0..num_outcomes {
        let mass = col::<AB>(local, air.col_mass(k));
        let sel = col::<AB>(local, air.col_sel(k));
        let c = ef_sub_limbs::<AB>(mass, &ef_mul_limbs::<AB>(sel, &amp2));
        let first_active = ef_mul_limbs::<AB>(is_first_row, &active);
        folder.push(&first_active, &c);
    }

    for k in 0..num_outcomes {
        let claim = col::<AB>(local, air.col_claim(k));
        let next_claim = col::<AB>(next, air.col_claim(k));
        folder.push(is_transition, &ef_sub_limbs::<AB>(next_claim, claim));

        let mass = col::<AB>(local, air.col_mass(k));
        let next_mass = col::<AB>(next, air.col_mass(k));
        let next_sel = col::<AB>(next, air.col_sel(k));
        let next_re = col::<AB>(next, COL_RE);
        let next_im = col::<AB>(next, COL_IM);
        let next_amp2 = ef_add_limbs::<AB>(
            &ef_square_limbs::<AB>(next_re),
            &ef_square_limbs::<AB>(next_im),
        );
        let trans_next_active = ef_mul_limbs::<AB>(is_transition, &next_active);
        folder.push(
            &trans_next_active,
            &ef_sub_limbs::<AB>(
                next_mass,
                &ef_add_limbs::<AB>(mass, &ef_mul_limbs::<AB>(next_sel, &next_amp2)),
            ),
        );
        let trans_next_pad = ef_mul_limbs::<AB>(is_transition, next_is_pad);
        folder.push(&trans_next_pad, &ef_sub_limbs::<AB>(next_mass, mass));

        let entering_pad = ef_mul_limbs::<AB>(next_is_pad, &active);
        let trans_enter = ef_mul_limbs::<AB>(is_transition, &entering_pad);
        folder.push(
            &trans_enter,
            &ef_sub_limbs::<AB>(mass, &ef_mul_limbs::<AB>(claim, &scale)),
        );
    }

    for k in 0..num_outcomes {
        let mass = col::<AB>(local, air.col_mass(k));
        let claim = col::<AB>(local, air.col_claim(k));
        let last_active = ef_mul_limbs::<AB>(is_last_row, &active);
        folder.push(
            &last_active,
            &ef_sub_limbs::<AB>(mass, &ef_mul_limbs::<AB>(claim, &scale)),
        );
    }

    folder.push(is_pad, col::<AB>(local, COL_RE));
    folder.push(is_pad, col::<AB>(local, COL_IM));
    for k in 0..num_outcomes {
        folder.push(is_pad, col::<AB>(local, air.col_sel(k)));
    }

    folder.finish()
}

pub fn fold_shot_sampling_in_circuit<AB: AirBuilder>(
    local: &[[AB::Expr; 3]],
    alpha: &[AB::Expr; 3],
) -> [AB::Expr; 3]
where
    AB::F: Field + PrimeCharacteristicRing,
    AB::Expr: Clone,
{
    let one = ef_one::<AB>();
    let scale = ef_embed_base::<AB>(AB::F::from_u32(SHOT_SAMPLING_SCALE).into());
    let is_pad = col::<AB>(local, SHOT_SAMPLING_COL_IS_PAD);
    let active = ef_sub_limbs::<AB>(&one, is_pad);
    let outcome = col::<AB>(local, SHOT_SAMPLING_COL_OUTCOME);
    let p0 = col::<AB>(local, SHOT_SAMPLING_COL_P0);
    let p1 = col::<AB>(local, SHOT_SAMPLING_COL_P1);
    let u = col::<AB>(local, SHOT_SAMPLING_COL_U);
    let gap = col::<AB>(local, SHOT_SAMPLING_COL_GAP);

    let mut folder = FoldAcc::<AB>::new(alpha);

    folder.push_unfiltered(&ef_bool_check_limbs::<AB>(is_pad));
    folder.push(&active, &ef_bool_check_limbs::<AB>(outcome));

    let mut recomposed = ef_embed_base::<AB>(AB::Expr::ZERO);
    let mut pow = ef_embed_base::<AB>(AB::Expr::ONE);
    for i in 0..SHOT_SAMPLING_GAP_BITS {
        let bit = col::<AB>(local, SHOT_SAMPLING_COL_GAP_BITS + i);
        folder.push(&active, &ef_bool_check_limbs::<AB>(bit));
        recomposed = ef_add_limbs::<AB>(&recomposed, &ef_mul_limbs::<AB>(bit, &pow));
        pow = ef_add_limbs::<AB>(&pow, &pow);
    }
    folder.push(&active, &ef_sub_limbs::<AB>(gap, &recomposed));

    let lhs = ef_mul_limbs::<AB>(u, &ef_add_limbs::<AB>(p0, p1));
    let rhs = ef_mul_limbs::<AB>(p0, &scale);
    let zero_branch = ef_sub_limbs::<AB>(
        &ef_sub_limbs::<AB>(&ef_sub_limbs::<AB>(&rhs, &lhs), gap),
        &one,
    );
    let one_branch = ef_sub_limbs::<AB>(&ef_sub_limbs::<AB>(&lhs, &rhs), gap);

    folder.push(
        &active,
        &ef_mul_limbs::<AB>(&ef_sub_limbs::<AB>(&one, outcome), &zero_branch),
    );
    folder.push(&active, &ef_mul_limbs::<AB>(outcome, &one_branch));

    folder.finish()
}

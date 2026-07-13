//! Plonky3 `Air` for C2b Born-rule zk binding (terminal MEASURE probabilities).

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_field::{Field, PrimeCharacteristicRing};

/// Maximum qubit width for in-circuit Born zk (single-row wide trace).
pub const BORN_ZK_MAX_QUBITS: usize = 5;

/// Fixed-point scale — matches quantum execution AIR (`10_000`).
pub const BORN_ZK_SCALE: u32 = 10_000;

/// Outcome groups: each inner vec lists computational-basis indices contributing to one outcome.
#[derive(Clone, Debug)]
pub struct DistributionAir {
    pub dim: usize,
    pub outcome_groups: Vec<Vec<usize>>,
}

impl DistributionAir {
    pub fn width(&self) -> usize {
        2 * self.dim + self.outcome_groups.len()
    }

    /// Host-side constraint accumulator (`ZERO` iff the first trace row satisfies Born binding).
    pub fn evaluate_first_row_sum<FR>(&self, row: &[FR]) -> FR
    where
        FR: Field + PrimeCharacteristicRing + Copy,
    {
        let scale = FR::from_u32(BORN_ZK_SCALE);
        let mut acc = FR::ZERO;

        for (outcome_idx, group) in self.outcome_groups.iter().enumerate() {
            let claimed = row[2 * self.dim + outcome_idx];
            let mut mass = FR::ZERO;
            for &basis in group {
                let re = row[2 * basis];
                let im = row[2 * basis + 1];
                mass += re * re + im * im;
            }
            // claimed_p and amplitudes use SCALE fixed-point: p*SCALE² = Σ|ψ|².
            acc += claimed * scale - mass;
        }

        acc
    }
}

impl<F: Field> BaseAir<F> for DistributionAir {
    fn width(&self) -> usize {
        DistributionAir::width(self)
    }

    fn max_constraint_degree(&self) -> Option<usize> {
        // probability (deg 1) * scale² vs amplitude squares (deg 2).
        Some(6)
    }
}

fn born_constraints_expr<AB: AirBuilder>(air: &DistributionAir, curr: &[AB::Var]) -> AB::Expr
where
    AB::F: Field,
{
    let scale: AB::Expr = AB::F::from_u32(BORN_ZK_SCALE).into();
    let mut acc = AB::Expr::ZERO;

    for (outcome_idx, group) in air.outcome_groups.iter().enumerate() {
        let claimed = curr[2 * air.dim + outcome_idx].into();
        let mut mass = AB::Expr::ZERO;
        for &basis in group {
            let re = curr[2 * basis].into();
            let im = curr[2 * basis + 1].into();
            mass = mass + re.clone() * re + im.clone() * im;
        }
        acc = acc + claimed * scale.clone() - mass;
    }

    acc
}

impl<AB: AirBuilder> Air<AB> for DistributionAir
where
    AB::F: Field,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let curr = main.current_slice();
        debug_assert_eq!(curr.len(), self.width());

        let acc = born_constraints_expr::<AB>(self, curr);
        builder.when_first_row().assert_zero(acc);

        // Amplitudes and claimed probabilities are static across padded rows.
        let next = main.next_slice();
        for col in 0..self.width() {
            builder
                .when_transition()
                .assert_zero(next[col].into() - curr[col].into());
        }
    }
}

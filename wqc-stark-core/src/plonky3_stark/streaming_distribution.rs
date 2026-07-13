//! Shared helpers to build streaming Born / marginal Plonky3 traces.

use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::dense::RowMajorMatrix;
use p3_mersenne_31::Mersenne31;

use crate::air::f64_to_m31;

use super::distribution_air::{
    DistributionAir, BORN_ZK_MAX_OUTCOMES, BORN_ZK_MAX_QUBITS, BORN_ZK_SCALE, COL_IM, COL_RE,
};

/// Builds a streaming Born matrix: one active row per basis amplitude, then pad rows.
///
/// Claimed probabilities are derived from fixed-point amplitude masses (`mass * SCALE⁻¹`)
/// so the AIR identity `mass = claim * SCALE` holds exactly. Host code separately checks
/// f64 oracle probabilities against the segment.
pub fn build_streaming_distribution_matrix(
    air: &DistributionAir,
    statevector: &[(f64, f64)],
    outcome_of_basis: impl Fn(usize) -> Option<usize>,
) -> Option<RowMajorMatrix<Mersenne31>> {
    if air.dim == 0
        || air.num_outcomes == 0
        || air.num_outcomes > BORN_ZK_MAX_OUTCOMES
        || statevector.len() != air.dim
    {
        return None;
    }

    let scale_inv = Mersenne31::from_u32(BORN_ZK_SCALE).inverse();
    let width = air.width();

    // Pass 1: accumulate masses.
    let mut mass = vec![Mersenne31::ZERO; air.num_outcomes];
    let mut amps = Vec::with_capacity(air.dim);
    let mut outcomes = Vec::with_capacity(air.dim);
    for (basis, (re, im)) in statevector.iter().enumerate() {
        let outcome = outcome_of_basis(basis)?;
        if outcome >= air.num_outcomes {
            return None;
        }
        let re_f = f64_to_m31(*re);
        let im_f = f64_to_m31(*im);
        mass[outcome] += re_f * re_f + im_f * im_f;
        amps.push((re_f, im_f));
        outcomes.push(outcome);
    }
    let claims: Vec<Mersenne31> = mass.iter().map(|m| *m * scale_inv).collect();

    // Pass 2: emit rows with running mass.
    let mut values = Vec::with_capacity(air.dim.saturating_mul(width));
    let mut running = vec![Mersenne31::ZERO; air.num_outcomes];
    for (basis, ((re_f, im_f), outcome)) in amps.into_iter().zip(outcomes).enumerate() {
        let _ = basis;
        let amp2 = re_f * re_f + im_f * im_f;
        running[outcome] += amp2;

        let mut row = vec![Mersenne31::ZERO; width];
        row[COL_RE] = re_f;
        row[COL_IM] = im_f;
        row[air.col_sel(outcome)] = Mersenne31::ONE;
        for k in 0..air.num_outcomes {
            row[air.col_mass(k)] = running[k];
            row[air.col_claim(k)] = claims[k];
        }
        row[air.col_is_pad()] = Mersenne31::ZERO;
        if air.evaluate_active_row_local::<Mersenne31>(&row) != Mersenne31::ZERO {
            return None;
        }
        values.extend_from_slice(&row);
    }

    let matrix = RowMajorMatrix::new(values, width);
    Some(pad_streaming_with_inactive(air, matrix))
}

/// Pads to uni-STARK height with `is_pad=1` rows that freeze mass/claim.
fn pad_streaming_with_inactive(
    air: &DistributionAir,
    matrix: RowMajorMatrix<Mersenne31>,
) -> RowMajorMatrix<Mersenne31> {
    let width = matrix.width;
    let height = matrix.values.len() / width;
    let target = height.next_power_of_two().max(crate::air::MIN_UNI_STARK_HEIGHT);
    if target == height {
        return matrix;
    }

    let last_active = matrix.values[(height - 1) * width..height * width].to_vec();
    let mut values = matrix.values;
    for _ in height..target {
        let mut row = vec![Mersenne31::ZERO; width];
        for k in 0..air.num_outcomes {
            row[air.col_mass(k)] = last_active[air.col_mass(k)];
            row[air.col_claim(k)] = last_active[air.col_claim(k)];
        }
        row[air.col_is_pad()] = Mersenne31::ONE;
        values.extend_from_slice(&row);
    }
    RowMajorMatrix::new(values, width)
}

/// Shared qubit / outcome soft-cap gate for streaming Born zk.
pub fn streaming_zk_shape_ok(qubit_count: usize, num_outcomes: usize, dim: usize) -> bool {
    qubit_count > 0
        && qubit_count <= BORN_ZK_MAX_QUBITS
        && num_outcomes > 0
        && num_outcomes <= BORN_ZK_MAX_OUTCOMES
        && dim == (1usize << qubit_count)
}

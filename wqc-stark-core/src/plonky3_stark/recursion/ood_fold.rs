//! Native OOD constraint folding for witness extraction and bind checks (R3 OOD AIR).

use p3_air::Air;
use p3_field::PrimeCharacteristicRing;
use p3_uni_stark::VerifierConstraintFolder;

use crate::plonky3_stark::aggregation_air::AggregationAir;
use crate::plonky3_stark::config::{Challenge, WqcStarkConfig};
use crate::plonky3_stark::distribution_air::DistributionAir;
use crate::plonky3_stark::quantum_air::QuantumExecutionAir;
use crate::plonky3_stark::shot_sampling_air::ShotSamplingAir;

use super::ood_air::OodAirKind;

/// Host-side fold used to sanity-check witnesses at prove/bind time (all AIR kinds).
#[allow(clippy::too_many_arguments)]
pub fn fold_ood_native(
    kind: OodAirKind,
    num_outcomes: usize,
    degree_bits: usize,
    trace_local: &[Challenge],
    trace_next: &[Challenge],
    is_first_row: Challenge,
    is_last_row: Challenge,
    is_transition: Challenge,
    alpha: Challenge,
) -> Challenge {
    use p3_air::RowWindow;
    use p3_matrix::dense::RowMajorMatrixView;
    use p3_matrix::stack::VerticalPair;

    let main = VerticalPair::new(
        RowMajorMatrixView::new_row(trace_local),
        RowMajorMatrixView::new_row(trace_next),
    );
    let empty: &[Challenge] = &[];
    let preprocessed: VerticalPair<
        RowMajorMatrixView<'_, Challenge>,
        RowMajorMatrixView<'_, Challenge>,
    > = VerticalPair::new(
        RowMajorMatrixView::new(empty, 0),
        RowMajorMatrixView::new(empty, 0),
    );
    let preprocessed_window = RowWindow::from_two_rows(empty, empty);
    let mut folder: VerifierConstraintFolder<'_, WqcStarkConfig> = VerifierConstraintFolder {
        main,
        preprocessed,
        preprocessed_window,
        periodic_values: &[],
        public_values: &[],
        is_first_row,
        is_last_row,
        is_transition,
        alpha,
        accumulator: Challenge::ZERO,
    };
    match kind {
        OodAirKind::Aggregation => AggregationAir.eval(&mut folder),
        OodAirKind::Unitary => QuantumExecutionAir.eval(&mut folder),
        OodAirKind::Distribution => {
            let dim = 1usize << degree_bits;
            DistributionAir { dim, num_outcomes }.eval(&mut folder);
        }
        OodAirKind::ShotSampling => ShotSamplingAir.eval(&mut folder),
    }
    folder.accumulator
}

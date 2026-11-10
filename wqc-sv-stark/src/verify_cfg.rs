//! A verify-only config for building a leaf's verifier in less memory.
//!
//! Building a verifier means preparing the leaf circuit, and most of that memory is the
//! preprocessed commitment: [`Cfg`]'s PCS commits every preprocessed matrix's whole low-degree
//! extension (four times the matrix at rate 1/4) and keeps the Merkle tree for opening it.
//! [`VerifyCfg`] is [`Cfg`] with a PCS that computes the same commitment a run of rows at a
//! time and keeps nothing, and that delegates everything a verifier uses to [`Cfg`]'s PCS.
//!
//! The commitment is the Merkle cap of the bit-reversed LDEs. In bit-reversed order the `N`
//! rows of an LDE split into `R` runs of `N / R` rows, run `r` being the evaluations on a coset
//! of the order-`N / R` subgroup, again bit-reversed. Run `r` of every matrix sits under the
//! same subtree, so the commitment is the subtrees' roots, from the same MMCS over the runs,
//! folded with the same compression. Tests check it against [`Cfg`]'s commitment.
//!
//! Proving needs the prover data this PCS never keeps, so its proving methods panic: a
//! [`VerifyCfg`] circuit can be prepared and verified against, never proved.

use p3_commit::{
    CommitmentOpening, OpenedValues, OpeningRequest, Pcs, PeriodicLdeTable, UnivariateStarkPcs,
};
use p3_dft::{Radix2Dit, TwoAdicSubgroupDft};
use p3_field::{Field, PrimeCharacteristicRing, TwoAdicField};
use p3_goldilocks::Poseidon2Goldilocks;
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::util::reverse_matrix_index_bits;
use p3_matrix::Matrix;
use p3_merkle_tree::{MerkleCap, MerkleTreeMmcs};
use p3_symmetric::{PaddingFreeSponge, PseudoCompressionFunction, TruncatedPermutation};
use p3_uni_stark::StarkGenericConfig;
use p3_util::reverse_bits_len;

use crate::{Cfg, Challenge, F};

type InnerPcs = <Cfg as StarkGenericConfig>::Pcs;
type Challenger = <Cfg as StarkGenericConfig>::Challenger;
type Domain = <InnerPcs as Pcs<Challenge, Challenger>>::Domain;
type Commitment = <InnerPcs as Pcs<Challenge, Challenger>>::Commitment;
type Perm = Poseidon2Goldilocks<8>;
type Hash = PaddingFreeSponge<Perm, 8, 4, 4>;
type Compress = TruncatedPermutation<Perm, 2, 4, 8>;
type Mmcs = MerkleTreeMmcs<<F as Field>::Packing, <F as Field>::Packing, Hash, Compress, 2, 4>;

/// [`Cfg`]'s PCS for a verifier: the preprocessed commitment in about the coefficients' memory
/// (plus one run), no prover data, verification delegated.
#[derive(Clone)]
pub struct VerifyPcs {
    inner: InnerPcs,
    log_blowup: usize,
    cap_height: usize,
    perm: Perm,
    compress: Compress,
}

/// [`Cfg`] with [`VerifyPcs`]: prepares and verifies exactly as [`Cfg`], cannot prove.
#[derive(Clone)]
pub struct VerifyCfg {
    inner: Cfg,
    pcs: VerifyPcs,
}

impl VerifyCfg {
    pub fn new(inner: Cfg) -> Self {
        let d = inner.descriptor();
        let log_blowup = d.log_blowup() as usize;
        let cap_height = d.input_cap_height() as usize;
        let perm = p3_recursion::builtin_config::fixed_goldilocks_poseidon2_8();
        let pcs = VerifyPcs {
            inner: inner.pcs().clone(),
            log_blowup,
            cap_height,
            compress: Compress::new(perm.clone()),
            perm,
        };
        Self { inner, pcs }
    }
}

impl StarkGenericConfig for VerifyCfg {
    type Pcs = VerifyPcs;
    type Challenge = Challenge;
    type Challenger = Challenger;

    fn pcs(&self) -> &Self::Pcs {
        &self.pcs
    }

    fn initialise_challenger(&self) -> Self::Challenger {
        self.inner.initialise_challenger()
    }

    fn is_zk(&self) -> usize {
        self.inner.is_zk()
    }

    fn lookup_proof_of_work_bits(&self) -> usize {
        self.inner.lookup_proof_of_work_bits()
    }

    fn ood_proof_of_work_bits(&self) -> usize {
        self.inner.ood_proof_of_work_bits()
    }
}

fn verify_only() -> ! {
    panic!("a VerifyCfg leaf cannot prove")
}

/// The LDEs are committed in at most this many runs (`2^LOG_RUNS`), each about this fraction
/// of a matrix: the memory beyond the coefficients is a run and its subtree.
const LOG_RUNS: usize = 6;

impl VerifyPcs {
    /// The commitment [`InnerPcs::commit`] gives `evaluations`, one run of LDE rows at a time.
    fn commit_by_runs(&self, evaluations: Vec<(Domain, RowMajorMatrix<F>)>) -> Commitment {
        // Radix2Dit transforms in place; any DFT gives the same field values.
        let dft = Radix2Dit::<F>::default();
        // Coefficients, and the shift taking each matrix's domain to `gK` (as `coset_ldes`).
        let polys: Vec<(RowMajorMatrix<F>, F)> = evaluations
            .into_iter()
            .map(|(domain, evals)| {
                assert_eq!(domain.size(), evals.height());
                (dft.idft_batch(evals), F::GENERATOR / domain.shift())
            })
            .collect();
        let log_min_lde = polys
            .iter()
            .map(|(c, _)| c.height().ilog2() as usize + self.log_blowup)
            .min()
            .expect("a preprocessed matrix");
        let log_runs = LOG_RUNS.min(log_min_lde);
        let mmcs = Mmcs::new(
            Hash::new(self.perm.clone()),
            Compress::new(self.perm.clone()),
            self.cap_height.saturating_sub(log_runs),
        );
        let mut layer: Vec<[F; 4]> = Vec::new();
        for r in 0..1usize << log_runs {
            let run: Vec<RowMajorMatrix<F>> = polys
                .iter()
                .map(|(coeffs, shift)| self.run(&dft, coeffs, *shift, r, log_runs))
                .collect();
            let (cap, _tree) = p3_commit::Mmcs::<F>::commit(&mmcs, run);
            layer.extend_from_slice(cap.roots());
        }
        // The runs' caps, in order, are the layer `log_runs` levels below their roots' root;
        // fold it up to the cap height.
        while layer.len() > 1 << self.cap_height {
            layer = layer
                .chunks_exact(2)
                .map(|pair| self.compress.compress([pair[0], pair[1]]))
                .collect();
        }
        MerkleCap::new(layer)
    }

    /// Run `r` of `2^log_runs` of a matrix's bit-reversed LDE. With `N` the LDE height and
    /// `h' = N / 2^log_runs`, its rows are the evaluations on `s·H'` (`H'` of order `h'`,
    /// `s = shift · ω_N^rev(r)`), bit-reversed: the polynomial reduced mod `x^h' − s^h'`, then a
    /// coset DFT of size `h'`.
    fn run(
        &self,
        dft: &Radix2Dit<F>,
        coeffs: &RowMajorMatrix<F>,
        shift: F,
        r: usize,
        log_runs: usize,
    ) -> RowMajorMatrix<F> {
        let log_n = coeffs.height().ilog2() as usize + self.log_blowup;
        let log_run = log_n - log_runs;
        let s = shift * F::two_adic_generator(log_n).exp_u64(reverse_bits_len(r, log_runs) as u64);
        // p(s·x) for x^h' = 1: fold coefficient k + t·h' into k with weight (s^h')^t.
        let w = coeffs.width();
        let s_run = s.exp_power_of_2(log_run);
        let mut folded = vec![F::ZERO; w << log_run];
        let mut weight = F::ONE;
        for chunk in coeffs.values.chunks(w << log_run) {
            for (f, &c) in folded.iter_mut().zip(chunk) {
                *f += c * weight;
            }
            weight *= s_run;
        }
        let mut evals = dft.coset_dft_batch(RowMajorMatrix::new(folded, w), s);
        reverse_matrix_index_bits(&mut evals);
        evals
    }
}

impl Pcs<Challenge, Challenger> for VerifyPcs {
    type Domain = Domain;
    type Commitment = Commitment;
    type ProverData = ();
    type Proof = <InnerPcs as Pcs<Challenge, Challenger>>::Proof;
    type Error = <InnerPcs as Pcs<Challenge, Challenger>>::Error;
    type ProverError = <InnerPcs as Pcs<Challenge, Challenger>>::ProverError;

    fn natural_domain_for_degree(&self, degree: usize) -> Self::Domain {
        <InnerPcs as Pcs<Challenge, Challenger>>::natural_domain_for_degree(&self.inner, degree)
    }

    fn commit(
        &self,
        _: impl IntoIterator<Item = (Self::Domain, RowMajorMatrix<F>)>,
    ) -> Result<(Self::Commitment, Self::ProverData), Self::ProverError> {
        verify_only()
    }

    fn open(
        &self,
        _: Vec<OpeningRequest<'_, Self::ProverData, Challenge>>,
        _: &mut Challenger,
    ) -> Result<(OpenedValues<Challenge>, Self::Proof), Self::ProverError> {
        verify_only()
    }

    fn verify(
        &self,
        commitments_with_opening_points: Vec<
            CommitmentOpening<Challenge, Self::Commitment, Self::Domain>,
        >,
        proof: &Self::Proof,
        challenger: &mut Challenger,
    ) -> Result<(), Self::Error> {
        <InnerPcs as Pcs<Challenge, Challenger>>::verify(
            &self.inner,
            commitments_with_opening_points,
            proof,
            challenger,
        )
    }
}

impl UnivariateStarkPcs<Challenge, Challenger> for VerifyPcs {
    type EvaluationsOnDomain<'a> = RowMajorMatrix<F>;

    const ZK: bool = <InnerPcs as UnivariateStarkPcs<Challenge, Challenger>>::ZK;

    fn log_max_trace_height(&self) -> usize {
        <InnerPcs as UnivariateStarkPcs<Challenge, Challenger>>::log_max_trace_height(&self.inner)
    }

    fn log_min_trace_height(&self) -> usize {
        <InnerPcs as UnivariateStarkPcs<Challenge, Challenger>>::log_min_trace_height(&self.inner)
    }

    fn commit_preprocessing(
        &self,
        evaluations: impl IntoIterator<Item = (Self::Domain, RowMajorMatrix<F>)>,
    ) -> Result<(Self::Commitment, Self::ProverData), Self::ProverError> {
        Ok((self.commit_by_runs(evaluations.into_iter().collect()), ()))
    }

    fn get_quotient_ldes(
        &self,
        _: impl IntoIterator<Item = (Self::Domain, RowMajorMatrix<F>)>,
        _: usize,
    ) -> Result<Vec<RowMajorMatrix<F>>, Self::ProverError> {
        verify_only()
    }

    fn commit_ldes(
        &self,
        _: Vec<RowMajorMatrix<F>>,
    ) -> Result<(Self::Commitment, Self::ProverData), Self::ProverError> {
        verify_only()
    }

    fn get_evaluations_on_domain<'a>(
        &self,
        _: &'a Self::ProverData,
        _: usize,
        _: Self::Domain,
    ) -> Self::EvaluationsOnDomain<'a> {
        verify_only()
    }

    fn open_with_preprocessing(
        &self,
        _: Vec<OpeningRequest<'_, Self::ProverData, Challenge>>,
        _: &mut Challenger,
        _: Option<usize>,
    ) -> Result<(OpenedValues<Challenge>, Self::Proof), Self::ProverError> {
        verify_only()
    }

    fn verify_with_preprocessing(
        &self,
        rounds: Vec<CommitmentOpening<Challenge, Self::Commitment, Self::Domain>>,
        proof: &Self::Proof,
        challenger: &mut Challenger,
        preprocessed_commitment: Option<usize>,
    ) -> Result<(), Self::Error> {
        <InnerPcs as UnivariateStarkPcs<Challenge, Challenger>>::verify_with_preprocessing(
            &self.inner,
            rounds,
            proof,
            challenger,
            preprocessed_commitment,
        )
    }

    fn get_opt_randomization_poly_commitment(
        &self,
        domain: impl IntoIterator<Item = Self::Domain>,
    ) -> Result<Option<(Self::Commitment, Self::ProverData)>, Self::ProverError> {
        match <InnerPcs as UnivariateStarkPcs<Challenge, Challenger>>::get_opt_randomization_poly_commitment(&self.inner, domain)? {
            None => Ok(None),
            Some(_) => verify_only(),
        }
    }

    fn build_periodic_lde_table(
        &self,
        periodic_cols: &[Vec<F>],
        trace_domain: Self::Domain,
        quotient_domain: Self::Domain,
    ) -> PeriodicLdeTable<F> {
        <InnerPcs as UnivariateStarkPcs<Challenge, Challenger>>::build_periodic_lde_table(
            &self.inner,
            periodic_cols,
            trace_domain,
            quotient_domain,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_field::PrimeCharacteristicRing;

    fn matrices(shapes: &[(usize, usize)], seed: u64) -> Vec<(Domain, RowMajorMatrix<F>)> {
        // splitmix64: arbitrary values, reproducible.
        let mut x = seed;
        let mut next = move || {
            x = x.wrapping_add(0x9E37_79B9_7F4A_7C15);
            let mut z = x;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            F::from_u64(z ^ (z >> 31))
        };
        let pcs = crate::FriParams::RECURSION.config().pcs().clone();
        shapes
            .iter()
            .map(|&(log_h, width)| {
                let values = (0..width << log_h).map(|_| next()).collect();
                (
                    <InnerPcs as Pcs<Challenge, Challenger>>::natural_domain_for_degree(
                        &pcs,
                        1 << log_h,
                    ),
                    RowMajorMatrix::new(values, width),
                )
            })
            .collect()
    }

    /// The run-by-run commitment is the inner PCS's, for one and several matrices of mixed
    /// heights and widths, at the leaf's blowup and the recursion's.
    #[test]
    fn commit_by_runs_matches_the_inner_commitment() {
        let shapes: [&[(usize, usize)]; 4] = [
            &[(3, 1)],
            &[(5, 13), (3, 8), (5, 2)],
            &[(6, 7), (4, 1), (3, 23), (6, 4), (5, 9)],
            &[(8, 13), (8, 8), (7, 11), (4, 2)],
        ];
        for fri in [
            crate::FriParams::leaf(crate::SecurityLevel::Ultra),
            crate::FriParams::RECURSION,
        ] {
            let cfg = fri.config();
            let v = VerifyCfg::new(cfg.clone());
            for (k, s) in shapes.iter().enumerate() {
                let (want, _) =
                    <InnerPcs as UnivariateStarkPcs<Challenge, Challenger>>::commit_preprocessing(
                        cfg.pcs(),
                        matrices(s, k as u64),
                    )
                    .unwrap();
                let (got, ()) = v.pcs().commit_preprocessing(matrices(s, k as u64)).unwrap();
                assert_eq!(got, want, "{fri:?} {s:?}");
            }
        }
    }
}

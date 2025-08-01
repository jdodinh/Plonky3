//! The FRI PCS protocol over two-adic fields.
//!
//! The following implements a slight variant of the usual FRI protocol. As usual we start
//! with a polynomial `F(x)` of degree `n` given as evaluations over the coset `gH` with `|H| = 2^n`.
//!
//! Now consider the polynomial `G(x) = F(gx)`. Note that `G(x)` has the same degree as `F(x)` and
//! the evaluations of `F(x)` over `gH` are identical to the evaluations of `G(x)` over `H`.
//!
//! Hence we can reinterpret our vector of evaluations as evaluations of `G(x)` over `H` and apply
//! the standard FRI protocol to this evaluation vector. This makes it easier to apply FRI to a collection
//! of polynomials defined over different cosets as we don't need to keep track of the coset shifts. We
//! can just assume that every polynomial is defined over the subgroup of the relevant size.
//!
//! If we changed our domain construction (e.g., using multiple cosets), we would need to carefully reconsider these assumptions.

use alloc::vec;
use alloc::vec::Vec;
use core::fmt::Debug;
use core::marker::PhantomData;

use itertools::{Itertools, izip};
use p3_challenger::{CanObserve, FieldChallenger, GrindingChallenger};
use p3_commit::{BatchOpening, Mmcs, OpenedValues, Pcs};
use p3_dft::TwoAdicSubgroupDft;
use p3_field::coset::TwoAdicMultiplicativeCoset;
use p3_field::{
    ExtensionField, PackedFieldExtension, TwoAdicField, batch_multiplicative_inverse, dot_product,
};
use p3_interpolation::interpolate_coset_with_precomputation;
use p3_matrix::Matrix;
use p3_matrix::bitrev::{BitReversedMatrixView, BitReversibleMatrix};
use p3_matrix::dense::{RowMajorMatrix, RowMajorMatrixView};
use p3_maybe_rayon::prelude::*;
use p3_util::linear_map::LinearMap;
use p3_util::{log2_strict_usize, reverse_bits_len, reverse_slice_index_bits};
use tracing::{info_span, instrument};

use crate::verifier::{self, FriError};
use crate::{FriFoldingStrategy, FriParameters, FriProof, prover};

/// A polynomial commitment scheme using FRI to generate opening proofs.
///
/// We commit to a polynomial `f` via its evaluation vectors over a coset
/// `gH` where `|H| >= 2 * deg(f)`. A value `f(z)` is opened by using a FRI
/// proof to show that the evaluations of `(f(x) - f(z))/(x - z)` over
/// `gH` are low degree.
#[derive(Debug)]
pub struct TwoAdicFriPcs<Val, Dft, InputMmcs, FriMmcs> {
    pub(crate) dft: Dft,
    pub(crate) mmcs: InputMmcs,
    pub(crate) fri: FriParameters<FriMmcs>,
    _phantom: PhantomData<Val>,
}

impl<Val, Dft, InputMmcs, FriMmcs> TwoAdicFriPcs<Val, Dft, InputMmcs, FriMmcs> {
    pub const fn new(dft: Dft, mmcs: InputMmcs, fri: FriParameters<FriMmcs>) -> Self {
        Self {
            dft,
            mmcs,
            fri,
            _phantom: PhantomData,
        }
    }
}

/// The Prover Data associated to a commitment to a collection of matrices
/// and a list of points to open each matrix at.
pub type ProverDataWithOpeningPoints<'a, EF, ProverData> = (
    // The matrices and auxiliary prover data
    &'a ProverData,
    // for each matrix,
    Vec<
        // points to open
        Vec<EF>,
    >,
);

/// A joint commitment to a collection of matrices and their opening at
/// a collection of points.
pub type CommitmentWithOpeningPoints<Challenge, Commitment, Domain> = (
    Commitment,
    // For each matrix in the commitment:
    Vec<(
        // The domain of the matrix
        Domain,
        // A vector of (point, claimed_evaluation) pairs
        Vec<(Challenge, Vec<Challenge>)>,
    )>,
);

pub struct TwoAdicFriFolding<InputProof, InputError>(pub PhantomData<(InputProof, InputError)>);

pub type TwoAdicFriFoldingForMmcs<F, M> =
    TwoAdicFriFolding<Vec<BatchOpening<F, M>>, <M as Mmcs<F>>::Error>;

impl<F: TwoAdicField, InputProof, InputError: Debug, EF: ExtensionField<F>>
    FriFoldingStrategy<F, EF> for TwoAdicFriFolding<InputProof, InputError>
{
    type InputProof = InputProof;
    type InputError = InputError;

    fn extra_query_index_bits(&self) -> usize {
        0
    }

    fn fold_row(
        &self,
        index: usize,
        log_height: usize,
        beta: EF,
        evals: impl Iterator<Item = EF>,
    ) -> EF {
        let arity = 2;
        let log_arity = 1;
        let (e0, e1) = evals
            .collect_tuple()
            .expect("TwoAdicFriFolder only supports arity=2");
        // If performance critical, make this API stateful to avoid this
        // This is a bit more math than is necessary, but leaving it here
        // in case we want higher arity in the future.
        let subgroup_start = F::two_adic_generator(log_height + log_arity)
            .exp_u64(reverse_bits_len(index, log_height) as u64);
        let mut xs = F::two_adic_generator(log_arity)
            .shifted_powers(subgroup_start)
            .collect_n(arity);
        reverse_slice_index_bits(&mut xs);
        assert_eq!(log_arity, 1, "can only interpolate two points for now");
        // interpolate and evaluate at beta
        e0 + (beta - xs[0]) * (e1 - e0) * (xs[1] - xs[0]).inverse()
        // Currently Algebra<F> does not include division so we do it manually.
        // Note we do not want to do an EF division as that is far more expensive.
    }

    fn fold_matrix<M: Matrix<EF>>(&self, beta: EF, m: M) -> Vec<EF> {
        // We use the fact that
        //     p_e(x^2) = (p(x) + p(-x)) / 2
        //     p_o(x^2) = (p(x) - p(-x)) / (2 x)
        // that is,
        //     p_e(g^(2i)) = (p(g^i) + p(g^(n/2 + i))) / 2
        //     p_o(g^(2i)) = (p(g^i) - p(g^(n/2 + i))) / (2 g^i)
        // so
        //     result(g^(2i)) = p_e(g^(2i)) + beta p_o(g^(2i))
        //
        // As p_e, p_o will be in the extension field we want to find ways to avoid extension multiplications.
        // We should only need a single one (namely multiplication by beta).
        let g_inv = F::two_adic_generator(log2_strict_usize(m.height()) + 1).inverse();

        // TODO: vectorize this (after we have packed extension fields)

        // As beta is in the extension field, we want to avoid multiplying by it
        // for as long as possible. Here we precompute the powers  `g_inv^i / 2` in the base field.
        let mut halve_inv_powers = g_inv.shifted_powers(F::ONE.halve()).collect_n(m.height());
        reverse_slice_index_bits(&mut halve_inv_powers);

        m.par_rows()
            .zip(halve_inv_powers)
            .map(|(mut row, halve_inv_power)| {
                let (lo, hi) = row.next_tuple().unwrap();
                (lo + hi).halve() + (lo - hi) * beta * halve_inv_power
            })
            .collect()
    }
}

impl<Val, Dft, InputMmcs, FriMmcs, Challenge, Challenger> Pcs<Challenge, Challenger>
    for TwoAdicFriPcs<Val, Dft, InputMmcs, FriMmcs>
where
    Val: TwoAdicField,
    Dft: TwoAdicSubgroupDft<Val>,
    InputMmcs: Mmcs<Val>,
    FriMmcs: Mmcs<Challenge>,
    Challenge: ExtensionField<Val>,
    Challenger:
        FieldChallenger<Val> + CanObserve<FriMmcs::Commitment> + GrindingChallenger<Witness = Val>,
{
    type Domain = TwoAdicMultiplicativeCoset<Val>;
    type Commitment = InputMmcs::Commitment;
    type ProverData = InputMmcs::ProverData<RowMajorMatrix<Val>>;
    type EvaluationsOnDomain<'a> = BitReversedMatrixView<RowMajorMatrixView<'a, Val>>;
    type Proof = FriProof<Challenge, FriMmcs, Val, Vec<BatchOpening<Val, InputMmcs>>>;
    type Error = FriError<FriMmcs::Error, InputMmcs::Error>;
    const ZK: bool = false;

    /// Get the unique subgroup `H` of size `|H| = degree`.
    ///
    /// # Panics:
    /// This function will panic if `degree` is not a power of 2 or `degree > (1 << Val::TWO_ADICITY)`.
    fn natural_domain_for_degree(&self, degree: usize) -> Self::Domain {
        TwoAdicMultiplicativeCoset::new(Val::ONE, log2_strict_usize(degree)).unwrap()
    }

    /// Commit to a collection of evaluation matrices.
    ///
    /// Each element of `evaluations` contains a coset `shift * H` and a matrix `mat` with `mat.height() = |H|`.
    /// Interpreting each column of `mat` as the evaluations of a polynomial `p_i(x)` over `shift * H`,
    /// this computes the evaluations of `p_i` over `gK` where `g` is the chosen generator of the multiplicative group
    /// of `Val` and `K` is the unique subgroup of order `|H| << self.fri.log_blowup`.
    ///
    /// This then outputs a Merkle commitment to these evaluations.
    fn commit(
        &self,
        evaluations: impl IntoIterator<Item = (Self::Domain, RowMajorMatrix<Val>)>,
    ) -> (Self::Commitment, Self::ProverData) {
        let ldes: Vec<_> = evaluations
            .into_iter()
            .map(|(domain, evals)| {
                assert_eq!(domain.size(), evals.height());
                // coset_lde_batch converts from evaluations over `xH` to evaluations over `shift * x * K`.
                // Hence, letting `shift = g/x` the output will be evaluations over `gK` as desired.
                // When `x = g`, we could just use the standard LDE but currently this doesn't seem
                // to give a meaningful performance boost.
                let shift = Val::GENERATOR / domain.shift();
                // Compute the LDE with blowup factor fri.log_blowup.
                // We bit reverse as this is required by our implementation of the FRI protocol.
                self.dft
                    .coset_lde_batch(evals, self.fri.log_blowup, shift)
                    .bit_reverse_rows()
                    .to_row_major_matrix()
            })
            .collect();

        // Commit to the bit-reversed LDEs.
        self.mmcs.commit(ldes)
    }

    /// Given the evaluations on a domain `gH`, return the evaluations on a different domain `g'K`.
    ///
    /// Arguments:
    /// - `prover_data`: The prover data containing all committed evaluation matrices.
    /// - `idx`: The index of the matrix containing the evaluations we want. These evaluations
    ///   are assumed to be over the coset `gH` where `g = Val::GENERATOR`.
    /// - `domain`: The domain `g'K` on which to get evaluations on. Currently, this assumes that
    ///   `g' = g` and `K` is a subgroup of `H` and panics if this is not the case.
    fn get_evaluations_on_domain<'a>(
        &self,
        prover_data: &'a Self::ProverData,
        idx: usize,
        domain: Self::Domain,
    ) -> Self::EvaluationsOnDomain<'a> {
        // todo: handle extrapolation for LDEs we don't have
        assert_eq!(domain.shift(), Val::GENERATOR);
        let lde = self.mmcs.get_matrices(prover_data)[idx];
        assert!(lde.height() >= domain.size());
        lde.split_rows(domain.size()).0.bit_reverse_rows()
    }

    /// Open a batch of matrices at a collection of points.
    ///
    /// Returns the opened values along with a proof.
    ///
    /// This function assumes that all matrices correspond to evaluations over the
    /// coset `gH` where `g = Val::GENERATOR` and `H` is a subgroup of appropriate size depending on the
    /// matrix.
    fn open(
        &self,
        // For each multi-matrix commitment,
        commitment_data_with_opening_points: Vec<(
            // The matrices and auxiliary prover data
            &Self::ProverData,
            // for each matrix,
            Vec<
                // points to open
                Vec<Challenge>,
            >,
        )>,
        challenger: &mut Challenger,
    ) -> (OpenedValues<Challenge>, Self::Proof) {
        /*

        A quick rundown of the optimizations in this function:
        We are trying to compute sum_i alpha^i * (p(X) - y)/(X - z),
        for each z an opening point, y = p(z). Each p(X) is given as evaluations in bit-reversed order
        in the columns of the matrices. y is computed by barycentric interpolation.
        X and p(X) are in the base field; alpha, y and z are in the extension.
        The primary goal is to minimize extension multiplications.

        - Instead of computing all alpha^i, we just compute alpha^i for i up to the largest width
        of a matrix, then multiply by an "alpha offset" when accumulating.
              a^0 x0 + a^1 x1 + a^2 x2 + a^3 x3 + ...
            = ( a^0 x0 + a^1 x1 ) + a^2 ( a^0 x2 + a^1 x3 ) + ...
            (see `alpha_pows`, `alpha_pow_offset`, `num_reduced`)

        - For each unique point z, we precompute 1/(X-z) for the largest subgroup opened at this point.
        Since we compute it in bit-reversed order, smaller subgroups can simply truncate the vector.
            (see `inv_denoms`)

        - Then, for each matrix (with columns p_i) and opening point z, we want:
            for each row (corresponding to subgroup element X):
                reduced[X] += alpha_offset * sum_i [ alpha^i * inv_denom[X] * (p_i[X] - y[i]) ]

            We can factor out inv_denom, and expand what's left:
                reduced[X] += alpha_offset * inv_denom[X] * sum_i [ alpha^i * p_i[X] - alpha^i * y[i] ]

            And separate the sum:
                reduced[X] += alpha_offset * inv_denom[X] * [ sum_i [ alpha^i * p_i[X] ] - sum_i [ alpha^i * y[i] ] ]

            And now the last sum doesn't depend on X, so we can precompute that for the matrix, too.
            So the hot loop (that depends on both X and i) is just:
                sum_i [ alpha^i * p_i[X] ]

            with alpha^i an extension, p_i[X] a base

        */

        // Contained in each `Self::ProverData` is a list of matrices which have been committed to.
        // We extract those matrices to be able to refer to them directly.
        let mats_and_points = commitment_data_with_opening_points
            .iter()
            .map(|(data, points)| {
                let mats = self
                    .mmcs
                    .get_matrices(data)
                    .into_iter()
                    .map(|m| m.as_view())
                    .collect_vec();
                debug_assert_eq!(
                    mats.len(),
                    points.len(),
                    "each matrix should have a corresponding set of evaluation points"
                );
                (mats, points)
            })
            .collect_vec();

        // Find the maximum height and the maximum width of matrices in the batch.
        // These do not need to correspond to the same matrix.
        let (global_max_height, global_max_width) = mats_and_points
            .iter()
            .flat_map(|(mats, _)| mats.iter().map(|m| (m.height(), m.width())))
            .reduce(|(hmax, wmax), (h, w)| (hmax.max(h), wmax.max(w)))
            .expect("No Matrices Supplied?");
        let log_global_max_height = log2_strict_usize(global_max_height);

        // Get all values of the coset `gH` for the largest necessary subgroup `H`.
        // We also bit reverse which means that coset has the nice property that
        // `coset[..2^i]` contains the values of `gK` for `|K| = 2^i`.
        let coset = {
            let coset =
                TwoAdicMultiplicativeCoset::new(Val::GENERATOR, log_global_max_height).unwrap();
            let mut coset_points = coset.iter().collect();
            reverse_slice_index_bits(&mut coset_points);
            coset_points
        };

        // For each unique opening point z, we will find the largest degree bound
        // for that point, and precompute 1/(z - X) for the largest subgroup (in bitrev order).
        let inv_denoms = compute_inverse_denominators(&mats_and_points, &coset);

        // Evaluate coset representations and write openings to the challenger
        let all_opened_values = mats_and_points
            .iter()
            .map(|(mats, points)| {
                // For each collection of matrices
                izip!(mats.iter(), points.iter())
                    .map(|(mat, points_for_mat)| {
                        // TODO: This assumes that every input matrix has a blowup of at least self.fri.log_blowup.
                        // If the blow_up factor is smaller than self.fri.log_blowup, this will lead to errors.
                        // If it is bigger, we shouldn't get any errors but it will be slightly slower.
                        // Ideally, polynomials could be passed in with their blow_up factors known.

                        // The point of this correction is that each column of the matrix corresponds to a low degree polynomial.
                        // Hence we can save time by restricting the height of the matrix to be the minimal height which
                        // uniquely identifies the polynomial.
                        let h = mat.height() >> self.fri.log_blowup;

                        // `subgroup` and `mat` are both in bit-reversed order, so we can truncate.
                        let (low_coset, _) = mat.split_rows(h);
                        let coset_h = &coset[..h];

                        points_for_mat
                            .iter()
                            .map(|&point| {
                                let _guard =
                                    info_span!("evaluate matrix", dims = %mat.dimensions())
                                        .entered();

                                // Use Barycentric interpolation to evaluate each column of the matrix at the given point.
                                let ys =
                                    info_span!("compute opened values with Lagrange interpolation")
                                        .in_scope(|| {
                                            // Get the relevant inverse denominators for this point and use these to
                                            // interpolate to get the evaluation of each polynomial in the matrix
                                            // at the desired point.
                                            let inv_denoms = &inv_denoms.get(&point).unwrap()[..h];
                                            interpolate_coset_with_precomputation(
                                                &low_coset,
                                                Val::GENERATOR,
                                                point,
                                                coset_h,
                                                inv_denoms,
                                            )
                                        });
                                ys.iter()
                                    .for_each(|&y| challenger.observe_algebra_element(y));
                                ys
                            })
                            .collect_vec()
                    })
                    .collect_vec()
            })
            .collect_vec();

        // Batch combination challenge

        // Soundness Error:
        // See the discussion in the doc comment of [`prove_fri`]. Essentially, the soundness error
        // for this sample is tightly tied to the soundness error of the FRI protocol.
        // Roughly speaking, at a minimum is it k/|EF| where `k` is the sum of, for each function, the number of
        // points it needs to be opened at. This comes from the fact that we are takeing a large linear combination
        // of `(f(zeta) - f(x))/(zeta - x)` for each function `f` and all of `f`'s opening points.
        // In our setup, k is two times the trace width plus the number of quotient polynomials.
        let alpha: Challenge = challenger.sample_algebra_element();

        // We precompute powers of alpha as we need the same powers for each matrix.
        // We compute both a vector of unpacked powers and a vector of packed powers.
        // TODO: It should be possible to refactor this to only use the packed powers but
        // this is not a bottleneck so is not a priority.
        let packed_alpha_powers =
            Challenge::ExtensionPacking::packed_ext_powers_capped(alpha, global_max_width)
                .collect_vec();
        let alpha_powers =
            Challenge::ExtensionPacking::to_ext_iter(packed_alpha_powers.iter().copied())
                .collect_vec();

        // Now that we have sent the openings to the verifier, it remains to prove
        // that those openings are correct.

        // Given a low degree polynomial `f(x)` with claimed evaluation `f(zeta)`, we can check
        // that `f(zeta)` is correct by doing a low degree test on `(f(zeta) - f(x))/(zeta - x)`.
        // We will use `alpha` to batch together both different claimed openings `zeta` and
        // different polynomials `f` whose evaluation vectors have the same height.

        // TODO: If we allow different polynomials to have different blow_up factors
        // we may need to revisit this and to ensure it is safe to batch them together.

        // num_reduced records the number of (function, opening point) pairs for each `log_height`.
        // TODO: This should really be `[0; Val::TWO_ADICITY]` but that runs into issues with generics.
        let mut num_reduced = [0; 32];

        // For each `log_height` from 2^1 -> 2^32, reduced_openings will contain either `None`
        // if there are no matrices of that height, or `Some(vec)` where `vec` is equal to
        // a weighted sum of `(f(zeta) - f(x))/(zeta - x)` over all `f`'s of that height and
        // for each `f`, all opening points `zeta`. The sum is weighted by powers of the challenge alpha.
        let mut reduced_openings: [_; 32] = core::array::from_fn(|_| None);

        for ((mats, points), openings_for_round) in
            mats_and_points.iter().zip(all_opened_values.iter())
        {
            for (mat, points_for_mat, openings_for_mat) in
                izip!(mats.iter(), points.iter(), openings_for_round.iter())
            {
                let _guard =
                    info_span!("reduce matrix quotient", dims = %mat.dimensions()).entered();

                let log_height = log2_strict_usize(mat.height());

                // If this is our first matrix at this height, initialise reduced_openings to zero.
                // Otherwise, get a mutable reference to it.
                let reduced_opening_for_log_height = reduced_openings[log_height]
                    .get_or_insert_with(|| vec![Challenge::ZERO; mat.height()]);
                debug_assert_eq!(reduced_opening_for_log_height.len(), mat.height());

                // Treating our matrix M as the evaluations of functions f_0, f_1, ...
                // Compute the evaluations of `Mred(x) = f_0(x) + alpha*f_1(x) + ...`
                let mat_compressed = info_span!("compress mat").in_scope(|| {
                    // This will be reused for all points z which M is opened at so we collect into a vector.
                    mat.rowwise_packed_dot_product::<Challenge>(&packed_alpha_powers)
                        .collect::<Vec<_>>()
                });

                for (&point, openings) in points_for_mat.iter().zip(openings_for_mat) {
                    // If we have multiple matrices at the same height, we need to scale alpha to combine them.
                    // This means that reduced_openings will contain:
                    // Mred_0(x) + alpha^{M_0.width()}Mred_1(x) + alpha^{M_0.width() + M_1.width()}Mred_2(x) + ...
                    // Where M_0, M_1, ... are the matrices of the same height.
                    let alpha_pow_offset = alpha.exp_u64(num_reduced[log_height] as u64);

                    // As we have all the openings `f_i(z)`, we can combine them using `alpha`
                    // in an identical way to before to compute `Mred(z)`.
                    let reduced_openings: Challenge =
                        dot_product(alpha_powers.iter().copied(), openings.iter().copied());

                    mat_compressed
                        .par_iter()
                        .zip(reduced_opening_for_log_height.par_iter_mut())
                        // inv_denoms contains `1/(z - x)` for `x` in a coset `gK`.
                        // If `|K| =/= mat.height()` we actually want a subset of this
                        // corresponding to the evaluations over `gH` for `|H| = mat.height()`.
                        // As inv_denoms is bit reversed, the evaluations over `gH` are exactly
                        // the evaluations over `gK` at the indices `0..mat.height()`.
                        // So zip will truncate to the desired smaller length.
                        .zip(inv_denoms.get(&point).unwrap().par_iter())
                        // Map the function `Mred(x) -> (Mred(z) - Mred(x))/(z - x)`
                        // across the evaluation vector of `Mred(x)`. Adjust by alpha_pow_offset
                        // as needed.
                        .for_each(|((&reduced_row, ro), &inv_denom)| {
                            *ro += alpha_pow_offset * (reduced_openings - reduced_row) * inv_denom
                        });
                    num_reduced[log_height] += mat.width();
                }
            }
        }

        // It remains to prove that all evaluation vectors in reduced_openings correspond to
        // low degree functions.
        let fri_input = reduced_openings.into_iter().rev().flatten().collect_vec();

        let folding: TwoAdicFriFoldingForMmcs<Val, InputMmcs> = TwoAdicFriFolding(PhantomData);

        // Produce the FRI proof.
        let fri_proof = prover::prove_fri(
            &folding,
            &self.fri,
            fri_input,
            challenger,
            log_global_max_height,
            &commitment_data_with_opening_points,
            &self.mmcs,
        );

        (all_opened_values, fri_proof)
    }

    fn verify(
        &self,
        // For each commitment:
        commitments_with_opening_points: Vec<
            CommitmentWithOpeningPoints<Challenge, Self::Commitment, Self::Domain>,
        >,
        proof: &Self::Proof,
        challenger: &mut Challenger,
    ) -> Result<(), Self::Error> {
        // Write all evaluations to challenger.
        // Need to ensure to do this in the same order as the prover.
        for (_, round) in &commitments_with_opening_points {
            for (_, mat) in round {
                for (_, point) in mat {
                    point
                        .iter()
                        .for_each(|&opening| challenger.observe_algebra_element(opening));
                }
            }
        }

        let folding: TwoAdicFriFoldingForMmcs<Val, InputMmcs> = TwoAdicFriFolding(PhantomData);

        verifier::verify_fri(
            &folding,
            &self.fri,
            proof,
            challenger,
            &commitments_with_opening_points,
            &self.mmcs,
        )?;

        Ok(())
    }
}

/// Compute vectors of inverse denominators for each unique opening point.
///
/// Arguments:
/// - `mats_and_points` is a list of matrices and for each matrix a list of points. We assume that
///    the total number of distinct points is very small as several methods contained herein are `O(n^2)`
///    in the number of points.
/// - `coset` is the set of points `gH` where `H` a two-adic subgroup such that `|H|` is greater
///     than or equal to the largest height of any matrix in `mats_and_points`. The values
///     in `coset` must be in bit-reversed order.
///
/// For each point `z`, let `M` be the matrix of largest height which opens at `z`.
/// let `H_z` be the unique subgroup of order `M.height()`. Compute the vector of
/// `1/(z - x)` for `x` in `gH_z`.
///
/// Return a LinearMap which allows us to recover the computed vectors for each `z`.
#[instrument(skip_all)]
fn compute_inverse_denominators<F: TwoAdicField, EF: ExtensionField<F>, M: Matrix<F>>(
    mats_and_points: &[(Vec<M>, &Vec<Vec<EF>>)],
    coset: &[F],
) -> LinearMap<EF, Vec<EF>> {
    // For each `z`, find the maximal height of any matrix which we need to
    // open at `z`.
    let mut max_log_height_for_point: LinearMap<EF, usize> = LinearMap::new();
    for (mats, points) in mats_and_points {
        for (mat, points_for_mat) in izip!(mats, *points) {
            let log_height = log2_strict_usize(mat.height());
            for &z in points_for_mat {
                if let Some(lh) = max_log_height_for_point.get_mut(&z) {
                    *lh = core::cmp::max(*lh, log_height);
                } else {
                    max_log_height_for_point.insert(z, log_height);
                }
            }
        }
    }

    // Compute the inverse denominators for each point `z`.
    max_log_height_for_point
        .into_iter()
        .map(|(z, log_height)| {
            (
                z,
                batch_multiplicative_inverse(
                    // As coset is stored in bit-reversed order,
                    // we can just take the first `2^log_height` elements.
                    &coset[..(1 << log_height)]
                        .iter()
                        .map(|&x| z - x)
                        .collect_vec(),
                ),
            )
        })
        .collect()
}

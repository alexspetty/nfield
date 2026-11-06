/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.TheStructureThatSurvives
import NField.Alignment.CollisionSpectrumSourceDetails

/-!
# The Structure That Survives

All seven named claims in the unchanged published manuscript are represented
by checked Lean proofs. The original thirteen statements remain unchanged.

The concrete exponential kernel is positive definite and has the printed
irreducible tridiagonal inverse, including its complex Hermitian quadratic
form. Its literal population-weighted quotient has simple eigenvalues
strictly decreasing from one to a positive endpoint. The actual particle
matrix has the exact quotient-plus-bulk spectral multiset and multiplicity,
and its matrix exponential satisfies the printed heat-trace identity and
sharp bounds. Sorting actual integer labels supplies the hypotheses rather
than assuming a spectral model. Mathlib Dirichlet coverage gives eventual
occurrence of all labels, exact eventual bulk multiplicity, and vanishing
actual nontrivial-mode proportion. All three first-three-hundred-prime
examples have exactly twelve labels and bulk multiplicity two hundred
eighty eight, for every positive kernel scale.

The separate numerical tolerance checks remain bounded computational
records. The kinetic analogy is interpretive, and the manuscript explicitly
leaves asymptotic universality beyond the quotient open.
-/

namespace NField.Papers.TheStructureThatSurvives

open scoped BigOperators ComplexConjugate
open Filter
open NField.CollisionDefinition
open NField.Alignment.CollisionFluctuationSum
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionTransformStrip
open NField.Alignment.TheStructureThatSurvives

/-- All-size finite determination after the exact slice reduction. -/
theorem exact_all_size_slice_table
    {b ell N : ℕ} (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (hcop : Nat.Coprime N b) :
    allLagSliceDeviation b ell N =
      allLagTable b ell (N % allLagModulus b ell) :=
  allLagSliceDeviation_eq_table_mod hb2 hell hcop

/-- All-size finite determination for the intrinsic digit-collision
deviation. -/
theorem exact_all_size_direct_table
    {b ell N : ℕ} (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (hcop : Nat.Coprime N b) :
    directAllLagDeviation b ell N =
      allLagTable b ell (N % allLagModulus b ell) :=
  directAllLagDeviation_eq_table_mod hb2 hell hcop

/-- Prime divisors of the base have exact direct label zero. -/
theorem exact_base_prime_label_zero
    {b ell p : ℕ} (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (hp : Nat.Prime p) (hpb : p ∣ b) :
    directAllLagDeviation b ell p = 0 :=
  primeDividingBase_directDeviation_zero hb2 hell hp hpb

/-- The half-centered unit table is exactly odd under reflection. -/
theorem exact_centered_reflection
    {b ell : ℕ} [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (a : UnitClass (allLagModulus b ell)) :
    halfCenteredUnitTable b ell (-a) = -halfCenteredUnitTable b ell a :=
  halfCenteredUnitTable_odd hb2 hell a

/-- Every even character is absent from the half-centered transform. -/
theorem exact_parity_gate
    {b ell : ℕ} [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (χ : Character (allLagModulus b ell)) (heven : χ.Even) :
    collisionCoefficient (halfCenteredUnitTable b ell) χ = 0 :=
  halfCenteredUnitTable_evenCoefficient_zero hb2 hell χ heven

/-- Exact action of the full block kernel through its quotient coordinates. -/
theorem exact_finite_quotient_action
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (label : ι → κ) (scale : κ → ℝ) (Q : Matrix κ κ ℝ)
    (hscale : ∀ α, scale α ≠ 0) (v : ι → ℝ) (i : ι) :
    Matrix.mulVec (normalizedBlockKernel label scale Q) v i =
      Matrix.mulVec Q (normalizedBlockCoordinate label scale v) (label i) /
        scale (label i) :=
  normalizedBlockKernel_mulVec label scale Q hscale v i

/-- The normalized block lift intertwines the quotient and full kernels. -/
theorem exact_quotient_intertwining
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (label : ι → κ) (scale : κ → ℝ) (Q : Matrix κ κ ℝ)
    (hscale : ∀ α, scale α ≠ 0)
    (hscaleSq : ∀ α, scale α ^ 2 = labelPopulation label α)
    (y : κ → ℝ) :
    Matrix.mulVec (normalizedBlockKernel label scale Q)
        (normalizedBlockLift label scale y) =
      normalizedBlockLift label scale (Matrix.mulVec Q y) :=
  normalizedBlockKernel_mulVec_lift label scale Q hscale hscaleSq y

/-- The exact `N-q`-dimensional eigenvalue-one bulk subspace. -/
theorem exact_surviving_bulk_subspace
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (label : ι → κ) (scale : κ → ℝ) (Q : Matrix κ κ ℝ)
    (hscale : ∀ α, scale α ≠ 0)
    (hscaleSq : ∀ α, scale α ^ 2 = labelPopulation label α) :
    Module.finrank ℝ (normalizedBlockCoordinateLinear label scale).ker =
        Fintype.card ι - Fintype.card κ ∧
      ∀ v ∈ (normalizedBlockCoordinateLinear label scale).ker,
        squaredNormalizedLaplacianAction
          (normalizedBlockKernel label scale Q) v = v :=
  surviving_bulk_subspace label scale Q hscale hscaleSq

/-- Every unit label class contains arbitrarily large primes. -/
theorem exact_prime_class_coverage
    {m : ℕ} [NeZero m] (a : UnitClass m) (n : ℕ) :
    ∃ p > n, p.Prime ∧ (p : ZMod m) = a.val :=
  unitClass_contains_arbitrarily_large_primes a n

/-- Fixed spectral complexity has zero asymptotic proportion. -/
theorem exact_fixed_complexity_limit (q : ℕ) :
    Tendsto (fun N : ℕ => (q : ℝ) / N) atTop (nhds 0) :=
  fixedModeProportion_tendsto_zero q

/-- Sharp scalar heat-term bounds for quotient modes in `[0,1]`. -/
theorem exact_heat_term_bounds
    {κ : Type*} [Fintype κ] (mode : κ → ℝ) (t : ℝ)
    (ht : 0 ≤ t) (hmode : ∀ i, 0 ≤ mode i ∧ mode i ≤ 1) :
    (Fintype.card κ : ℝ) * Real.exp (-t) ≤
        ∑ i, Real.exp (-t * mode i) ∧
      (∑ i, Real.exp (-t * mode i)) ≤ Fintype.card κ :=
  quotientHeatTerms_bounds mode t ht hmode

/-- The three displayed lag-one label sets are exact. -/
theorem exact_displayed_label_sets :
    finiteUnitLabelSet 7 = {-6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5} ∧
      finiteUnitLabelSet 10 = {-9, -7, -4, -3, -2, -1, 0, 1, 2, 3, 6, 8} ∧
      finiteUnitLabelSet 12 = {-11, -7, -5, -3, -2, -1, 0, 1, 2, 4, 6, 10} :=
  ⟨baseSeven_finiteUnitLabelSet, baseTen_finiteUnitLabelSet,
    baseTwelve_finiteUnitLabelSet⟩

/-- Every displayed label set contains exactly twelve values. -/
theorem exact_displayed_label_counts :
    (finiteUnitLabelSet 7).card = 12 ∧
      (finiteUnitLabelSet 10).card = 12 ∧
      (finiteUnitLabelSet 12).card = 12 :=
  displayed_finiteUnitLabelSet_cardinalities

#check exact_all_size_slice_table
#check exact_all_size_direct_table
#check exact_base_prime_label_zero
#check exact_centered_reflection
#check exact_parity_gate
#check exact_finite_quotient_action
#check exact_quotient_intertwining
#check exact_surviving_bulk_subspace
#check exact_prime_class_coverage
#check exact_fixed_complexity_limit
#check exact_heat_term_bounds
#check exact_displayed_label_sets
#check exact_displayed_label_counts

#check NField.Alignment.ExponentialDistanceKernel.kernel_chain
#check NField.Alignment.ExponentialDistanceKernel.adjacentRatio_formula
#check NField.Alignment.ExponentialDistanceKernel.adjacentRatio_bounds
#check NField.Alignment.ExponentialDistanceKernel.kernel_posDef
#check NField.Alignment.ExponentialDistanceKernel.precision_mul_kernel
#check NField.Alignment.ExponentialDistanceKernel.kernel_inverse
#check NField.Alignment.ExponentialDistanceKernel.kernel_inverse_quadratic
#check NField.Alignment.ExponentialDistanceKernel.precision_tridiagonal
#check NField.Alignment.ExponentialDistanceKernel.kernel_inverse_adjacent_ne_zero
#check NField.Alignment.ExponentialDistanceKernel.kernel_interval_product
#check NField.Alignment.ExponentialDistanceKernel.kernel_inverse_complex_quadratic
#check NField.Alignment.TridiagonalSimpleSpectrum.eigenvector_zero_of_first_zero
#check NField.Alignment.ExponentialSpectralQuotient.quotient_factor
#check NField.Alignment.ExponentialSpectralQuotient.quotient_posDef
#check NField.Alignment.ExponentialSpectralQuotient.quotient_inverse
#check NField.Alignment.ExponentialSpectralQuotient.quotient_inverse_tridiagonal
#check NField.Alignment.ExponentialSpectralQuotient.quotient_inverse_adjacent
#check NField.Alignment.ExponentialSpectralQuotient.quotient_eigenvalues_injective
#check NField.Alignment.ExponentialSpectralQuotient.quotient_perron
#check NField.Alignment.ExponentialSpectralQuotient.quotient_eigenvalues_bounds
#check NField.Alignment.ExponentialSpectralQuotient.quotient_exists_eigenvalue_one
#check NField.Alignment.ExponentialSpectralQuotient.quotient_modes_bounds
#check NField.Alignment.ExponentialSpectralQuotient.quotient_modes_injective
#check NField.Alignment.ConcreteCollisionBlocks.particleDegree_eq
#check NField.Alignment.ConcreteCollisionBlocks.particleNormalized_eq_blockKernel
#check NField.Alignment.ConcreteCollisionBlocks.blockEmbedding_orthonormal
#check NField.Alignment.ConcreteCollisionBlocks.particleNormalized_factor
#check NField.Alignment.BlockSpectralMultiplicity.particle_spectral_multiset
#check NField.Alignment.ConcreteCollisionSpectrum.particle_bulk_multiplicity
#check NField.Alignment.ConcreteCollisionSpectrum.particle_heat_trace
#check NField.Alignment.ConcreteCollisionSpectrum.particle_heat_trace_bounds
#check NField.Alignment.CanonicalCollisionSpectrum.sorted_label_representation
#check NField.Alignment.CanonicalCollisionSpectrum.integer_bulk_multiplicity
#check NField.Alignment.CanonicalCollisionSpectrum.first_prime_bulk_multiplicity
#check NField.Alignment.CanonicalCollisionSpectrum.eventually_first_prime_bulk
#check NField.Alignment.EventualCollisionLabels.firstPrimeLabelSet_subset
#check NField.Alignment.EventualCollisionLabels.eventually_firstPrimeLabelSet_eq
#check NField.Alignment.DisplayedPrimeSpectra.base_seven_first_three_hundred_labels
#check NField.Alignment.DisplayedPrimeSpectra.base_ten_first_three_hundred_labels
#check NField.Alignment.DisplayedPrimeSpectra.base_twelve_first_three_hundred_labels
#check NField.Alignment.DisplayedPrimeSpectra.displayed_first_three_hundred_counts
#check NField.Alignment.DisplayedPrimeSpectra.displayed_bulk_multiplicities
#check NField.Alignment.CollisionSpectrumSourceDetails.scale_sqrt_ratio
#check NField.Alignment.CollisionSpectrumSourceDetails.particle_diagonal_normalization
#check NField.Alignment.CollisionSpectrumSourceDetails.quotient_ordered_spectrum
#check NField.Alignment.CollisionSpectrumSourceDetails.integer_nontrivial_mode_count
#check NField.Alignment.CollisionSpectrumSourceDetails.first_prime_nontrivial_mode_bound
#check NField.Alignment.CollisionSpectrumSourceDetails.actual_nontrivial_proportion_tendsto_zero

end NField.Papers.TheStructureThatSurvives

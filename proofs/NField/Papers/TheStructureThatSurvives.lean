/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.TheStructureThatSurvives

/-!
# The Structure That Survives

Reader-facing theorem map for the Lean companion to
`papers/the_structure_that_survives.tex`.

## Proved in Lean

* After the diagonal-slice reduction, finite determination holds for every
  positive integer coprime to the base, including the quotient-zero case.
* The intrinsic digit-collision deviation is joined to that all-size table by
  the exact direct collision-to-slice bridge.
* A prime dividing the base has direct collision deviation exactly zero at
  every positive lag.
* The finite unit table obeys the exact reflection law. Adding one half makes
  it odd, and every even Dirichlet-character coefficient vanishes.
* A normalized block-constant particle kernel factors exactly through its
  finite label coordinates.
* The normalized block lift intertwines the full kernel with the quotient
  matrix exactly.
* Every vector with zero sum on each label block is annihilated by the kernel
  and fixed by the squared normalized Laplacian.
* That within-block zero-sum space has exact dimension `N-q`. Thus Lean proves
  the manuscript's exact `N-q`-dimensional eigenvalue-one subspace.
* Dirichlet's theorem, as supplied by Mathlib, gives arbitrarily large primes
  in every unit class.
* A fixed finite number of nontrivial modes has asymptotic proportion zero.
* The scalar heat terms satisfy the manuscript's sharp interval bounds once
  the quotient squared-Laplacian eigenvalues lie in `[0,1]`.
* Exhaustive exact evaluation gives the displayed twelve-element label sets
  for bases seven, ten, and twelve.

## Formalization boundary

This companion is partial. The direct digit-collision-to-diagonal-slice bridge
and the all-size finite table are both closed. The block compression itself
and the `N-q` bulk subspace are exact. The rest
of the manuscript's spectral theorem additionally uses positive definiteness
of the exponential distance matrix, its tridiagonal inverse, irreducibility,
simple spectrum, and Perron--Frobenius. Those facts are not yet assembled for
this concrete kernel. Lean therefore does not yet claim that the eigenvalue
one multiplicity is no larger than `N-q`, nor that all quotient modes are
simple, distinct, and strictly below one.

The full matrix-exponential heat-trace identity and the first-three-hundred-
prime quotient-spectrum regressions are also outside Lean. The displayed
finite label sets themselves are exact Lean certificates. No unchecked
declaration is used, and no manuscript contradiction appeared in the
formalized layer.
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

end NField.Papers.TheStructureThatSurvives

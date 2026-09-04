/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.TheCollisionSpectrum
import NField.Papers.CollisionSpectrumLandscape

/-!
# The Collision Spectrum

Reader-facing theorem map for the Lean companion to
`papers/the_collision_spectrum.tex`.

## Proved in Lean

* The actual centered lag-one finite collision transform is zero-sum and odd
  under reflection.
* At an odd prime base, every nonzero channel of that actual transform is a
  primitive odd Dirichlet character.
* The direct finite table, raw reflection, reflected fiber means, centered
  fiber zero, and generalized Bernoulli floor and fractional-part transforms
  are inherited from the earlier spectrum map.
* The reflection reduction gives the exact factor two.  The floor and diagonal
  terms give the signed Bernoulli-diagonal coefficient product.
* The manuscript's phase-separated coefficient formula follows with the exact
  sign and normalization from the stated classical Bernoulli-to-`L(1,chi)`
  identity.
* Parseval is proved for the actual normalized collision coefficients.
* The primitive-odd population, Bernoulli-to-`L(1,chi)` magnitude identity,
  normalized-weight consequences, and weighted-mean algebra are exact.
* The complete base-five Laurent-polynomial certificate and its magnitude
  consequence are inherited.  The exact centered collision energy is checked
  over all twenty unit classes and equals forty-eight.  The final fourth-moment
  scale is checked as exact algebra from the stated coefficient identity and
  Parseval.
* The Ramanujan arithmetic ledger gives 300 and the diagonal fourth-power
  ledger gives 4,800.
* The declared eighteen-base population formula sums to exactly 14,372
  channels.

## Formalization boundary

This is a partial companion, not a claim that every result in the manuscript is
formalized.  The primitive-odd population formula is proved, but the displayed
primitive-odd character kernel is not yet assembled in Lean.  Consequently the
universal exact diagonal moment is checked only through its downstream
normalization algebra, not from the concrete primitive-character sum.

The direct floor-jump-to-Bernoulli coefficient bridge is still split across
finite lemmas rather than assembled as one theorem about the concrete
coefficient.  The squared-magnitude Bernoulli-to-`L(1,chi)` relation is proved
against Mathlib's analytically continued Dirichlet `L`-function.  The
phase-complete root-number convention remains an explicit hypothesis in the
phase-separated algebra, and the fourth `L`-value moment is proved as a
consequence of that input plus Parseval.

The rounded Pearson correlations are exhaustive nfield computations, not Lean
theorems.  No limiting correlation, decay law, critical-strip statement, or
zero-location claim is made.  No unchecked declaration is used, and no
manuscript contradiction appeared in the formalized layer.
-/

namespace NField.Papers.TheCollisionSpectrum

open scoped BigOperators ComplexConjugate
open NField.Alignment.CollisionFluctuationSum
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionTransformStrip
open NField.Alignment.NeutralityTheorem
open NField.Alignment.PrimitiveOddBoundaryMean
open NField.Alignment.CollisionSpectrumLandscape
open NField.Alignment.CollisionTransform
open NField.Alignment.TheCollisionSpectrum
open NField.Papers.DoubleTransversality

/-! ## Concrete finite collision data -/

/-- The direct collision deviation is exactly the finite table on every
eligible residue progression. -/
theorem exact_finite_determination
    {b ell t a : ℕ} (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (ha : 1 ≤ a) (halt : a < allLagModulus b ell)
    (hcop : a.Coprime (allLagModulus b ell)) :
    directAllLagDeviation b ell (allLagModulus b ell * t + a) =
      allLagTable b ell a :=
  NField.Papers.CollisionSpectrumLandscape.exact_finite_determination
    hb2 hell ha halt hcop

/-- The raw collision table has reflected sum negative one. -/
theorem exact_raw_reflection
    {b ell : ℕ} [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (a : UnitClass (allLagModulus b ell)) :
    allLagUnitTable b ell a + allLagUnitTable b ell (-a) = -1 :=
  NField.Papers.CollisionSpectrumLandscape.raw_collision_table_reflection
    hb2 hell a

/-- Reflected reduction-fiber means sum to negative one. -/
theorem exact_fiber_mean_reflection
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell) (u : UnitClass b) :
    fiberMean (coarseUnitReduction b ell) (allLagUnitTable b ell) u +
        fiberMean (coarseUnitReduction b ell) (allLagUnitTable b ell) (-u) =
      -1 :=
  NField.Papers.CollisionSpectrumLandscape.collision_fiber_mean_reflection
    hb2 hell u

/-- Every reduction fiber of the centered collision table has zero sum. -/
theorem exact_centered_fiber_sum_zero
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (u : UnitClass b) :
    ∑ a : Fiber (coarseUnitReduction b ell) u,
      centeredCollisionTable b ell a = 0 :=
  NField.Papers.CollisionSpectrumLandscape.centered_collision_fiber_sum_zero u

/-- Every even character coefficient vanishes. -/
theorem exact_even_character_gate
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (χ : Character (allLagModulus b ell))
    (heven : χ (-1 : ZMod (allLagModulus b ell)) = 1) :
    collisionCoefficient (centeredCollisionTable b ell) χ = 0 :=
  NField.Papers.CollisionSpectrumLandscape.even_character_gate
    hb2 hell χ heven

/-- Every character factored through base reduction vanishes. -/
theorem exact_base_factored_character_gate
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (ψ : UnitClass b → ℂ) (χ : Character (allLagModulus b ell))
    (hfactor : ∀ a, χ a.val = ψ (coarseUnitReduction b ell a)) :
    collisionCoefficient (centeredCollisionTable b ell) χ = 0 :=
  NField.Papers.CollisionSpectrumLandscape.base_factored_character_gate
    ψ χ hfactor

/-! ## Character and moment transforms -/

/-- The concrete centered collision spectrum is exactly odd. -/
theorem exact_reflection
    {b : ℕ} [NeZero b] [NeZero (allLagModulus b 1)]
    (hb2 : 2 ≤ b) (a : UnitClass (allLagModulus b 1)) :
    centeredLagOneSpectrum b (-a) = -centeredLagOneSpectrum b a :=
  centeredLagOneSpectrum_odd hb2 a

/-- The concrete centered collision spectrum has zero total mass. -/
theorem exact_centered_sum_zero
    {b : ℕ} [NeZero b] [NeZero (allLagModulus b 1)] :
    ∑ a, centeredLagOneSpectrum b a = 0 :=
  centeredLagOneSpectrum_sum_zero

/-- Every active prime-base channel is primitive and odd. -/
theorem exact_primitive_odd_gate
    {b : ℕ} (hb : Nat.Prime b)
    [NeZero b] [NeZero (allLagModulus b 1)]
    {χ : Character (allLagModulus b 1)}
    (hactive : collisionCoefficient (centeredLagOneSpectrum b) χ ≠ 0) :
    χ.IsPrimitive ∧ χ.Odd :=
  activeLagOneChannel_primitive_and_odd hb hactive

/-- Exact finite fractional-part reindexing behind the generalized Bernoulli
factor. -/
theorem exact_fractional_part_transform
    {q : ℕ} [NeZero q] (ψ : Character q) (u : UnitClass q) :
    fractionalPartTransform ψ u =
      ψ (u⁻¹ : UnitClass q).val * generalizedBernoulliOne ψ :=
  fractionalPartTransform_eq ψ u

/-- Exact floor transform for every primitive character and unit multiplier. -/
theorem exact_floor_transform
    {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : Character q} (hχ : χ.IsPrimitive) (k : UnitClass q) :
    (∑ a : UnitClass q,
        (((k.val.val * a.val.val) / q : ℕ) : ℂ) * χ⁻¹ a.val) =
      ((k.val.val : ℂ) - χ k.val) * generalizedBernoulliOne χ⁻¹ :=
  NField.Papers.CollisionSpectrumLandscape.exact_floor_transform hq hχ k

/-- Exact factor two from diagonal reflection. -/
theorem exact_diagonal_reduction
    {ι : Type*} [Fintype ι]
    (initial reflected : ι → ℂ) (α : ℂ)
    (hreflect : ∀ i, reflected i = -α * initial i) :
    (∑ i, reflected i) - α * ∑ i, initial i =
      -2 * α * ∑ i, initial i :=
  diagonal_reduction_from_reflection initial reflected α hreflect

/-- Exact Bernoulli-diagonal factorization algebra after the concrete finite
transforms have been identified. -/
theorem exact_collision_factorization
    (b : ℕ) (B G floorMoment diagonalMoment φ : ℂ)
    (hfloor : floorMoment = -(b : ℂ) * B)
    (hdiagonal : diagonalMoment = B * ((b : ℂ) - star G)) :
    φ⁻¹ * (floorMoment + diagonalMoment) = -(B * star G) / φ := by
  apply normalized_collision_factorization
  exact floor_diagonal_cancellation b B G floorMoment diagonalMoment
    hfloor hdiagonal

/-- Exact phase-separated formula from the manuscript's classical analytic
input and finite factorization. -/
theorem exact_phase_separation
    (base step B epsilon L A G coefficient : ℂ)
    (hbase : base ≠ 0) (hstep : step ≠ 0)
    (hB : B = -(base / Real.pi) * epsilon * L)
    (hG : G = 2 * A)
    (hcoefficient : coefficient = -(B * star G) / (base * step)) :
    coefficient = (2 / (Real.pi * step)) * epsilon * L * star A :=
  phaseSeparated_coefficient_algebra base step B epsilon L A G coefficient
    hbase hstep hB hG hcoefficient

/-- Parseval for the actual centered lag-one spectrum. -/
theorem exact_collision_parseval
    {b : ℕ} [NeZero b] [NeZero (allLagModulus b 1)] :
    ∑ χ : Character (allLagModulus b 1),
        ‖collisionCoefficient (centeredLagOneSpectrum b) χ‖ ^ 2 =
      ((allLagModulus b 1).totient : ℝ)⁻¹ *
        ∑ a : UnitClass (allLagModulus b 1),
          ‖centeredLagOneSpectrum b a‖ ^ 2 :=
  centeredLagOneSpectrum_parseval

/-- The primitive odd population at an odd prime square is exactly half the
square of one less than the base. -/
theorem exact_primitive_odd_population
    {b : ℕ} [NeZero (b ^ 2)] [NeZero b]
    (hb : b.Prime) (hbodd : b ≠ 2) :
    (primitiveOddCharacterCount (b ^ 2) : ℝ) =
      (((b - 1) ^ 2 : ℕ) : ℝ) / 2 :=
  NField.Papers.CollisionSpectrumLandscape.exact_primitive_odd_population
    hb hbodd

/-- Squared magnitudes of the factored coefficients give the exact weighted
finite Bernoulli-diagonal moment. -/
theorem exact_factored_coefficient_moment
    {ι : Type*} [Fintype ι]
    (coefficient bernoulli diagonal : ι → ℂ) (φ : ℂ)
    (hfactor : ∀ i,
      coefficient i = -(φ⁻¹ * (bernoulli i * star (diagonal i)))) :
    ∑ i, Complex.normSq (coefficient i) =
      Complex.normSq φ⁻¹ *
        ∑ i, Complex.normSq (bernoulli i) *
          Complex.normSq (diagonal i) :=
  NField.Papers.CollisionSpectrumLandscape.exact_factored_coefficient_moment
    coefficient bernoulli diagonal φ hfactor

/-- An exact diagonal moment normalizes the collision weights to one. -/
theorem exact_normalized_weight_sum
    {ι : Type*} [Fintype ι]
    (scale : ℝ) (diagonal : ι → ℂ) (hscale : scale ≠ 0)
    (hmoment : ∑ i, Complex.normSq (diagonal i) = scale) :
    ∑ i, normalizedCollisionWeight scale diagonal i = 1 :=
  normalizedCollisionWeight_sum_one scale diagonal hscale hmoment

/-- The weighted special-value expectation is the exact normalized moment. -/
theorem exact_weighted_special_value_mean
    {ι : Type*} [Fintype ι]
    (scale constant energy : ℝ)
    (diagonal : ι → ℂ) (specialValueSq : ι → ℝ)
    (hscale : scale ≠ 0)
    (hmoment :
      ∑ i, Complex.normSq (diagonal i) * specialValueSq i =
        constant * energy) :
    ∑ i, normalizedCollisionWeight scale diagonal i * specialValueSq i =
      constant * energy / scale :=
  normalizedCollisionWeight_specialValue_mean scale constant energy
    diagonal specialValueSq hscale hmoment

/-- Exact squared-magnitude form of the primitive odd relation between the
generalized Bernoulli sum and the Dirichlet `L`-function at one. -/
theorem exact_bernoulli_l_value_magnitude
    {b : ℕ} [NeZero (b ^ 2)] {χ : Character (b ^ 2)}
    (hb : b.Prime) (hχ : χ.IsPrimitive) (hodd : χ.Odd) :
    Complex.normSq (generalizedBernoulliOne χ⁻¹) =
      ((b ^ 2 : ℕ) : ℝ) / Real.pi ^ 2 *
        Complex.normSq (DirichletCharacter.LFunction χ 1) :=
  NField.Papers.CollisionSpectrumLandscape.exact_bernoulli_l_value_magnitude
    hb hχ hodd

/-- The complete base-five cyclotomic certificate. -/
theorem exact_base_five_cyclotomic_certificate (z : ℂ) (hz : z ≠ 0) :
    z ^ 7 *
        (baseFiveBernoulliPolynomial z *
            baseFiveBernoulliPolynomial z⁻¹ -
          5 * baseFiveShortPolynomial z * baseFiveShortPolynomial z⁻¹) =
      cyclotomicTwentyValue z * baseFiveCertificateQuotient z :=
  baseFive_laurent_polynomial_identity z hz

/-- Exact base-five magnitude relation forced by the cyclotomic certificate. -/
theorem exact_base_five_diagonal_bernoulli_magnitude
    (z α : ℂ) (hz : z ≠ 0) (hstar : star z = z⁻¹)
    (hcyclotomic : cyclotomicTwentyValue z = 0)
    (hα : Complex.normSq α = 1) :
    Complex.normSq (-2 * α * baseFiveShortPolynomial z) =
      5 * Complex.normSq
        (-(2 / 5 : ℂ) * baseFiveBernoulliPolynomial z) :=
  baseFive_diagonal_bernoulli_normSq z α hz hstar hcyclotomic hα

/-- Exact exhaustive centered collision energy at base five. -/
theorem exact_base_five_collision_energy :
    rationalCollisionEnergy 5 = 48 :=
  baseFive_rational_collision_energy

/-- The complete base-five table has twenty unit classes, energy forty-eight,
and zero total on every reduction fiber. -/
theorem exact_base_five_complete_table :
    (reducedResidues 25).card = 20 ∧
      rationalCollisionEnergy 5 = 48 ∧
      ∀ u ∈ reducedResidues 5, exactCenteredFiberTotal 5 1 u = 0 :=
  baseFive_complete_table_certificate

/-- Exact finite arithmetic in the base-five fourth-power ledger. -/
theorem exact_base_five_fourth_power_ledgers :
    ((32 : ℤ) * 8 + 28 * 2 + 14 * (-2) + 34 * 2 + 18 * (-2) +
      2 * (-8) = 300) ∧
      (16 : ℤ) * 300 = 4800 :=
  ⟨baseFive_ramanujan_fourth_power_ledger,
    baseFive_diagonal_fourth_power_ledger⟩

/-- The base-five coefficient scale and Parseval imply the exact fourth-moment
normalization used by the manuscript. -/
theorem exact_base_five_fourth_moment_from_parseval
    (fourthMoment coefficientEnergy collisionEnergy : ℝ)
    (hpi : Real.pi ≠ 0)
    (hcoefficient :
      coefficientEnergy =
        (125 / (16 * Real.pi ^ 4)) * fourthMoment)
    (hparseval : coefficientEnergy = collisionEnergy / 20) :
    fourthMoment = (4 * Real.pi ^ 4 / 625) * collisionEnergy :=
  baseFive_fourth_moment_from_parseval fourthMoment coefficientEnergy
    collisionEnergy hpi hcoefficient hparseval

/-- The declared finite character ledger contains exactly 14,372 channels. -/
theorem exact_declared_channel_count :
    ∑ b ∈ spectrumLedgerBases, declaredPrimitiveOddPopulation b = 14372 :=
  spectrumLedger_declared_channel_count

#check exact_finite_determination
#check exact_raw_reflection
#check exact_fiber_mean_reflection
#check exact_centered_fiber_sum_zero
#check exact_even_character_gate
#check exact_base_factored_character_gate
#check exact_reflection
#check exact_centered_sum_zero
#check exact_primitive_odd_gate
#check exact_fractional_part_transform
#check exact_floor_transform
#check exact_diagonal_reduction
#check exact_collision_factorization
#check exact_phase_separation
#check exact_collision_parseval
#check exact_primitive_odd_population
#check exact_factored_coefficient_moment
#check exact_normalized_weight_sum
#check exact_weighted_special_value_mean
#check exact_bernoulli_l_value_magnitude
#check exact_base_five_cyclotomic_certificate
#check exact_base_five_diagonal_bernoulli_magnitude
#check exact_base_five_collision_energy
#check exact_base_five_complete_table
#check exact_base_five_fourth_power_ledgers
#check exact_base_five_fourth_moment_from_parseval
#check exact_declared_channel_count

end NField.Papers.TheCollisionSpectrum

/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimitiveReductionFiber
import NField.Alignment.LandscapeActualSpectrum
import NField.Alignment.LandscapeSpecialValueMoment
import NField.Alignment.BaseFiveCharacterPolynomial
import NField.Alignment.BaseFiveCollisionEnergy
import NField.Alignment.BaseFiveSpecialValue
import NField.Alignment.BaseFiveLaurentLedger
import NField.Alignment.BaseFiveCharacterRoots
import NField.Alignment.BaseFiveFourthMomentDetails
import NField.Alignment.PrimitiveNaturalFloorTransform
import NField.Alignment.LandscapeSourceMoments
import NField.Alignment.BaseFiveArithmeticDetails
import NField.Alignment.LandscapeCorrelationScaling
import NField.Alignment.CollisionSpectrumLandscape
import NField.Alignment.PrimitiveFloorTransform
import NField.Alignment.PrimitiveOddBoundaryMean
import NField.Alignment.SawtoothLValue
import NField.Alignment.TheCollisionSpectrum
import NField.Papers.SpectralRepulsion

/-!
# The Collision Spectrum and the L-Function Landscape

Reader-facing theorem map for the Lean companion to
`papers/collision_spectrum_landscape.tex`.

## Checked here

* The direct collision deviation is exactly determined by the finite table.
  The raw table, reflected fiber means, centered fiber sums, and centered
  reflection identities are all exact.  Even and base-factored channels
  vanish, and every active prime-square channel is primitive and odd.
* The generalized Bernoulli sum is defined directly on the finite unit group.
  Multiplication by any unit proves the manuscript's exact fractional-part
  reindexing, with the inverse-character factor exposed explicitly.
* Reflection of the two diagonal halves gives the exact factor two and its
  magnitude form.  The floor and diagonal moments cancel their base-sized
  terms, leaving the signed Bernoulli-diagonal product.  Normalization gives
  the displayed coefficient factorization algebra.
* The primitive floor transform and the primitive-odd population formula are
  exact.  Factored coefficients satisfy the exact weighted finite moment identity.
  Independently, the concrete normalized collision coefficients satisfy the
  manuscript's exact Parseval normalization on the full character group.
* The classical primitive-odd Bernoulli-to-`L(1,chi)` magnitude relation is
  proved against Mathlib's analytically continued Dirichlet `L`-function.
* Lean expands and proves the complete base-five Laurent-polynomial identity.
  At a nonzero twentieth-cyclotomic root on the unit circle, this forces the
  exact magnitude-square ratio five.  With the Bernoulli and diagonal scales,
  it gives `|S_G|^2 = 5 |B_1|^2`.
* Exact evaluation of all twenty unit classes modulo twenty-five gives
  centered collision energy forty-eight and checks zero total on every coarse
  fiber.

## Exact source assembly

The actual primitive coefficient, diagonal reduction, weighted special-value
moment and exact base-five fourth moment are proved without factorization
hypotheses. Primitive reduction fibers, every natural floor multiplier, the
separate floor and diagonal moments, actual generator exponents, Bernoulli
polynomials and the literal Laurent/Ramanujan ledger are connected explicitly.
The original twenty-five declarations retain their statements; the additional
forty-six selected results supply the concrete source correspondences.

The correlations for bases five through seventy-one remain exhaustive nfield
evidence rather than Lean theorems.  No asymptotic correlation, decay law,
critical-strip statement, or zero-location claim is asserted.

No manuscript contradiction appeared in the formalized finite layer, and no
unchecked declaration is used.
-/

namespace NField.Papers.CollisionSpectrumLandscape

open scoped BigOperators ComplexConjugate
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionFluctuationSum
open NField.Alignment.CollisionTransformStrip
open NField.Alignment.DoubleTransversality
open NField.Alignment.NeutralityTheorem
open NField.Alignment.SpectralRepulsion
open NField.Alignment.CollisionSpectrumLandscape
open NField.Alignment.CollisionTransform
open NField.Alignment.CarryBoundarySpectra
open NField.Alignment.PrimitiveFloorTransform
open NField.Alignment.PrimitiveOddBoundaryMean
open NField.Alignment.SawtoothLValue
open NField.Papers.DoubleTransversality

/-! ## Concrete centered collision table -/

/-- The direct collision deviation is exactly the finite table on every
eligible residue progression. -/
theorem exact_finite_determination
    {b ell t a : ℕ} (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (ha : 1 ≤ a) (halt : a < allLagModulus b ell)
    (hcop : a.Coprime (allLagModulus b ell)) :
    directAllLagDeviation b ell (allLagModulus b ell * t + a) =
      allLagTable b ell a :=
  NField.Papers.SpectralRepulsion.exact_finite_determination
    hb2 hell ha halt hcop

/-- The raw collision table has reflected sum negative one. -/
theorem raw_collision_table_reflection
    {b ell : ℕ} [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (a : UnitClass (allLagModulus b ell)) :
    allLagUnitTable b ell a + allLagUnitTable b ell (-a) = -1 :=
  NField.Papers.SpectralRepulsion.raw_collision_table_reflection
    hb2 hell a

/-- Reflected reduction-fiber means sum to negative one. -/
theorem collision_fiber_mean_reflection
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell) (u : UnitClass b) :
    fiberMean (coarseUnitReduction b ell) (allLagUnitTable b ell) u +
        fiberMean (coarseUnitReduction b ell) (allLagUnitTable b ell) (-u) =
      -1 :=
  NField.Papers.SpectralRepulsion.collision_fiber_mean_reflection
    hb2 hell u

/-- Every reduction fiber of the centered collision table has zero sum. -/
theorem centered_collision_fiber_sum_zero
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (u : UnitClass b) :
    ∑ a : Fiber (coarseUnitReduction b ell) u,
      centeredCollisionTable b ell a = 0 :=
  NField.Papers.SpectralRepulsion.centered_collision_fiber_sum_zero u

/-- The concrete centered collision table has zero global sum. -/
theorem centered_collision_table_sum_zero
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)] :
    ∑ a, centeredCollisionTable b ell a = 0 :=
  NField.Papers.DoubleTransversality.centered_collision_table_sum_zero

/-- The concrete centered collision table is exactly odd under reflection. -/
theorem centered_collision_table_odd
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (a : UnitClass (allLagModulus b ell)) :
    centeredCollisionTable b ell (-a) = -centeredCollisionTable b ell a :=
  NField.Papers.DoubleTransversality.exact_centered_reflection hb2 hell a

/-- Every even character coefficient vanishes. -/
theorem even_character_gate
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (χ : Character (allLagModulus b ell))
    (heven : χ (-1 : ZMod (allLagModulus b ell)) = 1) :
    collisionCoefficient (centeredCollisionTable b ell) χ = 0 :=
  NField.Papers.SpectralRepulsion.even_character_gate
    hb2 hell χ heven

/-- Every character factored through base reduction vanishes. -/
theorem base_factored_character_gate
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (ψ : UnitClass b → ℂ) (χ : Character (allLagModulus b ell))
    (hfactor : ∀ a, χ a.val = ψ (coarseUnitReduction b ell a)) :
    collisionCoefficient (centeredCollisionTable b ell) χ = 0 :=
  NField.Papers.SpectralRepulsion.base_factored_character_gate
    ψ χ hfactor

/-- At prime base, every nonzero lag-one channel of the actual centered table
is primitive and odd. -/
theorem active_lag_one_channel_primitive_and_odd
    {b : ℕ} (hb : Nat.Prime b)
    [NeZero b] [NeZero (allLagModulus b 1)]
    {χ : Character (allLagModulus b 1)}
    (hactive : collisionCoefficient (centeredCollisionTable b 1) χ ≠ 0) :
    χ.IsPrimitive ∧ χ.Odd := by
  apply primeBase_active_primitive_and_odd hb
  apply mem_transformActiveCharacters_iff.mpr
  simpa [centeredCollisionTable, centeredCollisionTransform] using hactive

/-! ## Bernoulli and diagonal transforms -/

/-- Exact finite fractional-part transform under multiplication by a unit. -/
theorem exact_fractional_part_transform
    {q : ℕ} [NeZero q] (ψ : Character q) (u : UnitClass q) :
    fractionalPartTransform ψ u =
      ψ (u⁻¹ : UnitClass q).val * generalizedBernoulliOne ψ :=
  fractionalPartTransform_eq ψ u

/-- The unit-group Bernoulli sum is the standard residue-ring Bernoulli sum,
because a Dirichlet character vanishes on nonunits. -/
theorem generalizedBernoulliOne_eq_bernoulliOne
    {q : ℕ} [NeZero q] (ψ : Character q) :
    generalizedBernoulliOne ψ = bernoulliOne ψ := by
  unfold generalizedBernoulliOne bernoulliOne
  rw [sum_character_pairing_eq_units
    (fun x : ZMod q => (x.val : ℂ)) ψ]

/-- Exact floor transform for every primitive character and unit multiplier. -/
theorem exact_floor_transform
    {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : Character q} (hχ : χ.IsPrimitive) (k : UnitClass q) :
    (∑ a : UnitClass q,
        (((k.val.val * a.val.val) / q : ℕ) : ℂ) * χ⁻¹ a.val) =
      ((k.val.val : ℂ) - χ k.val) * generalizedBernoulliOne χ⁻¹ := by
  rw [generalizedBernoulliOne_eq_bernoulliOne]
  exact primitiveFloorTransform hq hχ k

/-- Exact factor two forced by reflection of the diagonal halves. -/
theorem exact_diagonal_reduction
    {ι : Type*} [Fintype ι]
    (initial reflected : ι → ℂ) (α : ℂ)
    (hreflect : ∀ i, reflected i = -α * initial i) :
    (∑ i, reflected i) - α * ∑ i, initial i =
      -2 * α * ∑ i, initial i :=
  diagonal_reduction_from_reflection initial reflected α hreflect

/-- The exact normalized collision factorization once the finite floor and
diagonal transforms have been identified. -/
theorem exact_collision_factorization
    (b : ℕ) (B G floorMoment diagonalMoment φ : ℂ)
    (hfloor : floorMoment = -(b : ℂ) * B)
    (hdiagonal : diagonalMoment = B * ((b : ℂ) - star G)) :
    φ⁻¹ * (floorMoment + diagonalMoment) =
      -(B * star G) / φ := by
  apply normalized_collision_factorization
  exact floor_diagonal_cancellation b B G floorMoment diagonalMoment
    hfloor hdiagonal

/-! ## Exact finite moments -/

/-- The universal primitive-odd population at an odd prime square is exactly
half the square of `b - 1`. -/
theorem exact_primitive_odd_population
    {b : ℕ} [NeZero (b ^ 2)] [NeZero b]
    (hb : b.Prime) (hbodd : b ≠ 2) :
    (primitiveOddCharacterCount (b ^ 2) : ℝ) =
      (((b - 1) ^ 2 : ℕ) : ℝ) / 2 := by
  have h := primitiveOddCharacterCount_primePower_real
    (p := b) (N := 2) hb hbodd (by omega)
  rw [Nat.totient_prime_pow hb (by omega : 0 < 2),
    Nat.totient_prime_pow hb (by omega : 0 < 2 - 1)] at h
  norm_num at h
  have hb1 : 1 ≤ b := hb.one_le
  rw [Nat.cast_sub hb1] at h
  have hcast : (((b - 1) ^ 2 : ℕ) : ℝ) = ((b : ℝ) - 1) ^ 2 := by
    rw [Nat.cast_pow, Nat.cast_sub hb1]
    norm_num
  rw [hcast]
  nlinarith

/-- Squared magnitudes of the factored coefficients give the weighted finite
Bernoulli-diagonal moment. -/
theorem exact_factored_coefficient_moment
    {ι : Type*} [Fintype ι]
    (coefficient bernoulli diagonal : ι → ℂ) (φ : ℂ)
    (hfactor : ∀ i,
      coefficient i = -(φ⁻¹ * (bernoulli i * star (diagonal i)))) :
    ∑ i, Complex.normSq (coefficient i) =
      Complex.normSq φ⁻¹ *
        ∑ i, Complex.normSq (bernoulli i) *
          Complex.normSq (diagonal i) :=
  factored_coefficient_moment coefficient bernoulli diagonal φ hfactor

/-- Parseval for the actual normalized collision coefficients. -/
theorem exact_collision_parseval
    {q : ℕ} [NeZero q] (F : UnitClass q → ℂ) :
    ∑ χ : Character q, ‖collisionCoefficient F χ‖ ^ 2 =
      (q.totient : ℝ)⁻¹ * ∑ r : UnitClass q, ‖F r‖ ^ 2 :=
  collisionCoefficient_parseval F

/-! ## The value at one -/

/-- Exact squared-magnitude form of the classical primitive-odd relation
between the generalized Bernoulli sum and Mathlib's analytically continued
Dirichlet `L`-function at one. -/
theorem exact_bernoulli_l_value_magnitude
    {b : ℕ} [NeZero (b ^ 2)] {χ : Character (b ^ 2)}
    (hb : b.Prime) (hχ : χ.IsPrimitive) (hodd : χ.Odd) :
    Complex.normSq (generalizedBernoulliOne χ⁻¹) =
      ((b ^ 2 : ℕ) : ℝ) / Real.pi ^ 2 *
        Complex.normSq (DirichletCharacter.LFunction χ 1) := by
  have hoddInv : (χ⁻¹).Odd := by
    change χ⁻¹ (-1) = -1
    rw [MulChar.inv_apply_eq_inv', hodd]
    norm_num
  have h := bernoulliOne_normSq_eq_LFunction
    (N := b ^ 2) (by nlinarith [hb.two_le])
    (inverse_isPrimitive hχ) hoddInv
  rw [← generalizedBernoulliOne_eq_bernoulliOne] at h
  simpa using h

/-! ## Exact base-five sector -/

/-- The complete Laurent-polynomial certificate is an exact identity. -/
theorem base_five_cyclotomic_certificate (z : ℂ) (hz : z ≠ 0) :
    z ^ 7 *
        (baseFiveBernoulliPolynomial z *
            baseFiveBernoulliPolynomial z⁻¹ -
          5 * baseFiveShortPolynomial z * baseFiveShortPolynomial z⁻¹) =
      cyclotomicTwentyValue z * baseFiveCertificateQuotient z :=
  baseFive_laurent_polynomial_identity z hz

/-- Exact base-five relation between diagonal and Bernoulli magnitudes. -/
theorem base_five_diagonal_bernoulli_magnitude
    (z α : ℂ) (hz : z ≠ 0) (hstar : star z = z⁻¹)
    (hcyclotomic : cyclotomicTwentyValue z = 0)
    (hα : Complex.normSq α = 1) :
    Complex.normSq (-2 * α * baseFiveShortPolynomial z) =
      5 * Complex.normSq
        (-(2 / 5 : ℂ) * baseFiveBernoulliPolynomial z) :=
  baseFive_diagonal_bernoulli_normSq z α hz hstar hcyclotomic hα

/-- Direct exhaustive base-five collision energy. -/
theorem base_five_collision_energy :
    rationalCollisionEnergy 5 = 48 :=
  baseFive_rational_collision_energy

/-- Complete twenty-unit and fiber-neutrality certificate at base five. -/
theorem base_five_complete_table_certificate :
    (reducedResidues 25).card = 20 ∧
      rationalCollisionEnergy 5 = 48 ∧
      ∀ u ∈ reducedResidues 5, exactCenteredFiberTotal 5 1 u = 0 :=
  baseFive_complete_table_certificate

/-- The exact Ramanujan arithmetic and diagonal fourth-power ledgers used in
the base-five energy calculation. -/
theorem base_five_fourth_power_ledgers :
    ((32 : ℤ) * 8 + 28 * 2 + 14 * (-2) + 34 * 2 + 18 * (-2) +
      2 * (-8) = 300) ∧
      (16 : ℤ) * 300 = 4800 :=
  ⟨NField.Alignment.TheCollisionSpectrum.baseFive_ramanujan_fourth_power_ledger,
    NField.Alignment.TheCollisionSpectrum.baseFive_diagonal_fourth_power_ledger⟩

/-- The base-five coefficient law and Parseval normalization force the exact
fourth-moment scale. -/
theorem base_five_fourth_moment_from_parseval
    (fourthMoment coefficientEnergy collisionEnergy : ℝ)
    (hcoefficient :
      coefficientEnergy =
        (125 / (16 * Real.pi ^ 4)) * fourthMoment)
    (hparseval : coefficientEnergy = collisionEnergy / 20) :
    fourthMoment = (4 * Real.pi ^ 4 / 625) * collisionEnergy :=
  NField.Alignment.TheCollisionSpectrum.baseFive_fourth_moment_from_parseval
    fourthMoment coefficientEnergy collisionEnergy Real.pi_ne_zero
    hcoefficient hparseval

/-- The declared eighteen-base finite ledger contains 14,372 primitive odd
character channels. -/
theorem declared_ledger_channel_count :
    ∑ b ∈ NField.Alignment.TheCollisionSpectrum.spectrumLedgerBases,
      NField.Alignment.TheCollisionSpectrum.declaredPrimitiveOddPopulation b =
        14372 :=
  NField.Alignment.TheCollisionSpectrum.spectrumLedger_declared_channel_count

#check exact_finite_determination
#check raw_collision_table_reflection
#check collision_fiber_mean_reflection
#check centered_collision_fiber_sum_zero
#check centered_collision_table_sum_zero
#check centered_collision_table_odd
#check even_character_gate
#check base_factored_character_gate
#check active_lag_one_channel_primitive_and_odd
#check exact_fractional_part_transform
#check generalizedBernoulliOne_eq_bernoulliOne
#check exact_floor_transform
#check exact_diagonal_reduction
#check exact_collision_factorization
#check exact_primitive_odd_population
#check exact_factored_coefficient_moment
#check exact_collision_parseval
#check exact_bernoulli_l_value_magnitude
#check base_five_cyclotomic_certificate
#check base_five_diagonal_bernoulli_magnitude
#check base_five_collision_energy
#check base_five_complete_table_certificate
#check base_five_fourth_power_ledgers
#check base_five_fourth_moment_from_parseval
#check declared_ledger_channel_count

#check NField.Alignment.PrimitiveReductionFiber.primitive_nontrivial_kernel
#check NField.Alignment.PrimitiveReductionFiber.primitive_fiber_sum_zero
#check NField.Alignment.PrimitiveReductionFiber.primitive_reduction_weight_sum_zero
#check NField.Alignment.LandscapeActualSpectrum.diagonalBoundary_eq_short_sum
#check NField.Alignment.LandscapeActualSpectrum.diagonalBoundary_norm
#check NField.Alignment.LandscapeActualSpectrum.actual_collision_coefficient
#check NField.Alignment.LandscapeActualSpectrum.actual_centered_collision_coefficient
#check NField.Alignment.LandscapeActualSpectrum.bernoulli_l_value_norm
#check NField.Alignment.LandscapeActualSpectrum.actual_coefficient_l_value_norm
#check NField.Alignment.LandscapeSpecialValueMoment.actual_primitive_parseval
#check NField.Alignment.LandscapeSpecialValueMoment.actual_special_value_moment
#check NField.Alignment.BaseFiveCharacterPolynomial.short_character_polynomial
#check NField.Alignment.BaseFiveCharacterPolynomial.bernoulli_character_polynomial
#check NField.Alignment.BaseFiveCharacterPolynomial.primitive_odd_cyclotomic_twenty
#check NField.Alignment.BaseFiveCollisionEnergy.base_five_actual_collision_energy
#check NField.Alignment.BaseFiveSpecialValue.actual_short_bernoulli_norm_sq
#check NField.Alignment.BaseFiveSpecialValue.actual_diagonal_bernoulli_norm
#check NField.Alignment.BaseFiveSpecialValue.actual_coefficient_l_value
#check NField.Alignment.BaseFiveSpecialValue.actual_l_value_fourth_moment
#check NField.Alignment.BaseFiveLaurentLedger.short_laurent_expansion
#check NField.Alignment.BaseFiveLaurentLedger.even_square_mod_twenty
#check NField.Alignment.BaseFiveLaurentLedger.actual_ramanujan_twenty_values
#check NField.Alignment.BaseFiveLaurentLedger.actual_ramanujan_twenty_odd_zero
#check NField.Alignment.BaseFiveCharacterRoots.generator_order
#check NField.Alignment.BaseFiveCharacterRoots.character_value_isPrimitiveRoot
#check NField.Alignment.BaseFiveCharacterRoots.characterExponent_bijective
#check NField.Alignment.BaseFiveFourthMomentDetails.actual_short_bernoulli_norm
#check NField.Alignment.BaseFiveFourthMomentDetails.actual_coefficient_diagonal_fourth
#check NField.Alignment.BaseFiveFourthMomentDetails.actual_diagonal_fourth_moment
#check NField.Alignment.BaseFiveFourthMomentDetails.actual_initial_fourth_moment
#check NField.Alignment.BaseFiveFourthMomentDetails.primitive_root_fourth_moment
#check NField.Alignment.PrimitiveNaturalFloorTransform.primitive_fractional_transform
#check NField.Alignment.PrimitiveNaturalFloorTransform.primitive_natural_floor_transform
#check NField.Alignment.PrimitiveNaturalFloorTransform.primitive_floor_jump_transform
#check NField.Alignment.LandscapeSourceMoments.prime_base_character_zero
#check NField.Alignment.LandscapeSourceMoments.primitive_base_floor_moment
#check NField.Alignment.LandscapeSourceMoments.primitive_diagonal_floor_moment
#check NField.Alignment.LandscapeSourceMoments.primitive_centering_removal
#check NField.Alignment.LandscapeSourceMoments.primitive_raw_coefficient_sum
#check NField.Alignment.LandscapeSourceMoments.actual_coefficient_short_l_norm
#check NField.Alignment.BaseFiveArithmeticDetails.residue_power_list
#check NField.Alignment.BaseFiveArithmeticDetails.primitive_exponent_list
#check NField.Alignment.BaseFiveArithmeticDetails.paired_residue_powers
#check NField.Alignment.BaseFiveArithmeticDetails.paired_character_powers
#check NField.Alignment.BaseFiveArithmeticDetails.paired_bernoulli_polynomial
#check NField.Alignment.LandscapeCorrelationScaling.actual_bernoulli_l_correlation

end NField.Papers.CollisionSpectrumLandscape

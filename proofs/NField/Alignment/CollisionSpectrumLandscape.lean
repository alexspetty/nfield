/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.SpectralRepulsion

/-!
# Collision spectrum and boundary landscape

Finite Bernoulli-transform, coefficient-factorization, cyclotomic, and exact
energy algebra for the Lean companion to
"The Collision Spectrum and the L-Function Landscape".
-/

namespace NField.Alignment.CollisionSpectrumLandscape

open scoped BigOperators ComplexConjugate
open NField.Alignment.CollisionFluctuationSum
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionTransformStrip
open NField.Alignment.NeutralityTheorem

/-! ## The finite generalized Bernoulli transform -/

/-- The first generalized Bernoulli sum, written directly on the unit group.
The character supplied here is the manuscript's conjugate character. -/
noncomputable def generalizedBernoulliOne
    {q : ℕ} [NeZero q] (ψ : Character q) : ℂ :=
  (q : ℂ)⁻¹ * ∑ a : UnitClass q, (a.val.val : ℂ) * ψ a.val

/-- The exact fractional-part numerator after multiplication by a unit. -/
noncomputable def fractionalPartTransform
    {q : ℕ} [NeZero q] (ψ : Character q) (u : UnitClass q) : ℂ :=
  (q : ℂ)⁻¹ *
    ∑ a : UnitClass q, ((u * a).val.val : ℂ) * ψ a.val

/-- Multiplication by a unit turns the fractional-part transform into the
corresponding inverse-character value times the Bernoulli sum. -/
theorem fractionalPartTransform_eq
    {q : ℕ} [NeZero q] (ψ : Character q) (u : UnitClass q) :
    fractionalPartTransform ψ u =
      ψ (u⁻¹ : UnitClass q).val * generalizedBernoulliOne ψ := by
  classical
  unfold fractionalPartTransform generalizedBernoulliOne
  have hreindex :
      (∑ a : UnitClass q, ((u * a).val.val : ℂ) * ψ a.val) =
        ∑ x : UnitClass q,
          (x.val.val : ℂ) * ψ ((u⁻¹ : UnitClass q) * x).val := by
    simpa [mul_assoc] using
      (Equiv.sum_comp (Equiv.mulLeft u)
        (fun x : UnitClass q =>
          (x.val.val : ℂ) * ψ ((u⁻¹ : UnitClass q) * x).val))
  rw [hreindex]
  simp_rw [Units.val_mul, map_mul]
  calc
    (q : ℂ)⁻¹ *
        ∑ x : UnitClass q,
          (x.val.val : ℂ) *
            (ψ (u⁻¹ : UnitClass q).val * ψ x.val) =
      (q : ℂ)⁻¹ *
        (ψ (u⁻¹ : UnitClass q).val *
          ∑ x : UnitClass q, (x.val.val : ℂ) * ψ x.val) := by
            congr 1
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x _
            ring
    _ = _ := by ring

/-! ## Diagonal reflection -/

/-- A reflected diagonal half contributes the negative of the other half;
subtracting the second copy gives the exact factor two. -/
theorem diagonal_reduction_from_reflection
    {ι : Type*} [Fintype ι]
    (initial reflected : ι → ℂ) (α : ℂ)
    (hreflect : ∀ i, reflected i = -α * initial i) :
    (∑ i, reflected i) - α * ∑ i, initial i =
      -2 * α * ∑ i, initial i := by
  classical
  simp_rw [hreflect, ← Finset.mul_sum]
  ring

/-- The magnitude form of the same exact diagonal reduction. -/
theorem diagonal_reduction_norm
    (P S α : ℂ) (hS : S = -2 * α * P) (hα : ‖α‖ = 1) :
    ‖S‖ = 2 * ‖P‖ := by
  rw [hS, norm_mul, norm_mul, hα]
  norm_num

/-! ## Exact coefficient and moment algebra -/

/-- The floor contribution and the diagonal contribution cancel their two
base-sized terms and leave the exact Bernoulli-diagonal product. -/
theorem floor_diagonal_cancellation
    (b : ℕ) (B G floorMoment diagonalMoment : ℂ)
    (hfloor : floorMoment = -(b : ℂ) * B)
    (hdiagonal : diagonalMoment = B * ((b : ℂ) - star G)) :
    floorMoment + diagonalMoment = -(B * star G) := by
  rw [hfloor, hdiagonal]
  ring

/-- Dividing the raw collision moment by the unit-group cardinality gives
the manuscript's normalized coefficient factorization. -/
theorem normalized_collision_factorization
    (raw B G φ : ℂ) (hraw : raw = -(B * star G)) :
    φ⁻¹ * raw = -(B * star G) / φ := by
  rw [hraw]
  field_simp

/-- Squared magnitudes of factored coefficients give the exact finite
weighted boundary moment before any analytic interpretation of `B`. -/
theorem factored_coefficient_moment
    {ι : Type*} [Fintype ι]
    (coefficient bernoulli diagonal : ι → ℂ) (φ : ℂ)
    (hfactor : ∀ i,
      coefficient i = -(φ⁻¹ * (bernoulli i * star (diagonal i)))) :
    ∑ i, Complex.normSq (coefficient i) =
      Complex.normSq φ⁻¹ *
        ∑ i, Complex.normSq (bernoulli i) *
          Complex.normSq (diagonal i) := by
  classical
  simp_rw [hfactor, Complex.normSq_neg, Complex.normSq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show Complex.normSq (star (diagonal i)) =
      Complex.normSq (diagonal i) by
    exact Complex.normSq_conj _]

/-- The normalized collision coefficients satisfy the manuscript's exact
Parseval normalization on the complete character group. -/
theorem collisionCoefficient_parseval
    {q : ℕ} [NeZero q] (F : UnitClass q → ℂ) :
    ∑ χ : Character q, ‖collisionCoefficient F χ‖ ^ 2 =
      (q.totient : ℝ)⁻¹ * ∑ r : UnitClass q, ‖F r‖ ^ 2 := by
  classical
  have hcoefficient (χ : Character q) :
      collisionCoefficient F χ =
        (q.totient : ℂ)⁻¹ * characterTransform F (star χ) := by
    unfold collisionCoefficient finiteCoefficient characterTransform
    rw [ZMod.card_units_eq_totient]
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    rw [MulChar.star_apply]
    ring
  have hreindex :
      (∑ χ : Character q, ‖characterTransform F (star χ)‖ ^ 2) =
        ∑ χ : Character q, ‖characterTransform F χ‖ ^ 2 := by
    simpa using (Equiv.sum_comp (Equiv.Perm.star :
      Equiv.Perm (Character q))
      (fun χ : Character q => ‖characterTransform F χ‖ ^ 2))
  have htot : (q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  simp_rw [hcoefficient, norm_mul, norm_inv]
  calc
    (∑ χ : Character q,
        (‖(q.totient : ℂ)‖⁻¹ *
          ‖characterTransform F (star χ)‖) ^ 2) =
      ‖(q.totient : ℂ)‖⁻¹ ^ 2 *
        ∑ χ : Character q,
          ‖characterTransform F (star χ)‖ ^ 2 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro χ _
            ring
    _ = ‖(q.totient : ℂ)‖⁻¹ ^ 2 *
        ∑ χ : Character q, ‖characterTransform F χ‖ ^ 2 := by
          rw [hreindex]
    _ = (q.totient : ℝ)⁻¹ *
        ∑ r : UnitClass q, ‖F r‖ ^ 2 := by
          rw [character_parseval]
          simp only [Complex.norm_natCast]
          field_simp

/-! ## The exact base-five cyclotomic identity -/

/-- The short base-five character polynomial. -/
def baseFiveShortPolynomial (z : ℂ) : ℂ :=
  1 + z + z ^ 2 + z ^ 7

/-- The reduced base-five Bernoulli polynomial. -/
def baseFiveBernoulliPolynomial (z : ℂ) : ℂ :=
  1 + 2 * z + 3 * z ^ 2 + z ^ 3 - 2 * z ^ 4 +
    z ^ 5 + z ^ 6 + 2 * z ^ 7

/-- The twentieth cyclotomic polynomial in the form used by the manuscript. -/
def cyclotomicTwentyValue (z : ℂ) : ℂ :=
  z ^ 8 - z ^ 6 + z ^ 4 - z ^ 2 + 1

/-- The quotient in the manuscript's exact Laurent-polynomial certificate. -/
def baseFiveCertificateQuotient (z : ℂ) : ℂ :=
  -3 + z ^ 2 + 5 * z ^ 3 + z ^ 4 - 3 * z ^ 6

/-- Exact Laurent-polynomial identity underlying the base-five collapse. -/
theorem baseFive_laurent_polynomial_identity (z : ℂ) (hz : z ≠ 0) :
    z ^ 7 *
        (baseFiveBernoulliPolynomial z *
            baseFiveBernoulliPolynomial z⁻¹ -
          5 * baseFiveShortPolynomial z * baseFiveShortPolynomial z⁻¹) =
      cyclotomicTwentyValue z * baseFiveCertificateQuotient z := by
  unfold baseFiveBernoulliPolynomial baseFiveShortPolynomial
    cyclotomicTwentyValue baseFiveCertificateQuotient
  field_simp
  ring

/-- At a nonzero root of the twentieth cyclotomic polynomial, the two
Laurent square products differ by the exact factor five. -/
theorem baseFive_product_identity
    (z : ℂ) (hz : z ≠ 0) (hcyclotomic : cyclotomicTwentyValue z = 0) :
    baseFiveBernoulliPolynomial z * baseFiveBernoulliPolynomial z⁻¹ =
      5 * baseFiveShortPolynomial z * baseFiveShortPolynomial z⁻¹ := by
  have h := baseFive_laurent_polynomial_identity z hz
  rw [hcyclotomic, zero_mul] at h
  exact sub_eq_zero.mp
    ((mul_eq_zero.mp h).resolve_left (pow_ne_zero 7 hz))

/-- Conjugation of the short polynomial is evaluation at the inverse on the
unit circle. -/
theorem star_baseFiveShortPolynomial
    (z : ℂ) (hstar : star z = z⁻¹) :
    star (baseFiveShortPolynomial z) = baseFiveShortPolynomial z⁻¹ := by
  unfold baseFiveShortPolynomial
  simp [hstar]

/-- The same conjugation identity for the reduced Bernoulli polynomial. -/
theorem star_baseFiveBernoulliPolynomial
    (z : ℂ) (hstar : star z = z⁻¹) :
    star (baseFiveBernoulliPolynomial z) =
      baseFiveBernoulliPolynomial z⁻¹ := by
  unfold baseFiveBernoulliPolynomial
  simp [hstar]

/-- The cyclotomic certificate forces the exact magnitude-square ratio five. -/
theorem baseFive_normSq_identity
    (z : ℂ) (hz : z ≠ 0) (hstar : star z = z⁻¹)
    (hcyclotomic : cyclotomicTwentyValue z = 0) :
    Complex.normSq (baseFiveBernoulliPolynomial z) =
      5 * Complex.normSq (baseFiveShortPolynomial z) := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [Complex.normSq_eq_conj_mul_self]
  change star (baseFiveBernoulliPolynomial z) *
      baseFiveBernoulliPolynomial z =
    5 * (star (baseFiveShortPolynomial z) *
      baseFiveShortPolynomial z)
  rw [star_baseFiveBernoulliPolynomial z hstar,
    star_baseFiveShortPolynomial z hstar]
  have hproduct := baseFive_product_identity z hz hcyclotomic
  calc
    baseFiveBernoulliPolynomial z⁻¹ *
        baseFiveBernoulliPolynomial z =
      baseFiveBernoulliPolynomial z *
        baseFiveBernoulliPolynomial z⁻¹ := by ring
    _ = 5 * baseFiveShortPolynomial z *
        baseFiveShortPolynomial z⁻¹ := hproduct
    _ = 5 * (baseFiveShortPolynomial z⁻¹ *
        baseFiveShortPolynomial z) := by ring

/-- With the manuscript's exact Bernoulli scaling, the squared magnitude of
the generalized Bernoulli value is four fifths of the short-sum square. -/
theorem baseFive_scaled_bernoulli_normSq
    (z : ℂ) (hz : z ≠ 0) (hstar : star z = z⁻¹)
    (hcyclotomic : cyclotomicTwentyValue z = 0) :
    Complex.normSq (-(2 / 5 : ℂ) * baseFiveBernoulliPolynomial z) =
      (4 / 5 : ℝ) * Complex.normSq (baseFiveShortPolynomial z) := by
  rw [Complex.normSq_mul, Complex.normSq_neg,
    baseFive_normSq_identity z hz hstar hcyclotomic]
  norm_num [Complex.normSq_div, Complex.normSq_ofNat]
  ring

/-- Combining the diagonal factor two with the Bernoulli scaling gives the
paper's exact base-five relation `|S_G|^2 = 5 |B_1|^2`. -/
theorem baseFive_diagonal_bernoulli_normSq
    (z α : ℂ) (hz : z ≠ 0) (hstar : star z = z⁻¹)
    (hcyclotomic : cyclotomicTwentyValue z = 0)
    (hα : Complex.normSq α = 1) :
    Complex.normSq (-2 * α * baseFiveShortPolynomial z) =
      5 * Complex.normSq
        (-(2 / 5 : ℂ) * baseFiveBernoulliPolynomial z) := by
  rw [Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_neg,
    hα, baseFive_scaled_bernoulli_normSq z hz hstar hcyclotomic]
  norm_num [Complex.normSq_ofNat]
  ring

/-! ## Exact executable energy -/

/-- Centered collision energy in the manuscript's exact rational table. -/
def rationalCollisionEnergy (b : ℕ) : ℚ :=
  ∑ a ∈ reducedResidues (b ^ 2), (rationalCenteredTable b 1 a) ^ 2

/-- Direct exact evaluation of the complete centered base-five table. -/
theorem baseFive_rational_collision_energy :
    rationalCollisionEnergy 5 = 48 := by
  decide +kernel

/-- The complete executable base-five ledger also checks all twenty unit
classes and the zero total on every coarse fiber. -/
theorem baseFive_complete_table_certificate :
    (reducedResidues 25).card = 20 ∧
      rationalCollisionEnergy 5 = 48 ∧
      ∀ u ∈ reducedResidues 5, exactCenteredFiberTotal 5 1 u = 0 := by
  decide +kernel

end NField.Alignment.CollisionSpectrumLandscape

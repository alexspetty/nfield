/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimeSquareMagnitudeBernoulliMoment

/-!
# The literal diagonal sum and its magnitude

This assembles the manuscript's oriented, conjugated sum over the actual
digit diagonal. The existing paired boundary and short window give the
phase-sensitive reduction and its exact magnitude, without assuming a
reflection identity for unspecified signals.
-/

set_option autoImplicit false

namespace NField.Alignment.PrimeSquareMagnitudeFamily

open scoped BigOperators ComplexConjugate ZMod
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionFluctuationSum
open NField.Alignment.PrimeSquareBoundaryFlux
open NField.Alignment.PrimeCarrySpectralBridge
open NField.Alignment.SpectralRepulsion

noncomputable def diagonalSum (b : ℕ) (χ : PrimitiveOddFamily b) : ℂ :=
  ∑ n ∈ diagonalSlices b,
    (star (χ.val ((n : ZMod (b^2))+1)) - star (χ.val (n : ZMod (b^2))))

theorem diagonalSum_eq_conj_flux {b : ℕ} [NeZero (b^2)]
    (hb : b.Prime) (χ : PrimitiveOddFamily b) :
    diagonalSum b χ = star (lagOneBoundaryFlux hb χ.val) := by
  rw [← cellBoundaryFlux_primeDiagonalWeight_eq_lagOne hb,
    cellBoundaryFlux_primeDiagonalWeight]
  unfold diagonalSum diagonalSlices
  rw [Finset.sum_image]
  · simp only [star_sum, star_sub]
    apply Finset.sum_congr rfl
    intro n _
    push_cast
    rfl
  · intro i _ j _ hij
    exact Nat.mul_left_cancel (Nat.succ_pos b) hij

theorem diagonalSum_eq_short_sum {b : ℕ} [NeZero (b^2)]
    (hb : b.Prime) (χ : PrimitiveOddFamily b) :
    diagonalSum b χ = -2 * star (χ.val ((b+1 : ℕ) : ZMod (b^2))) * shortSum b χ := by
  rw [diagonalSum_eq_conj_flux hb,
    lagOneBoundaryFlux_eq_shortWindow hb χ.val χ.property.2]
  simp only [star_mul, star_neg, star_ofNat]
  rw [← shortSum_eq_conj_window hb χ]
  simp only [lagOneStepUnit, ZMod.coe_unitOfCoprime]
  ring

theorem diagonalSum_norm {b : ℕ} [NeZero (b^2)]
    (hb : b.Prime) (χ : PrimitiveOddFamily b) :
    ‖diagonalSum b χ‖ = 2 * ‖shortSum b χ‖ := by
  have hs : ‖diagonalSum b χ‖^2 = 4 * ‖shortSum b χ‖^2 := by
    rw [diagonalSum_eq_conj_flux hb, norm_star, Complex.sq_norm,
      lagOneBoundaryFlux_normSq hb χ.val χ.property.2,
      shortSum_eq_conj_window hb, norm_star, Complex.sq_norm]
  nlinarith [norm_nonneg (diagonalSum b χ), norm_nonneg (shortSum b χ)]

theorem shortSum_square_average {b : ℕ} [NeZero b] [NeZero (b^2)]
    (hb : b.Prime) (hbodd : b ≠ 2) :
    uniformAverage (fun χ : PrimitiveOddFamily b => ‖shortSum b χ‖^2) = (b : ℝ) := by
  unfold uniformAverage
  rw [family_population hb hbodd, shortSum_second_moment_total hb, Nat.cast_pow]
  have hb1 : ((b-1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (by have h := hb.one_lt; omega : b-1 ≠ 0)
  field_simp

theorem diagonalSum_square_average {b : ℕ} [NeZero b] [NeZero (b^2)]
    (hb : b.Prime) (hbodd : b ≠ 2) :
    uniformAverage (fun χ : PrimitiveOddFamily b => ‖diagonalSum b χ‖^2) = 4*b := by
  simp_rw [diagonalSum_norm hb, mul_pow]
  norm_num only [show (2 : ℝ)^2 = 4 from by norm_num]
  rw [uniformAverage_mul_left, shortSum_square_average hb hbodd]

theorem baseSeven_proportionality_forces_square {c : ℝ}
    (h : ∀ χ : PrimitiveOddFamily 7, ‖diagonalSum 7 χ‖ = c * ‖bernoulliSum 7 χ‖) :
    c^2 = 7/2 := by
  have havg := diagonalSum_square_average (by decide : Nat.Prime 7) (by decide)
  have hbern := bernoulli_magnitude_second_moment (by decide : Nat.Prime 7) (by decide)
  simp_rw [h, mul_pow] at havg
  rw [uniformAverage_mul_left, hbern] at havg
  norm_num at havg
  linarith

end NField.Alignment.PrimeSquareMagnitudeFamily

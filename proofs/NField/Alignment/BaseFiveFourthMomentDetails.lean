/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.BaseFiveSpecialValue
import NField.Alignment.BaseFiveCharacterRoots

/-! # Literal fourth-power ledgers for the base-five objects -/

noncomputable section
namespace NField.Alignment.BaseFiveFourthMomentDetails
open scoped BigOperators
open CollisionCharacterStructure CollisionTransformStrip CollisionSpectrumLandscape
  LandscapeActualSpectrum LandscapeSpecialValueMoment BaseFiveSpecialValue
  BaseFiveCollisionEnergy BaseFiveCharacterRoots SpectralCharacterPairs
  PrimeCarryEnergyBridge PrimeCarryFiberCentering

theorem actual_short_bernoulli_norm (χ : Character 25)
    (hprim : χ.IsPrimitive) (hodd : χ.Odd) :
    ‖initialCharacterSum 5 χ‖ = Real.sqrt 5 / 2 * ‖generalizedBernoulliOne χ⁻¹‖ := by
  have h := actual_diagonal_bernoulli_norm χ hprim hodd
  rw [diagonalBoundary_norm (by decide : Nat.Prime 5) χ hodd] at h
  linarith

theorem actual_coefficient_diagonal_fourth (χ : Character 25)
    (hprim : χ.IsPrimitive) (hodd : χ.Odd) :
    ‖collisionCoefficient (primeCarryCentered (by decide : Nat.Prime 5)) χ‖ ^ 2 =
      ‖diagonalBoundary 5 χ‖ ^ 4 / 2000 := by
  rw [actual_collision_coefficient (by decide : Nat.Prime 5) χ hprim,
    norm_div, norm_neg, norm_mul, norm_star, Complex.norm_natCast]
  norm_num [show Nat.totient 25 = 20 by decide]
  have h := actual_diagonal_bernoulli_norm_sq χ hprim hodd
  linear_combination -(‖diagonalBoundary 5 χ‖ ^ 2 / 2000) * h

theorem actual_diagonal_fourth_moment :
    (∑ χ : PrimitiveOddFamily 5, ‖diagonalBoundary 5 χ.val‖ ^ 4) = 4800 := by
  have h := actual_primitive_parseval (by decide : Nat.Prime 5) (by decide : 5 ≠ 2)
  rw [base_five_actual_collision_energy] at h
  have he : (∑ χ : PrimitiveOddFamily 5,
      ‖collisionCoefficient (primeCarryCentered (by decide : Nat.Prime 5)) χ.val‖ ^ 2) =
      (∑ χ : PrimitiveOddFamily 5, ‖diagonalBoundary 5 χ.val‖ ^ 4) / 2000 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro χ _
    exact actual_coefficient_diagonal_fourth χ.val χ.property.1 χ.property.2
  rw [he] at h
  norm_num [show Nat.totient 25 = 20 by decide] at h
  linarith

theorem actual_initial_fourth_moment :
    (∑ χ : PrimitiveOddFamily 5, ‖initialCharacterSum 5 χ.val‖ ^ 4) = 300 := by
  have h := actual_diagonal_fourth_moment
  have he : (∑ χ : PrimitiveOddFamily 5, ‖diagonalBoundary 5 χ.val‖ ^ 4) =
      16 * ∑ χ : PrimitiveOddFamily 5, ‖initialCharacterSum 5 χ.val‖ ^ 4 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro χ _
    rw [diagonalBoundary_norm (by decide : Nat.Prime 5) χ.val χ.property.2]
    ring
  rw [he] at h
  linarith

theorem actual_initial_norm_polynomial (χ : Character 25) :
    ‖initialCharacterSum 5 χ‖ = ‖baseFiveShortPolynomial (χ 2)‖ := by
  have h : initialCharacterSum 5 χ = star (baseFiveShortPolynomial (χ 2)) := by
    rw [initial_sum_polynomial]
    unfold baseFiveShortPolynomial
    simp [MulChar.star_apply']
  rw [h, norm_star]

theorem primitive_root_fourth_moment :
    (∑ j : PrimitiveExponent, ‖baseFiveShortPolynomial (zeta ^ j.val.val)‖ ^ 4) = 300 := by
  rw [← Equiv.sum_comp characterExponentEquiv
    (fun j : PrimitiveExponent => ‖baseFiveShortPolynomial (zeta ^ j.val.val)‖ ^ 4)]
  change (∑ χ : PrimitiveOddFamily 5,
    ‖baseFiveShortPolynomial (zeta ^ (characterExponent χ).val.val)‖ ^ 4) = 300
  calc
    _ = ∑ χ : PrimitiveOddFamily 5, ‖initialCharacterSum 5 χ.val‖ ^ 4 := by
      apply Finset.sum_congr rfl
      intro χ _
      rw [characterExponent_spec]
      exact congrArg (fun x : ℝ => x ^ 4) (actual_initial_norm_polynomial χ.val).symm
    _ = 300 := actual_initial_fourth_moment

end NField.Alignment.BaseFiveFourthMomentDetails

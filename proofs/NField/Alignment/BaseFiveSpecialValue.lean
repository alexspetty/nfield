/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.BaseFiveCharacterPolynomial
import NField.Alignment.BaseFiveCollisionEnergy
import NField.Alignment.LandscapeSpecialValueMoment

/-! # The exact base-five fourth moment for actual Dirichlet characters -/

noncomputable section
namespace NField.Alignment.BaseFiveSpecialValue
open scoped BigOperators
open CollisionCharacterStructure CollisionTransformStrip CollisionSpectrumLandscape CarryBoundarySpectra
  LandscapeActualSpectrum BaseFiveCharacterPolynomial BaseFiveCollisionEnergy
  LandscapeSpecialValueMoment SpectralCharacterPairs PrimeCarryEnergyBridge
  PrimeCarryFiberCentering

theorem initial_sum_polynomial (χ : Character 25) :
    initialCharacterSum 5 χ = baseFiveShortPolynomial (χ⁻¹ 2) := by
  unfold initialCharacterSum
  simp only [MulChar.star_apply']
  exact short_character_polynomial χ⁻¹

theorem actual_short_bernoulli_norm_sq (χ : Character 25)
    (hprim : χ.IsPrimitive) (hodd : χ.Odd) :
    ‖generalizedBernoulliOne χ⁻¹‖ ^ 2 =
      (4 / 5 : ℝ) * ‖initialCharacterSum 5 χ‖ ^ 2 := by
  have hi : (χ⁻¹).Odd := by
    change χ⁻¹ (-1) = -1
    rw [MulChar.inv_apply_eq_inv', hodd]
    norm_num
  have hz : χ⁻¹ (2 : ZMod 25) ≠ 0 := by
    intro hz
    have h := odd_character_two_tenth χ⁻¹ hi
    rw [hz] at h
    norm_num at h
  have hstar : star (χ⁻¹ (2 : ZMod 25)) = (χ⁻¹ (2 : ZMod 25))⁻¹ := by
    rw [MulChar.star_apply', MulChar.inv_apply_eq_inv']
  have h := baseFive_scaled_bernoulli_normSq (χ⁻¹ 2) hz hstar
    (primitive_odd_cyclotomic_twenty χ⁻¹ (inverse_isPrimitive hprim) hi)
  rw [← bernoulli_character_polynomial χ⁻¹ (inverse_isPrimitive hprim) hi,
    ← generalizedBernoulliOne_eq_full, ← initial_sum_polynomial χ,
    Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h
  exact h

theorem actual_diagonal_bernoulli_norm_sq (χ : Character 25)
    (hprim : χ.IsPrimitive) (hodd : χ.Odd) :
    ‖diagonalBoundary 5 χ‖ ^ 2 = 5 * ‖generalizedBernoulliOne χ⁻¹‖ ^ 2 := by
  rw [diagonalBoundary_norm (by decide : Nat.Prime 5) χ hodd]
  have h := actual_short_bernoulli_norm_sq χ hprim hodd
  nlinarith [h]

theorem actual_diagonal_bernoulli_norm (χ : Character 25)
    (hprim : χ.IsPrimitive) (hodd : χ.Odd) :
    ‖diagonalBoundary 5 χ‖ = Real.sqrt 5 * ‖generalizedBernoulliOne χ⁻¹‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
  exact actual_diagonal_bernoulli_norm_sq χ hprim hodd

theorem actual_coefficient_l_value (χ : Character 25)
    (hprim : χ.IsPrimitive) (hodd : χ.Odd) :
    ‖collisionCoefficient (primeCarryCentered (by decide : Nat.Prime 5)) χ‖ =
      5 * Real.sqrt 5 / (4 * Real.pi ^ 2) * ‖DirichletCharacter.LFunction χ 1‖ ^ 2 := by
  rw [actual_coefficient_l_value_norm (by decide : Nat.Prime 5) χ hprim hodd,
    actual_diagonal_bernoulli_norm χ hprim hodd,
    bernoulli_l_value_norm (by decide : Nat.Prime 5) χ hprim hodd]
  norm_num [show Nat.totient 25 = 20 by decide]
  ring

theorem actual_l_value_fourth_moment :
    (∑ χ : PrimitiveOddFamily 5, ‖DirichletCharacter.LFunction χ.val 1‖ ^ 4) =
      192 * Real.pi ^ 4 / 625 := by
  have hs := actual_primitive_parseval (by decide : Nat.Prime 5) (by decide : 5 ≠ 2)
  rw [base_five_actual_collision_energy] at hs
  have hc : (∑ χ : PrimitiveOddFamily 5,
      ‖collisionCoefficient (primeCarryCentered (by decide : Nat.Prime 5)) χ.val‖ ^ 2) =
      (125 / (16 * Real.pi ^ 4)) *
        ∑ χ : PrimitiveOddFamily 5, ‖DirichletCharacter.LFunction χ.val 1‖ ^ 4 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro χ _
    rw [actual_coefficient_l_value χ.val χ.property.1 χ.property.2]
    ring_nf
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
    ring
  rw [hc] at hs
  norm_num [show Nat.totient 25 = 20 by decide] at hs
  field_simp [Real.pi_ne_zero] at hs
  nlinarith [hs]

end NField.Alignment.BaseFiveSpecialValue

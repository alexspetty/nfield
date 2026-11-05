/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.LandscapeActualSpectrum
import NField.Alignment.SpectralCharacterPairs

/-! # Exact special-value moment of the actual collision energy -/

noncomputable section
namespace NField.Alignment.LandscapeSpecialValueMoment
open scoped BigOperators
open CollisionCharacterStructure CollisionTransformStrip CenteredCollisionSum
  CollisionSpectrumLandscape TheCollisionSpectrum PrimeCarryEnergyBridge
  PrimeCarryFiberCentering LandscapeActualSpectrum SpectralCharacterPairs

theorem actual_inactive_coefficient_zero {b : ℕ} [NeZero b] [NeZero (b ^ 2)]
    (hb : b.Prime) (hbodd : b ≠ 2) (χ : Character (b ^ 2))
    (hχ : ¬ (χ.IsPrimitive ∧ χ.Odd)) :
    collisionCoefficient (primeCarryCentered hb) χ = 0 := by
  letI : NeZero (allLagModulus b 1) :=
    ⟨by simpa only [allLagModulus, Nat.reduceAdd] using NeZero.ne (b ^ 2)⟩
  by_contra hne
  apply hχ
  apply activeLagOneChannel_primitive_and_odd hb
  rw [show centeredLagOneSpectrum b = primeCarryCentered hb by
    funext a
    exact centeredLagOneSpectrum_eq_primeCarryCentered hb hbodd a]
  exact hne

theorem actual_primitive_parseval {b : ℕ} [NeZero b] [NeZero (b ^ 2)]
    (hb : b.Prime) (hbodd : b ≠ 2) :
    (∑ χ : PrimitiveOddFamily b, ‖collisionCoefficient (primeCarryCentered hb) χ.val‖ ^ 2) =
      primeCarryEnergy hb / ((b ^ 2).totient : ℝ) := by
  classical
  have heq : (∑ χ : Character (b ^ 2), ‖collisionCoefficient (primeCarryCentered hb) χ‖ ^ 2) =
      ∑ χ : PrimitiveOddFamily b, ‖collisionCoefficient (primeCarryCentered hb) χ.val‖ ^ 2 := by
    rw [← Finset.sum_subtype (p := fun χ : Character (b ^ 2) => χ.IsPrimitive ∧ χ.Odd)
      (F := primitiveFamilyFintype b)
      (Finset.univ.filter (fun χ : Character (b ^ 2) => χ.IsPrimitive ∧ χ.Odd)) (by simp)
      (fun χ => ‖collisionCoefficient (primeCarryCentered hb) χ‖ ^ 2)]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro χ _ hnot
    rw [actual_inactive_coefficient_zero hb hbodd χ (by simpa using hnot)]
    norm_num
  rw [← heq, collisionCoefficient_parseval]
  change ((b ^ 2).totient : ℝ)⁻¹ * primeCarryEnergy hb = _
  ring

/-- Parseval after substituting the proved, rather than assumed, coefficient
factorization and Bernoulli-to-L-value identity. -/
theorem actual_special_value_moment {b : ℕ} [NeZero b] [NeZero (b ^ 2)]
    (hb : b.Prime) (hbodd : b ≠ 2) :
    (∑ χ : PrimitiveOddFamily b,
      ‖DirichletCharacter.LFunction χ.val 1‖ ^ 2 * ‖diagonalBoundary b χ.val‖ ^ 2) =
      Real.pi ^ 2 * ((b ^ 2).totient : ℝ) / (b : ℝ) ^ 2 * primeCarryEnergy hb := by
  have hb0 : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne_zero
  have hφ : ((b ^ 2).totient : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (pow_pos hb.pos 2)).ne'
  have hs : (∑ χ : PrimitiveOddFamily b,
      ‖collisionCoefficient (primeCarryCentered hb) χ.val‖ ^ 2) =
      ((b : ℝ) / (Real.pi * (b ^ 2).totient)) ^ 2 *
        ∑ χ : PrimitiveOddFamily b,
          ‖DirichletCharacter.LFunction χ.val 1‖ ^ 2 * ‖diagonalBoundary b χ.val‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro χ _
    rw [actual_coefficient_l_value_norm hb χ.val χ.property.1 χ.property.2]
    ring
  rw [actual_primitive_parseval hb hbodd] at hs
  field_simp [Real.pi_ne_zero, hφ] at hs
  field_simp [hb0]
  nlinarith [hs]

end NField.Alignment.LandscapeSpecialValueMoment

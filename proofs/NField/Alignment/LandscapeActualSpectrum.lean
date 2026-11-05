/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimeCarrySpectralBridge
import NField.Alignment.SawtoothLValue
import NField.Alignment.TheCollisionSpectrum

/-! # The Bernoulli product for the literal collision coefficient

The deep carry and primitive-character transforms are reused here. These
correspondences are placed below the paper modules, so earlier titles can
use them without importing the later magnitude-theory paper.
-/

noncomputable section
namespace NField.Alignment.LandscapeActualSpectrum
open scoped BigOperators ComplexConjugate ZMod
open CollisionCharacterStructure CollisionFluctuationSum CollisionSpectrumLandscape
  CollisionTransformStrip CollisionTransform TheCollisionSpectrum
  PrimeCarryEnergyBridge PrimeCarryFiberCentering PrimeCarrySpectralBridge
  PrimeSquareBoundaryFlux PrimeSquareCollisionWindow CarryBoundarySpectra SawtoothLValue

def diagonalBoundary (b : ℕ) (χ : Character (b ^ 2)) : ℂ :=
  ∑ n ∈ diagonalSlices b,
    (star (χ ((n : ZMod (b ^ 2)) + 1)) - star (χ (n : ZMod (b ^ 2))))

def initialCharacterSum (b : ℕ) (χ : Character (b ^ 2)) : ℂ :=
  ∑ k ∈ Finset.Icc 1 (b - 1), star (χ (k : ZMod (b ^ 2)))

theorem initialCharacterSum_eq_conj_window {b : ℕ} (hb : b.Prime)
    (χ : Character (b ^ 2)) :
    initialCharacterSum b χ = star (shortWindowSum hb χ) := by
  classical
  unfold initialCharacterSum shortWindowSum firstWindowUnit
  simp only [ZMod.coe_unitOfCoprime, star_sum]
  change (∑ k ∈ Finset.Icc 1 (b - 1), star (χ (k : ZMod (b ^ 2)))) =
    ∑ i : Fin (b - 1), star (χ ((i.val + 1 : ℕ) : ZMod (b ^ 2)))
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => star (χ ((k + 1 : ℕ) : ZMod (b ^ 2)))) (b - 1)]
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp [Nat.sub_add_cancel hb.one_lt.le, Nat.add_comm]

theorem diagonalBoundary_eq_conj_flux {b : ℕ} [NeZero (b ^ 2)]
    (hb : b.Prime) (χ : Character (b ^ 2)) :
    diagonalBoundary b χ = star (lagOneBoundaryFlux hb χ) := by
  rw [← cellBoundaryFlux_primeDiagonalWeight_eq_lagOne hb,
    cellBoundaryFlux_primeDiagonalWeight]
  unfold diagonalBoundary diagonalSlices
  rw [Finset.sum_image]
  · simp only [star_sum, star_sub]
    apply Finset.sum_congr rfl
    intro n _
    push_cast
    rfl
  · intro i _ j _ hij
    exact Nat.mul_left_cancel (Nat.succ_pos b) hij

/-- The actual diagonal reduction needs oddness, not primitivity. -/
theorem diagonalBoundary_eq_short_sum {b : ℕ} [NeZero (b ^ 2)]
    (hb : b.Prime) (χ : Character (b ^ 2)) (hodd : χ.Odd) :
    diagonalBoundary b χ =
      -2 * star (χ ((b + 1 : ℕ) : ZMod (b ^ 2))) * initialCharacterSum b χ := by
  rw [diagonalBoundary_eq_conj_flux hb, lagOneBoundaryFlux_eq_shortWindow hb χ hodd]
  simp only [star_mul, star_neg, star_ofNat]
  rw [← initialCharacterSum_eq_conj_window hb χ]
  simp only [lagOneStepUnit, ZMod.coe_unitOfCoprime]
  ring

theorem diagonalBoundary_norm {b : ℕ} [NeZero (b ^ 2)]
    (hb : b.Prime) (χ : Character (b ^ 2)) (hodd : χ.Odd) :
    ‖diagonalBoundary b χ‖ = 2 * ‖initialCharacterSum b χ‖ := by
  have hs : ‖diagonalBoundary b χ‖ ^ 2 = 4 * ‖initialCharacterSum b χ‖ ^ 2 := by
    rw [diagonalBoundary_eq_conj_flux hb, norm_star, Complex.sq_norm,
      lagOneBoundaryFlux_normSq hb χ hodd,
      initialCharacterSum_eq_conj_window hb, norm_star, Complex.sq_norm]
  nlinarith [norm_nonneg (diagonalBoundary b χ), norm_nonneg (initialCharacterSum b χ)]

theorem generalizedBernoulliOne_eq_full {q : ℕ} [NeZero q] (χ : Character q) :
    generalizedBernoulliOne χ = bernoulliOne χ := by
  unfold generalizedBernoulliOne bernoulliOne
  rw [sum_character_pairing_eq_units (fun x : ZMod q => (x.val : ℂ)) χ]

/-- Exact sign, conjugation and normalization for the concrete centered table. -/
theorem actual_collision_coefficient {b : ℕ} [NeZero (b ^ 2)]
    (hb : b.Prime) (χ : Character (b ^ 2)) (hprim : χ.IsPrimitive) :
    collisionCoefficient (primeCarryCentered hb) χ =
      -(generalizedBernoulliOne χ⁻¹ * star (diagonalBoundary b χ)) /
        ((b ^ 2).totient : ℂ) := by
  have hc := collisionCoefficient_inv_eq_characterTransform (primeCarryCentered hb) χ⁻¹
  simp only [inv_inv] at hc
  rw [hc, primitive_characterTransform_factorization hb χ⁻¹
    (inverse_isPrimitive hprim), inv_inv,
    diagonalBoundary_eq_conj_flux hb, star_star, generalizedBernoulliOne_eq_full]
  ring

theorem actual_centered_collision_coefficient {b : ℕ}
    [NeZero b] [NeZero (b ^ 2)] [NeZero (CenteredCollisionSum.allLagModulus b 1)]
    (hb : b.Prime) (hbodd : b ≠ 2)
    (χ : Character (b ^ 2)) (hprim : χ.IsPrimitive) :
    collisionCoefficient (centeredLagOneSpectrum b) χ =
      -(generalizedBernoulliOne χ⁻¹ * star (diagonalBoundary b χ)) /
        ((b ^ 2).totient : ℂ) := by
  have heq : centeredLagOneSpectrum b = primeCarryCentered hb := by
    funext a
    exact centeredLagOneSpectrum_eq_primeCarryCentered hb hbodd a
  rw [heq]
  exact actual_collision_coefficient hb χ hprim

theorem bernoulli_l_value_norm {b : ℕ} [NeZero (b ^ 2)]
    (hb : b.Prime) (χ : Character (b ^ 2)) (hprim : χ.IsPrimitive) (hodd : χ.Odd) :
    ‖generalizedBernoulliOne χ⁻¹‖ =
      (b : ℝ) / Real.pi * ‖DirichletCharacter.LFunction χ 1‖ := by
  have hoddInv : (χ⁻¹).Odd := by
    change χ⁻¹ (-1) = -1
    rw [MulChar.inv_apply_eq_inv', hodd]
    norm_num
  have h := bernoulliOne_normSq_eq_LFunction (N := b ^ 2)
    (by nlinarith [hb.two_le]) (inverse_isPrimitive hprim) hoddInv
  rw [← generalizedBernoulliOne_eq_full] at h
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  simpa only [inv_inv, Complex.normSq_eq_norm_sq, Nat.cast_pow, mul_pow, div_pow] using h

theorem actual_coefficient_l_value_norm {b : ℕ} [NeZero (b ^ 2)]
    (hb : b.Prime) (χ : Character (b ^ 2)) (hprim : χ.IsPrimitive) (hodd : χ.Odd) :
    ‖collisionCoefficient (primeCarryCentered hb) χ‖ =
      (b : ℝ) / (Real.pi * (b ^ 2).totient) *
        ‖DirichletCharacter.LFunction χ 1‖ * ‖diagonalBoundary b χ‖ := by
  rw [actual_collision_coefficient hb χ hprim, norm_div, norm_neg, norm_mul,
    norm_star, Complex.norm_natCast, bernoulli_l_value_norm hb χ hprim hodd]
  ring

end NField.Alignment.LandscapeActualSpectrum

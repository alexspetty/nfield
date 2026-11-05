/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimitiveNaturalFloorTransform
import NField.Alignment.LandscapeActualSpectrum
import NField.Alignment.PrimitiveReductionFiber

/-! # The separate floor and diagonal moments in the source derivation -/

noncomputable section
namespace NField.Alignment.LandscapeSourceMoments
open scoped BigOperators
open CollisionCharacterStructure CollisionFluctuationSum CarryBoundarySpectra
  PrimitiveNaturalFloorTransform LandscapeActualSpectrum PrimitiveReductionFiber
  PrimeCarryEnergyBridge PrimeCarryFiberCentering CenteredCollisionSum
  CollisionTransformStrip

theorem prime_base_character_zero {b : ℕ} [NeZero (b ^ 2)]
    (hb : b.Prime) (χ : Character (b ^ 2)) : χ (b : ZMod (b ^ 2)) = 0 := by
  apply MulChar.map_nonunit
  rw [ZMod.isUnit_iff_coprime]
  rw [Nat.coprime_pow_right_iff (by decide : 0 < 2), Nat.coprime_self]
  exact hb.ne_one

theorem primitive_base_floor_moment {b : ℕ} [NeZero (b ^ 2)]
    (hb : b.Prime) (χ : Character (b ^ 2)) (hprim : χ.IsPrimitive) :
    (∑ a : UnitClass (b ^ 2), ((a.val.val / b : ℕ) : ℂ) * χ⁻¹ a.val) =
      (b : ℂ) * CollisionSpectrumLandscape.generalizedBernoulliOne χ⁻¹ := by
  have h := primitive_natural_floor_transform χ hprim b
  have hdiv (a : UnitClass (b ^ 2)) : b * a.val.val / b ^ 2 = a.val.val / b := by
    simpa only [pow_two] using Nat.mul_div_mul_left a.val.val b hb.pos
  simp_rw [hdiv] at h
  rw [prime_base_character_zero hb χ, sub_zero,
    ← generalizedBernoulliOne_eq_full] at h
  exact h

theorem primitive_diagonal_floor_moment {b : ℕ} [NeZero (b ^ 2)]
    (χ : Character (b ^ 2)) (hprim : χ.IsPrimitive) :
    (∑ a : UnitClass (b ^ 2),
      (∑ n ∈ diagonalSlices b, (floorJump (b ^ 2) a.val.val n : ℂ)) * χ⁻¹ a.val) =
      CollisionSpectrumLandscape.generalizedBernoulliOne χ⁻¹ *
        ((b : ℂ) - star (diagonalBoundary b χ)) := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [primitive_floor_jump_transform χ hprim]
  rw [← Finset.sum_mul, ← generalizedBernoulliOne_eq_full]
  simp only [diagonalBoundary, star_sum, star_sub, star_star]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, diagonalSlices_card]
  ring

theorem primitive_centering_removal {b : ℕ} [NeZero b] [NeZero (b ^ 2)]
    (hb : b.Prime) (χ : Character (b ^ 2)) (hprim : χ.IsPrimitive) :
    (∑ a : UnitClass (b ^ 2), primeCarryCentered hb a * χ⁻¹ a.val) =
      ∑ a : UnitClass (b ^ 2), (fluctuationTable b a.val.val : ℂ) * χ⁻¹ a.val := by
  have hd : b ∣ b ^ 2 := dvd_pow_self b (by decide : 2 ≠ 0)
  have hlt : b < b ^ 2 := by nlinarith [hb.two_le]
  have h := primitive_reduction_weight_sum_zero hd hlt χ⁻¹
    (inverse_isPrimitive hprim) (fun u => ((b - u.val.val : ℕ) : ℂ) / b)
  have hval (a : UnitClass (b ^ 2)) : (ZMod.unitsMap hd a).val.val = a.val.val % b := by
    rw [ZMod.unitsMap_val, ZMod.cast_eq_val, ZMod.val_natCast]
  simp_rw [hval] at h
  unfold primeCarryCentered
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib, h, add_zero]

theorem primitive_raw_coefficient_sum {b : ℕ} [NeZero b] [NeZero (b ^ 2)]
    (hb : b.Prime) (χ : Character (b ^ 2)) (hprim : χ.IsPrimitive) :
    ((b ^ 2).totient : ℂ) * collisionCoefficient (primeCarryCentered hb) χ =
      ∑ a : UnitClass (b ^ 2), (fluctuationTable b a.val.val : ℂ) * χ⁻¹ a.val := by
  have hφ : ((b ^ 2).totient : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (pow_pos hb.pos 2)).ne'
  unfold collisionCoefficient finiteCoefficient
  rw [ZMod.card_units_eq_totient, ← mul_assoc, mul_inv_cancel₀ hφ, one_mul]
  simp only [MulChar.star_apply']
  exact primitive_centering_removal hb χ hprim

theorem actual_coefficient_short_l_norm {b : ℕ} [NeZero (b ^ 2)]
    (hb : b.Prime) (χ : Character (b ^ 2)) (hprim : χ.IsPrimitive) (hodd : χ.Odd) :
    ‖collisionCoefficient (primeCarryCentered hb) χ‖ =
      (2 * (b : ℝ)) / (Real.pi * (b ^ 2).totient) *
        ‖DirichletCharacter.LFunction χ 1‖ * ‖initialCharacterSum b χ‖ := by
  rw [actual_coefficient_l_value_norm hb χ hprim hodd,
    diagonalBoundary_norm hb χ hodd]
  ring

end NField.Alignment.LandscapeSourceMoments

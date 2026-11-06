/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimeSquareShortMoment
import NField.Alignment.LandscapeSourceMoments
import NField.Alignment.LandscapeSpecialValueMoment
import NField.Alignment.BaseFiveFourthMomentDetails

/-! # Phase and diagonal moments of the literal collision spectrum

All sums below use the manuscript's actual prime-square characters and digit
diagonal. The Bernoulli identity is the proved boundary value of Mathlib's
Dirichlet L-function. The short-window orthogonality proof is shared with the
later magnitude paper below both reader-facing modules.
-/

noncomputable section
namespace NField.Alignment.CollisionSpectrumSource
open scoped BigOperators ComplexConjugate ZMod
open CollisionCharacterStructure CollisionSpectrumLandscape CollisionTransformStrip
  LandscapeActualSpectrum LandscapeSpecialValueMoment SpectralCharacterPairs
  PrimeSquareCollisionWindow PrimeSquareBoundaryFlux PrimeSquareShortMoment
  PrimeCarrySpectralBridge PrimeCarryEnergyBridge PrimeCarryFiberCentering
  CarryBoundarySpectra SawtoothLValue PrimitiveOddBoundaryMean

/-- The upper endpoint sum printed as `A(χ)` in the manuscript. -/
def upperDiagonalSum (b : ℕ) (χ : Character (b ^ 2)) : ℂ :=
  ∑ r ∈ Finset.range (b - 1), star (χ (((b + 1) * r + 1 : ℕ) : ZMod (b ^ 2)))

/-- Title: `Upper diagonal sum from the actual endpoints`. -/
theorem upperDiagonalSum_eq_short_sum {b : ℕ} [NeZero (b ^ 2)]
    (hb : b.Prime) (χ : Character (b ^ 2)) (hodd : χ.Odd) :
    upperDiagonalSum b χ =
      -star (χ ((b + 1 : ℕ) : ZMod (b ^ 2))) * initialCharacterSum b χ := by
  have hright : (∑ i : FirstWindowIndex b, χ (lagOneBoundaryRight hb i).val) =
      -(∑ i : FirstWindowIndex b, χ (lagOneBoundaryLeft hb i).val) := by
    simp only [lagOneBoundaryRight, Units.val_neg, hodd.eval_neg, Finset.sum_neg_distrib]
    congr 1
    exact Equiv.sum_comp (Fin.revPerm : Equiv.Perm (FirstWindowIndex b))
      (fun i : FirstWindowIndex b => χ (lagOneBoundaryLeft hb i).val)
  have hupper : upperDiagonalSum b χ =
      star (∑ i : FirstWindowIndex b, χ (lagOneBoundaryRight hb i).val) := by
    simp only [upperDiagonalSum, star_sum, lagOneBoundaryRight_eq_diagonalSuccessor hb]
    exact (Fin.sum_univ_eq_sum_range
      (fun r : ℕ => star (χ (((b + 1) * r + 1 : ℕ) : ZMod (b ^ 2)))) (b - 1)).symm
  rw [hupper, hright, leftEndpointSum_factor hb χ]
  simp only [star_neg, star_mul, ← initialCharacterSum_eq_conj_window hb χ,
    lagOneStepUnit, ZMod.coe_unitOfCoprime]
  ring

/-- Title: `Diagonal sum is twice the upper endpoint sum`. -/
theorem diagonalBoundary_eq_twice_upper {b : ℕ} [NeZero (b ^ 2)]
    (hb : b.Prime) (χ : Character (b ^ 2)) (hodd : χ.Odd) :
    diagonalBoundary b χ = 2 * upperDiagonalSum b χ := by
  rw [diagonalBoundary_eq_short_sum hb χ hodd, upperDiagonalSum_eq_short_sum hb χ hodd]
  ring

/-- The root number in the manuscript's positive exponential convention. -/
def collisionRootNumber (b : ℕ) [NeZero (b ^ 2)] (χ : Character (b ^ 2)) : ℂ :=
  gaussSum χ⁻¹ ZMod.stdAddChar / (Complex.I * b)

/-- Title: `Root number has unit magnitude`. -/
theorem collisionRootNumber_norm {b : ℕ} [NeZero (b ^ 2)]
    (hb : b.Prime) (χ : Character (b ^ 2)) (hprim : χ.IsPrimitive) (hodd : χ.Odd) :
    ‖collisionRootNumber b χ‖ = 1 := by
  have hi : (χ⁻¹).Odd := by
    change χ⁻¹ (-1) = -1
    rw [MulChar.inv_apply_eq_inv', hodd]
    norm_num
  have h := primitiveOdd_gaussSum_normSq (N := b ^ 2)
    (by nlinarith [hb.two_le]) (inverse_isPrimitive hprim) hi
  have ht : ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ = (b : ℝ) := by
    apply (sq_eq_sq₀ (norm_nonneg _) (Nat.cast_nonneg _)).mp
    simpa only [Complex.normSq_eq_norm_sq, Nat.cast_pow] using h
  rw [collisionRootNumber, norm_div, norm_mul, Complex.norm_I, Complex.norm_natCast,
    one_mul, ht, div_self (Nat.cast_ne_zero.mpr hb.ne_zero)]

/-- Title: `Bernoulli value with the exact root number phase`. -/
theorem bernoulli_rootNumber_l_value {b : ℕ} [NeZero (b ^ 2)]
    (hb : b.Prime) (χ : Character (b ^ 2)) (hprim : χ.IsPrimitive) (hodd : χ.Odd) :
    generalizedBernoulliOne χ⁻¹ =
      -((b : ℂ) / Real.pi) * collisionRootNumber b χ *
        DirichletCharacter.LFunction χ 1 := by
  have hi : (χ⁻¹).Odd := by
    change χ⁻¹ (-1) = -1
    rw [MulChar.inv_apply_eq_inv', hodd]
    norm_num
  have h := primitiveOdd_LFunction_bernoulliOne (N := b ^ 2)
    (by nlinarith [hb.two_le]) (inverse_isPrimitive hprim) hi
  simp only [inv_inv] at h
  rw [generalizedBernoulliOne_eq_full]
  unfold collisionRootNumber
  have hb0 : (b : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne_zero
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hb0, hpi, Complex.I_ne_zero]
  linear_combination -h

/-- Title: `Phase separated coefficient of the actual collision table`. -/
theorem actual_phase_separated_coefficient {b : ℕ} [NeZero (b ^ 2)]
    (hb : b.Prime) (χ : Character (b ^ 2)) (hprim : χ.IsPrimitive) (hodd : χ.Odd) :
    collisionCoefficient (primeCarryCentered hb) χ =
      (2 / ((Real.pi : ℂ) * (b - 1 : ℕ))) * collisionRootNumber b χ *
        DirichletCharacter.LFunction χ 1 * star (upperDiagonalSum b χ) := by
  rw [actual_collision_coefficient hb χ hprim,
    bernoulli_rootNumber_l_value hb χ hprim hodd,
    diagonalBoundary_eq_twice_upper hb χ hodd]
  rw [Nat.totient_prime_pow hb (by decide : 0 < 2)]
  simp only [Nat.reduceSub, pow_one, Nat.cast_mul, star_mul, star_ofNat]
  have hb0 : (b : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne_zero
  have hb1 : ((b - 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := hb.one_lt; omega)
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hb0, hb1, hpi]

/-- Title: `Exact diagonal second moment`. -/
theorem actual_diagonal_second_moment {b : ℕ} [NeZero b] [NeZero (b ^ 2)]
    (hb : b.Prime) :
    (∑ χ : PrimitiveOddFamily b, ‖diagonalBoundary b χ.val‖ ^ 2) =
      2 * (b : ℝ) * ((b - 1 : ℕ) : ℝ) ^ 2 := by
  classical
  have h := primitive_odd_shortWindow_second_moment hb
  rw [Finset.sum_subtype (p := fun χ : Character (b ^ 2) => χ.IsPrimitive ∧ χ.Odd)
    (F := primitiveFamilyFintype b) _ (by simp) (fun χ =>
    (Complex.normSq (shortWindowSum hb χ) : ℂ))] at h
  have hr : (∑ χ : PrimitiveOddFamily b, Complex.normSq (shortWindowSum hb χ.val)) =
      (1 / 2 : ℝ) * ((b ^ 2).totient : ℝ) * (b - 1 : ℕ) := by
    apply Complex.ofReal_injective
    push_cast
    exact h
  have hd (χ : PrimitiveOddFamily b) :
      ‖diagonalBoundary b χ.val‖ ^ 2 = 4 * Complex.normSq (shortWindowSum hb χ.val) := by
    rw [diagonalBoundary_eq_conj_flux hb, norm_star, Complex.sq_norm,
      lagOneBoundaryFlux_normSq hb χ.val χ.property.2]
  simp_rw [hd]
  rw [← Finset.mul_sum, hr, Nat.totient_prime_pow hb (by decide : 0 < 2)]
  norm_num
  ring

/-- Title: `Diagonal squares have mean four times the base`. -/
theorem actual_diagonal_mean {b : ℕ} [NeZero b] [NeZero (b ^ 2)]
    (hb : b.Prime) (hbodd : b ≠ 2) :
    (∑ χ : PrimitiveOddFamily b, ‖diagonalBoundary b χ.val‖ ^ 2) /
      (Fintype.card (PrimitiveOddFamily b) : ℝ) = 4 * b := by
  rw [actual_diagonal_second_moment hb, primitive_population hb hbodd, Nat.cast_pow]
  have hb1 : ((b - 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := hb.one_lt; omega)
  field_simp
  ring

/-- The probability weights are the actual diagonal squares. -/
def collisionProbabilityWeight (b : ℕ) (χ : PrimitiveOddFamily b) : ℝ :=
  ‖diagonalBoundary b χ.val‖ ^ 2 / (2 * b * ((b - 1 : ℕ) : ℝ) ^ 2)

/-- Title: `Collision weights sum to one`. -/
theorem actual_collision_weights_sum {b : ℕ} [NeZero b] [NeZero (b ^ 2)]
    (hb : b.Prime) : (∑ χ : PrimitiveOddFamily b, collisionProbabilityWeight b χ) = 1 := by
  unfold collisionProbabilityWeight
  rw [← Finset.sum_div, actual_diagonal_second_moment hb]
  apply div_self
  have hb0 : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne_zero
  have hb1 : ((b - 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := hb.one_lt; omega)
  exact mul_ne_zero (mul_ne_zero (by norm_num) hb0) (pow_ne_zero _ hb1)

/-- Title: `Exact expectation under collision weights`. -/
theorem actual_collision_weighted_l_value_mean {b : ℕ} [NeZero b] [NeZero (b ^ 2)]
    (hb : b.Prime) (hbodd : b ≠ 2) :
    (∑ χ : PrimitiveOddFamily b,
      collisionProbabilityWeight b χ * ‖DirichletCharacter.LFunction χ.val 1‖ ^ 2) =
      Real.pi ^ 2 * primeCarryEnergy hb / (2 * (b : ℝ) ^ 2 * (b - 1 : ℕ)) := by
  unfold collisionProbabilityWeight
  simp_rw [div_mul_eq_mul_div, mul_comm (‖diagonalBoundary b _‖ ^ 2)]
  rw [← Finset.sum_div, actual_special_value_moment hb hbodd,
    Nat.totient_prime_pow hb (by decide : 0 < 2)]
  simp only [Nat.reduceSub, pow_one, Nat.cast_mul]
  have hb0 : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne_zero
  have hb1 : ((b - 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := hb.one_lt; omega)
  field_simp

end NField.Alignment.CollisionSpectrumSource

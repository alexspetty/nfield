/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.MagnitudeDiagonalReduction
import NField.Alignment.OddBernoulliPrimeSquare

/-!
# Literal definitions and magnitude normalizations

The unit-group Bernoulli transform equals the displayed weighted residue
sum, including its zero extension. Its previously proved squared L-value
identity also yields the unsquared magnitude and the paper's normalization.
-/

set_option autoImplicit false

namespace NField.Alignment.PrimeSquareMagnitudeFamily

open scoped BigOperators ComplexConjugate ZMod
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionSpectrumLandscape
open NField.Alignment.CarryBoundarySpectra
open NField.Alignment.OddBernoulliMoments

theorem bernoulliSum_eq_full_residue_sum {b : ℕ} [NeZero (b^2)]
    (χ : PrimitiveOddFamily b) :
    bernoulliSum b χ = (b : ℂ)⁻¹^2 *
      ∑ a ∈ Finset.Ico 1 (b^2), (a : ℂ)*star (χ.val (a : ZMod (b^2))) := by
  classical
  unfold bernoulliSum generalizedBernoulliOne
  rw [← sum_character_pairing_eq_units (fun x : ZMod (b^2) => (x.val : ℂ)) χ.val⁻¹]
  simp only [← MulChar.star_apply', Nat.cast_pow, inv_pow]
  congr 1
  have hs : (∑ x : ZMod (b^2), (x.val : ℂ)*star (χ.val x)) =
      ∑ a ∈ Finset.range (b^2), (a : ℂ)*star (χ.val (a : ZMod (b^2))) := by
    rw [← sum_zmod_val (fun a => (a : ℂ)*star (χ.val (a : ZMod (b^2))))]
    simp only [ZMod.natCast_zmod_val]
  rw [hs]
  symm
  apply Finset.sum_subset
  · intro a ha
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp ha).2
  · intro a ha hnot
    have ha' := Finset.mem_range.mp ha
    have ha0 : a = 0 := by
      simp only [Finset.mem_Ico, not_and] at hnot
      omega
    simp [ha0]

theorem bernoulli_l_magnitude {b : ℕ} [NeZero (b^2)]
    (hb : b.Prime) (χ : PrimitiveOddFamily b) :
    ‖bernoulliSum b χ‖ = (b : ℝ)/Real.pi * ‖DirichletCharacter.LFunction χ.val 1‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  have h := bernoulli_l_magnitude_sq hb χ
  simpa only [Complex.normSq_eq_norm_sq, Nat.cast_pow, mul_pow, div_pow] using h

theorem normalized_bernoulli_l_magnitude {b : ℕ} [NeZero (b^2)]
    (hb : b.Prime) (χ : PrimitiveOddFamily b) :
    Real.pi * ‖bernoulliSum b χ‖ / b = lMagnitude b χ := by
  rw [bernoulli_l_magnitude hb]
  have hb0 : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne_zero
  unfold lMagnitude
  field_simp

end NField.Alignment.PrimeSquareMagnitudeFamily

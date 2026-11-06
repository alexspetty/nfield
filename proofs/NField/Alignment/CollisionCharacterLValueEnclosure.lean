/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionComplexSeriesEnclosure
import NField.Alignment.CollisionAmplitudeCotangent
import Mathlib.NumberTheory.DirichletCharacter.Bounds

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.CollisionCharacterLValueEnclosure
open scoped BigOperators
open CollisionComplexPhaseEnclosure CollisionComplexSeriesEnclosure
open CollisionCotangentMixedMoment CollisionCotangentLValue CollisionFourierEnclosure
open CollisionHarmonicRootSeries

def characterLTwoPrefix {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (N : ℕ) : ℂ :=
  ∑ n∈Finset.range (N+1),χ (n : ZMod q)/(n : ℂ)^2

theorem character_square_term_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖χ (n : ZMod q)/(n : ℂ)^2‖ ≤ 1/(n : ℝ)^2 := by
  rw [norm_div,norm_pow,Complex.norm_natCast]
  exact div_le_div_of_nonneg_right (χ.norm_le_one _) (sq_nonneg _)

theorem character_L_two_tail {q N : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hN : 1 ≤ N) :
    ‖DirichletCharacter.LFunction χ 2-characterLTwoPrefix χ N‖ ≤ 1/(N : ℝ) := by
  rw [← (character_L_two_hasSum χ).tsum_eq]
  exact norm_series_tail_bound (character_L_two_hasSum χ).summable N
    (inverseSquare_summable.comp_injective (fun a b h => by omega))
    (fun n => character_square_term_bound χ (n+N+1)) (reciprocal_square_tail hN)

theorem character_L_two_enclosure {q N : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hN : 1 ≤ N) {rl ru il iu : ℝ}
    (hp : rectangleContains (characterLTwoPrefix χ N) rl ru il iu) :
    rectangleContains (DirichletCharacter.LFunction χ 2)
      (rl-1/(N : ℝ)) (ru+1/(N : ℝ)) (il-1/(N : ℝ)) (iu+1/(N : ℝ)) :=
  norm_error_rectangle hp (character_L_two_tail χ hN)

theorem character_L_one_from_coefficient {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.Odd) :
    DirichletCharacter.LFunction χ⁻¹ 1=((Real.pi : ℂ)/(2*(q : ℂ)))*
      (∑ a : (ZMod q)ˣ, star (χ a.val)*cotangentSignal a) := by
  rw [cotangent_signal_coefficient χ,if_pos hχ]
  have hq : (q : ℂ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hp : (Real.pi : ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

theorem character_L_one_enclosure {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.Odd) {rl ru il iu pl pu : ℝ}
    (hc : rectangleContains (∑ a : (ZMod q)ˣ, star (χ a.val)*cotangentSignal a) rl ru il iu)
    (hp : pl ≤ Real.pi ∧ Real.pi ≤ pu) :
    rectangleContains (DirichletCharacter.LFunction χ⁻¹ 1)
      (productLower rl ru (pl/(2*(q : ℝ))) (pu/(2*(q : ℝ))))
      (productUpper rl ru (pl/(2*(q : ℝ))) (pu/(2*(q : ℝ))))
      (productLower il iu (pl/(2*(q : ℝ))) (pu/(2*(q : ℝ))))
      (productUpper il iu (pl/(2*(q : ℝ))) (pu/(2*(q : ℝ)))) := by
  rw [character_L_one_from_coefficient χ hχ]
  have he : ((Real.pi/(2*(q : ℝ)) : ℝ) : ℂ)=(Real.pi : ℂ)/(2*(q : ℂ)) := by push_cast; rfl
  rw [← he]
  exact real_scale_enclosure hc ⟨div_le_div_of_nonneg_right hp.1 (by positivity),
    div_le_div_of_nonneg_right hp.2 (by positivity)⟩

theorem character_L_two_prefix_enclosure {q N : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (rl ru il iu : ℕ → ℝ)
    (h : ∀ n∈Finset.range (N+1), rectangleContains (χ (n : ZMod q)/(n : ℂ)^2)
      (rl n) (ru n) (il n) (iu n)) :
    rectangleContains (characterLTwoPrefix χ N)
      (∑ n∈Finset.range (N+1),rl n) (∑ n∈Finset.range (N+1),ru n)
      (∑ n∈Finset.range (N+1),il n) (∑ n∈Finset.range (N+1),iu n) :=
  sum_enclosure _ _ _ _ _ _ h

end NField.Alignment.CollisionCharacterLValueEnclosure

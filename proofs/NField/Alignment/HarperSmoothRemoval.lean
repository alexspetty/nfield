/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperSmoothCountDecay
import NField.Alignment.MagnitudeShortComparison
import NField.Alignment.FiniteMagnitudeDecorrelation
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# The actual character contribution of the removed smooth integers

Finite character orthogonality gives the second moment on the actual smooth
support. The normalized power-mean inequality bounds its three-halves moment
by the smooth count to the three-quarter power. The count decay then proves
the required negligible error, uniformly for bounded short coefficients.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperSmoothRemoval

open scoped BigOperators
open Filter Asymptotics SteinhausMoment MagnitudeShortComparison
  SpectralRepulsion CollisionCharacterStructure FiniteMagnitudeDecorrelation
  HarperSmoothCount HarperSmoothCountDecay HarperRoundedCutoff HarperConditioningDecay

theorem average_fractional_le_second {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) :
    uniformAverage (fun i => (f i)^(3/2 : ℝ)) ≤
      (uniformAverage (fun i => (f i)^2))^(3/4 : ℝ) := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hw : ∑ _i : ι, (Fintype.card ι : ℝ)⁻¹ = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hn]
  have h := Real.arith_mean_le_rpow_mean (s := Finset.univ)
    (fun _ : ι => (Fintype.card ι : ℝ)⁻¹) (fun i => (f i)^(3/2 : ℝ))
    (fun _ _ => by positivity) hw (fun i _ => Real.rpow_nonneg (hf i) _)
    (by norm_num : (1 : ℝ) ≤ 4/3)
  have he (i : ι) : ((f i)^(3/2 : ℝ))^(4/3 : ℝ) = (f i)^2 := by
    rw [← Real.rpow_mul (hf i)]
    norm_num
  simp_rw [he, ← Finset.mul_sum] at h
  simpa only [uniformAverage, show (1/(4/3) : ℝ) = 3/4 by norm_num] using h

theorem finite_supported_moment_bound {q : ℕ} [NeZero q] (s : Finset ℕ) (w : ℕ → ℂ)
    (hs : ∀ n ∈ s, 0 < n ∧ n < q ∧ n.Coprime q) (hw : ∀ n ∈ s, ‖w n‖ ≤ 1) :
    uniformAverage (fun χ : Character q => ‖∑ n ∈ s, w n * χ (n : ZMod q)‖^(3/2 : ℝ)) ≤
      (s.card : ℝ)^(3/4 : ℝ) := by
  refine (average_fractional_le_second _ (fun _ => norm_nonneg _)).trans ?_
  apply Real.rpow_le_rpow (average_nonneg (fun _ => sq_nonneg _)) _ (by norm_num)
  rw [polynomial_second_moment_comparison s w hs,
    polynomial_second_moment s w (fun n hn => (hs n hn).1.ne')]
  calc
    _ ≤ ∑ _n ∈ s, (1 : ℝ) := Finset.sum_le_sum
      (fun n hn => pow_le_one₀ (norm_nonneg _) (hw n hn))
    _ = _ := by simp

theorem smooth_support_units {p : ℕ} (hp : p.Prime) (y : ℝ) :
    ∀ n ∈ smoothSet ((p : ℝ)-1) y, 0 < n ∧ n < p^2 ∧ n.Coprime (p^2) := by
  intro n hn
  have h := smoothSet_mem.mp hn
  have hnp : n < p := by exact_mod_cast (show (n : ℝ) < p by linarith [h.2.1])
  exact ⟨h.1, by nlinarith [hp.two_le], small_factor_unit hp h.1 hnp⟩

theorem smooth_character_moment_bound {p : ℕ} [NeZero (p^2)] (hp : p.Prime)
    (y : ℝ) (w : ℕ → ℂ) (hw : ∀ n ∈ smoothSet ((p : ℝ)-1) y, ‖w n‖ ≤ 1) :
    uniformAverage (fun χ : Character (p^2) =>
      ‖∑ n ∈ smoothSet ((p : ℝ)-1) y, w n * χ (n : ZMod (p^2))‖^(3/2 : ℝ)) ≤
      (smoothCount ((p : ℝ)-1) y)^(3/4 : ℝ) :=
  finite_supported_moment_bound _ _ (smooth_support_units hp y) hw

/-- The smooth contribution is negligible at the printed target, uniformly
over all coefficients bounded by one on the removed support. -/
theorem eventual_smooth_removal {epsilon : ℝ} (he : 0 < epsilon) : ∀ᶠ p : ℕ in atTop,
    let x := (p : ℝ)-1
    let y := smoothCutoff x
    ∀ [NeZero (p^2)], p.Prime → ∀ w : ℕ → ℂ,
    (∀ n ∈ smoothSet x y, ‖w n‖ ≤ 1) →
    uniformAverage (fun χ : Character (p^2) =>
      ‖∑ n ∈ smoothSet x y, w n * χ (n : ZMod (p^2))‖^(3/2 : ℝ)) ≤
      epsilon * targetScale x := by
  filter_upwards [prime_square_smoothCount_decay.bound he,
    base_minus_one_tendsto.eventually_gt_atTop 0,
    ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp base_minus_one_tendsto).eventually_gt_atTop 0]
    with p hb hx hu
  dsimp only at hb ⊢
  dsimp only [Function.comp_apply] at hx hu
  have ht : 0 ≤ targetScale ((p : ℝ)-1) := by unfold targetScale; positivity
  have hc : 0 ≤ smoothCount ((p : ℝ)-1) (smoothCutoff ((p : ℝ)-1)) := by
    unfold smoothCount
    positivity
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hc _), Real.norm_of_nonneg ht] at hb
  intro _ hp w hw
  exact (smooth_character_moment_bound hp _ w hw).trans hb

end NField.Alignment.HarperSmoothRemoval

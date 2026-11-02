/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperRemainderDecay

/-!
# Actual per-box character/random comparison rates

Both error rates use the original smooth partition at the literal rounded
parameters. Coefficient bounds are explicit; the analytic comparison errors,
prime energies, arithmetic support conditions and remainder decay are proved.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperBoxComparison

open scoped BigOperators
open MeasureTheory Filter SteinhausMoment HarperPrimeProductMoment
  HarperProductApproximation HarperSmoothComparison HarperPrimeEnergyBound
  HarperRemainderDecay HarperFactorialDecay HarperParameterBounds HarperRoundedCutoff
  HarperConditioningDecay MagnitudeShortComparison
  SpectralRepulsion CollisionMertensInput CollisionCharacterStructure

theorem eventual_weighted_box_error : ∃ C : ℝ, 0 < C ∧ ∀ᶠ p : ℕ in atTop,
    let x := (p : ℝ) - 1
    let P := primeCutoff x
    let A := factorCount x
    let delta := precision (cutoffLog x)
    let J := rangeCount (cutoffLog x)
    ∀ [NeZero (p ^ 2)], p.Prime →
    ∀ (labels : Fin A → Fin (2 * J + 2)) (c1 c2 : Fin A → ℕ → ℂ) (w : ℕ → ℂ),
    (∀ i r, r ∈ primesUpTo P → ‖c1 i r‖ ≤ 1) →
    (∀ i r, r ∈ primesUpTo P → ‖c2 i r‖ ≤ 1) →
    (∀ n ∈ Finset.Icc 1 (p - 1), ‖w n‖ ≤ 1) →
    |uniformAverage (fun χ : Character (p ^ 2) =>
        ‖∑ n ∈ Finset.Icc 1 (p - 1), w n * χ (n : ZMod (p ^ 2))‖ ^ 2 *
          smoothValue delta J A P labels c1 c2 (fun n => χ (n : ZMod (p ^ 2)))) -
      ∫ ω, ‖∑ n ∈ Finset.Icc 1 (p - 1), w n * steinhaus n ω‖ ^ 2 *
        smoothValue delta J A P labels c1 c2 (fun n => steinhaus n ω) ∂phaseMeasure| ≤
      C * x * boxError (cutoffLog x) := by
  obtain ⟨C, hC, hshort⟩ := eventual_shortEnergy_bound
  refine ⟨2 * C, by positivity, ?_⟩
  filter_upwards [hshort, eventual_weighted_smooth_comparison,
    base_minus_one_tendsto.eventually eventual_weighted_error_le,
    (cutoffLog_tendsto.comp base_minus_one_tendsto).eventually_gt_atTop 0,
    (Real.tendsto_log_atTop.comp (cutoffLog_tendsto.comp base_minus_one_tendsto)).eventually_ge_atTop 1]
    with p hs hc he hell hlog
  dsimp only at hs hc he ⊢
  dsimp only [Function.comp_apply] at hell hlog
  intro _ hp labels c1 c2 w h1 h2 hw
  have hd := precision_pos hell
  have hj : 0 < rangeCount (cutoffLog ((p : ℝ) - 1)) := by
    exact_mod_cast lt_of_lt_of_le zero_lt_one (rangeCount_bounds hell hlog).1
  have hx : 0 ≤ (p : ℝ) - 1 := by
    have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  have hE : 0 ≤ roundedError ((p : ℝ) - 1) (2 * unitPrimeEnergy (primeCutoff ((p : ℝ) - 1))) :=
    errorSum_nonneg hd (by positivity [unitPrimeEnergy_nonneg (primeCutoff ((p : ℝ) - 1))]) _ _ _
  refine (hc hp _ hd _ hj labels c1 c2 w h1 h2).trans ?_
  change 2 * shortEnergy _ _ w * roundedError _ _ ≤ _
  calc
    _ ≤ 2 * (C * ((p : ℝ) - 1) * cutoffLog ((p : ℝ) - 1)) *
        roundedError ((p : ℝ) - 1) (2 * unitPrimeEnergy (primeCutoff ((p : ℝ) - 1))) := by
      gcongr
      exact hs w hw
    _ = (2 * C) * ((p : ℝ) - 1) *
        (cutoffLog ((p : ℝ) - 1) * roundedError ((p : ℝ) - 1)
          (2 * unitPrimeEnergy (primeCutoff ((p : ℝ) - 1)))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left he (by positivity)

theorem eventual_weight_box_error : ∀ᶠ p : ℕ in atTop,
    let x := (p : ℝ) - 1
    let P := primeCutoff x
    let A := factorCount x
    let delta := precision (cutoffLog x)
    let J := rangeCount (cutoffLog x)
    ∀ [NeZero (p ^ 2)], p.Prime →
    ∀ (labels : Fin A → Fin (2 * J + 2)) (c1 c2 : Fin A → ℕ → ℂ),
    (∀ i r, r ∈ primesUpTo P → ‖c1 i r‖ ≤ 1) →
    (∀ i r, r ∈ primesUpTo P → ‖c2 i r‖ ≤ 1) →
    |uniformAverage (fun χ : Character (p ^ 2) =>
        smoothValue delta J A P labels c1 c2 (fun n => χ (n : ZMod (p ^ 2)))) -
      ∫ ω, smoothValue delta J A P labels c1 c2 (fun n => steinhaus n ω) ∂phaseMeasure| ≤
      2 * boxError (cutoffLog x) := by
  filter_upwards [eventual_smooth_weight_comparison,
    base_minus_one_tendsto.eventually eventual_unweighted_error_le,
    (cutoffLog_tendsto.comp base_minus_one_tendsto).eventually_gt_atTop 0,
    (Real.tendsto_log_atTop.comp (cutoffLog_tendsto.comp base_minus_one_tendsto)).eventually_ge_atTop 1]
    with p hc he hell hlog
  dsimp only at hc he ⊢
  dsimp only [Function.comp_apply] at hell hlog
  intro _ hp labels c1 c2 h1 h2
  have hd := precision_pos hell
  have hj : 0 < rangeCount (cutoffLog ((p : ℝ) - 1)) := by
    exact_mod_cast lt_of_lt_of_le zero_lt_one (rangeCount_bounds hell hlog).1
  exact (hc hp _ hd _ hj labels c1 c2 h1 h2).trans
    (mul_le_mul_of_nonneg_left he (by norm_num))

end NField.Alignment.HarperBoxComparison

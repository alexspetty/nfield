/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperShiftedEulerProduct
import NField.Alignment.HarperConditioningDecay

/-!
# Smooth-count decay at the manuscript's cutoff

The Rankin factor is evaluated exactly at y=x^(1/log(log x)). The resulting
count is O(x/log(log x)), so its three-quarter power is negligible at the
short fractional-moment target. The previously proved cutoff hierarchy is
reused without changing its rounding or endpoint conventions.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperSmoothCountDecay

open Filter Asymptotics HarperRoundedCutoff HarperSmoothDivisor
  HarperSmoothCount HarperShiftedEulerProduct HarperConditioningDecay
open scoped Topology

theorem smoothCutoff_tendsto : Tendsto smoothCutoff atTop atTop :=
  tendsto_atTop_mono' atTop (eventual_cutoff_hierarchy.mono (fun _ h => h.1.le)) primeCutoff_tendsto

theorem log_smoothCutoff {x : ℝ} (hx : 0 < x) :
    Real.log (smoothCutoff x) = Real.log x / Real.log (Real.log x) := by
  rw [smoothCutoff, Real.log_rpow hx]
  ring

theorem rankin_scale_identity {x : ℝ} (hx : 1 < x) (hu : 0 < Real.log (Real.log x)) :
    x^(shift (smoothCutoff x)) * Real.log (smoothCutoff x) = x / Real.log (Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hl := Real.log_pos hx
  have he : x^(1 / Real.log (smoothCutoff x)) = Real.log x := by
    rw [Real.rpow_def_of_pos hx0, log_smoothCutoff hx0]
    have harg : Real.log x * (1 / (Real.log x / Real.log (Real.log x))) = Real.log (Real.log x) := by
      field_simp
    rw [harg, Real.exp_log hl]
  rw [shift, Real.rpow_sub hx0, Real.rpow_one, he, log_smoothCutoff hx0]
  field_simp

theorem eventual_smoothCount_bound : ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
    smoothCount x (smoothCutoff x) ≤ C * (x / Real.log (Real.log x)) := by
  obtain ⟨C, hC, hp⟩ := eventual_shiftedProduct_log_bound
  refine ⟨C, hC, ?_⟩
  filter_upwards [smoothCutoff_tendsto.eventually hp,
    (Real.tendsto_log_atTop.comp smoothCutoff_tendsto).eventually_ge_atTop 2,
    eventually_gt_atTop (1 : ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_gt_atTop 0]
    with x hprod hy hx hu
  dsimp only [Function.comp_apply] at hy hu
  have hs : 0 < shift (smoothCutoff x) := by linarith [(shift_bounds hy).1]
  calc
    _ ≤ x^(shift (smoothCutoff x)) * shiftedProduct (smoothCutoff x) (shift (smoothCutoff x)) :=
      rankin_bound (by linarith) _ hs
    _ ≤ x^(shift (smoothCutoff x)) * (C * Real.log (smoothCutoff x)) :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = C * (x^(shift (smoothCutoff x)) * Real.log (smoothCutoff x)) := by ring
    _ = _ := by rw [rankin_scale_identity hx hu]

theorem smoothCount_isBigO : (fun x => smoothCount x (smoothCutoff x)) =O[atTop]
    (fun x => x / Real.log (Real.log x)) := by
  obtain ⟨C, _, hb⟩ := eventual_smoothCount_bound
  apply IsBigO.of_bound C
  filter_upwards [hb, eventually_gt_atTop (0 : ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_gt_atTop 0] with x hb hx hu
  dsimp only [Function.comp_apply] at hu
  simpa only [Real.norm_of_nonneg (show 0 ≤ smoothCount x (smoothCutoff x) by unfold smoothCount; positivity),
    Real.norm_of_nonneg (div_nonneg hx.le hu.le)] using hb

theorem inverse_power_isLittleO : (fun u : ℝ => u^(-(3/4 : ℝ))) =o[atTop]
    (fun u : ℝ => u^(-(3/8 : ℝ))) := by
  apply isLittleO_of_tendsto' (by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    exact fun hz => ((Real.rpow_pos_of_pos hu _).ne' hz).elim)
  apply (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3/8)).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  rw [← Real.rpow_sub hu]
  norm_num

theorem smoothCount_fractional_isLittleO :
    (fun x => (smoothCount x (smoothCutoff x))^(3/4 : ℝ)) =o[atTop] targetScale := by
  have hg : ∀ᶠ x : ℝ in atTop, 0 ≤ x / Real.log (Real.log x) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ),
      (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_gt_atTop 0] with x hx hu
    exact div_nonneg hx.le hu.le
  have hpow := smoothCount_isBigO.rpow (by norm_num : (0 : ℝ) ≤ 3/4) hg
  have he : (fun x : ℝ => (x / Real.log (Real.log x))^(3/4 : ℝ)) =ᶠ[atTop]
      (fun x => x^(3/4 : ℝ) * (Real.log (Real.log x))^(-(3/4 : ℝ))) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ),
      (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_gt_atTop 0] with x hx hu
    dsimp only [Function.comp_apply] at hu
    rw [Real.div_rpow hx.le hu.le, Real.rpow_neg hu.le, div_eq_mul_inv]
  exact (hpow.congr' Filter.EventuallyEq.rfl he).trans_isLittleO
    ((isBigO_refl (fun x : ℝ => x^(3/4 : ℝ)) atTop).mul_isLittleO
      (inverse_power_isLittleO.comp_tendsto (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)))

theorem prime_square_smoothCount_decay :
    (fun p : ℕ => (smoothCount ((p : ℝ)-1) (smoothCutoff ((p : ℝ)-1)))^(3/4 : ℝ)) =o[atTop]
      (fun p : ℕ => targetScale ((p : ℝ)-1)) :=
  smoothCount_fractional_isLittleO.comp_tendsto base_minus_one_tendsto

end NField.Alignment.HarperSmoothCountDecay

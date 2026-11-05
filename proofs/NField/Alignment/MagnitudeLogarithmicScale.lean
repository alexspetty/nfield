/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperLowMomentScales

/-!
# Passing the short-window rate from b-1 to b

These elementary estimates preserve the exponent -3/8 and the exact
b^(3/4) normalization in the manuscript's primitive odd character moment.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.MagnitudeLogarithmicScale
open Filter HarperConditioningDecay

theorem eventual_loglog_shift : ∀ᶠ x : ℝ in atTop,
    2 < x ∧ 0 < Real.log (Real.log x) ∧
    Real.log (Real.log x)/2 ≤ Real.log (Real.log (x-1)) := by
  filter_upwards [eventually_gt_atTop (2 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (2*Real.log 2),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop
      (max 1 (2*Real.log 2))] with x hx hl hll
  dsimp only [Function.comp_apply] at hll
  have hx0 : 0 < x := by linarith
  have hl0 : 0 < Real.log x := Real.log_pos (by linarith)
  have h1 := Real.log_le_log (show 0 < x/2 by positivity)
    (show x/2 ≤ x-1 by linarith)
  rw [Real.log_div (ne_of_gt hx0) (by norm_num)] at h1
  have hhalf : Real.log x/2 ≤ Real.log (x-1) := by linarith
  have h2 := Real.log_le_log (show 0 < Real.log x/2 by positivity) hhalf
  rw [Real.log_div (ne_of_gt hl0) (by norm_num)] at h2
  have hll1 := (le_max_left _ _).trans hll
  have hll2 := (le_max_right _ _).trans hll
  exact ⟨hx,by linarith,by linarith⟩

theorem shifted_negative_power {Y T : ℝ} (hY : 0 < Y) (hT : Y/2 ≤ T) :
    T^(-(3/8 : ℝ)) ≤ 2*Y^(-(3/8 : ℝ)) := by
  have hT0 : 0 < T := by linarith
  rw [Real.rpow_neg hT0.le, Real.rpow_neg hY.le]
  have hpow : Y^(3/8 : ℝ) ≤ 2*T^(3/8 : ℝ) := by
    calc
      _ ≤ (2*T)^(3/8 : ℝ) := Real.rpow_le_rpow hY.le (by linarith) (by norm_num)
      _ = (2 : ℝ)^(3/8 : ℝ)*T^(3/8 : ℝ) := Real.mul_rpow (by norm_num) hT0.le
      _ ≤ _ := mul_le_mul_of_nonneg_right (by
        simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          (by norm_num : (3/8 : ℝ) ≤ 1)) (by positivity)
  rw [← one_div (T^(3/8 : ℝ)), ← one_div (Y^(3/8 : ℝ)), ← mul_div_assoc]
  exact (div_le_div_iff₀ (by positivity) (by positivity)).2 (by simpa using hpow)

theorem eventual_normalized_target_bound : ∀ᶠ x : ℝ in atTop,
    targetScale (x-1)/x^(3/4 : ℝ) ≤ 2*(Real.log (Real.log x))^(-(3/8 : ℝ)) := by
  filter_upwards [eventual_loglog_shift] with x hx
  have hx0 : 0 < x := by linarith [hx.1]
  have hxm : 0 ≤ x-1 := by linarith [hx.1]
  have hT : 0 < Real.log (Real.log (x-1)) := by linarith [hx.2.1,hx.2.2]
  have hp := Real.rpow_le_rpow hxm (show x-1 ≤ x by linarith) (by norm_num : (0 : ℝ) ≤ 3/4)
  have hneg := shifted_negative_power hx.2.1 hx.2.2
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hx0 _)).2
  unfold targetScale
  calc
    _ ≤ x^(3/4 : ℝ)*(2*(Real.log (Real.log x))^(-(3/8 : ℝ))) :=
      mul_le_mul hp hneg (Real.rpow_nonneg hT.le _) (by positivity)
    _ = _ := by ring

end NField.Alignment.MagnitudeLogarithmicScale

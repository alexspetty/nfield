/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperCriticalLowMoment
import NField.Alignment.HarperConditioningDecay

/-!
# The critical low-moment scale at the actual rounded prime cutoff

Both directions of comparison are retained: the negligible errors already
controlled at targetScale can therefore also be absorbed at the intermediate
scale printed in the short-sum proof.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperLowMomentScales
open Filter HarperRoundedCutoff HarperConditioningDecay

def intermediateScale (x : ℝ) : ℝ :=
  (x/(1+(1/4)*Real.sqrt (Real.log (Real.log (primeCutoff x)))))^(3/4 : ℝ)

theorem primeCutoff_tendsto : Tendsto primeCutoff atTop atTop :=
  Real.tendsto_exp_atTop.comp cutoffLog_tendsto

theorem eventual_log_cutoff_bounds : ∀ᶠ x : ℝ in atTop,
    1 < x ∧ 1 ≤ Real.log (Real.log x) ∧
    Real.log (Real.log x)/12 ≤ Real.log (Real.log (primeCutoff x)) ∧
    Real.log (Real.log (primeCutoff x)) ≤ Real.log (Real.log x) := by
  have hr := cutoffLog_ratio_limit.eventually
    (eventually_gt_nhds (by norm_num : (1/2 : ℝ) < 1))
  filter_upwards [hr, eventually_gt_atTop (1 : ℝ),
    cutoffLog_tendsto.eventually_gt_atTop 0,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop
      (max 1 (12*Real.log 2))] with x hx hx1 hc hll
  dsimp only [Function.comp_apply] at hll
  have hl := Real.log_pos hx1
  have hp : 0 < (Real.log x)^(1/6 : ℝ) := Real.rpow_pos_of_pos hl _
  have hratio := (lt_div_iff₀ hp).mp hx
  have hroot : (Real.log x)^(1/6 : ℝ) ≤ 2*cutoffLog x := by linarith
  have hlo := Real.log_le_log hp hroot
  rw [Real.log_rpow hl, Real.log_mul (by norm_num) (ne_of_gt hc)] at hlo
  have hhi := Real.log_le_log hc (cutoffLog_le_sixth_root hx1.le)
  rw [Real.log_rpow hl] at hhi
  rw [log_primeCutoff]
  exact ⟨hx1, (le_max_left _ _).trans hll, by
    have := (le_max_right _ _).trans hll
    linarith, by have := (le_max_left _ _).trans hll; linarith⟩

theorem denominator_bounds {Y T : ℝ} (hY : 1 ≤ Y)
    (hlo : Y/12 ≤ T) (hhi : T ≤ Y) :
    Real.sqrt Y/16 ≤ 1+(1/4)*Real.sqrt T ∧
    1+(1/4)*Real.sqrt T ≤ 2*Real.sqrt Y := by
  have hY0 : 0 ≤ Y := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hy := Real.sq_sqrt hY0
  have ht := Real.sq_sqrt hT0
  have hy0 := Real.sqrt_nonneg Y
  have ht0 := Real.sqrt_nonneg T
  have hroot : Real.sqrt Y ≤ 4*Real.sqrt T := by nlinarith
  have hroot1 : 1 ≤ Real.sqrt Y := by nlinarith
  have hroot2 := Real.sqrt_le_sqrt hhi
  constructor <;> linarith

theorem targetScale_eq_quotient {x : ℝ} (hx : 0 ≤ x)
    (hY : 0 ≤ Real.log (Real.log x)) :
    targetScale x = (x/Real.sqrt (Real.log (Real.log x)))^(3/4 : ℝ) := by
  rw [Real.div_rpow hx (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
    ← Real.rpow_mul hY]
  norm_num only [show (1/2 : ℝ)*(3/4)=3/8 by norm_num]
  rw [targetScale, Real.rpow_neg hY]
  rfl

theorem eventual_scale_comparison : ∀ᶠ x : ℝ in atTop,
    intermediateScale x ≤ 16*targetScale x ∧
    targetScale x ≤ 2*intermediateScale x := by
  filter_upwards [eventual_log_cutoff_bounds] with x hx
  have hx0 : 0 ≤ x := by linarith [hx.1]
  have hY0 : 0 ≤ Real.log (Real.log x) := by linarith [hx.2.1]
  have hs : 0 < Real.sqrt (Real.log (Real.log x)) := Real.sqrt_pos.2 (by linarith [hx.2.1])
  have hd : 0 < 1+(1/4 : ℝ)*Real.sqrt (Real.log (Real.log (primeCutoff x))) := by positivity
  obtain ⟨hlo,hhi⟩ := denominator_bounds hx.2.1 hx.2.2.1 hx.2.2.2
  rw [targetScale_eq_quotient hx0 hY0]
  unfold intermediateScale
  constructor
  · have hdv : x/(1+(1/4 : ℝ)*Real.sqrt (Real.log (Real.log (primeCutoff x)))) ≤
        16*(x/Real.sqrt (Real.log (Real.log x))) := by
      rw [← mul_div_assoc]
      apply (div_le_div_iff₀ hd hs).2
      nlinarith [mul_le_mul_of_nonneg_left hlo hx0]
    calc
      _ ≤ (16*(x/Real.sqrt (Real.log (Real.log x))))^(3/4 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hdv (by norm_num)
      _ = (16 : ℝ)^(3/4 : ℝ)*(x/Real.sqrt (Real.log (Real.log x)))^(3/4 : ℝ) :=
        Real.mul_rpow (by norm_num) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by
        simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 16)
          (by norm_num : (3/4 : ℝ) ≤ 1)) (by positivity)
  · have hdv : x/Real.sqrt (Real.log (Real.log x)) ≤
        2*(x/(1+(1/4 : ℝ)*Real.sqrt (Real.log (Real.log (primeCutoff x))))) := by
      rw [← mul_div_assoc]
      apply (div_le_div_iff₀ hs hd).2
      nlinarith [mul_le_mul_of_nonneg_left hhi hx0]
    calc
      _ ≤ (2*(x/(1+(1/4 : ℝ)*Real.sqrt (Real.log (Real.log (primeCutoff x))))))^(3/4 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hdv (by norm_num)
      _ = (2 : ℝ)^(3/4 : ℝ)*(x/(1+(1/4 : ℝ)*Real.sqrt (Real.log (Real.log (primeCutoff x)))))^(3/4 : ℝ) :=
        Real.mul_rpow (by norm_num) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by
        simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          (by norm_num : (3/4 : ℝ) ≤ 1)) (by positivity)

end NField.Alignment.HarperLowMomentScales

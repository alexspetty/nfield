/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperTaylorBudget

/-!
# Lower bounds for the actual rounded Taylor order

The natural floor loses at most one. Once its argument is at least 100,
the manuscript's factor 100 therefore retains a factor 99. All estimates
here use the actual rounded cutoff and factor count.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperTaylorGrowth

open Filter HarperParameterBounds HarperRoundedCutoff HarperTaylorBudget

theorem precision_le_one {ell : ℝ} (hell : 1 ≤ ell) : precision ell ≤ 1 := by
  exact Real.rpow_le_one_of_one_le_of_nonpos hell (by norm_num)

theorem taylorArgument_cancel {ell : ℝ} (hell : 0 < ell) :
    taylorArgument ell * precision ell ^ 2 = Real.log ((rangeCount ell : ℝ) * ell) := by
  have hd := precision_pos hell
  have he : precision ell ^ (-2 : ℝ) = (precision ell ^ 2)⁻¹ := by
    rw [Real.rpow_neg hd.le]
    norm_num
  rw [taylorArgument, he]
  field_simp

theorem taylorArgument_ge_self {ell : ℝ} (hell : 1 ≤ ell) (hlog : 1 ≤ Real.log ell) :
    ell ≤ taylorArgument ell := by
  have hp : 0 < ell := lt_of_lt_of_le zero_lt_one hell
  have hj := (rangeCount_bounds hp hlog).1
  have hl : 1 ≤ Real.log ((rangeCount ell : ℝ) * ell) :=
    hlog.trans (Real.log_le_log hp (by nlinarith))
  rw [taylorArgument_eq hp.le]
  calc
    _ ≤ ell ^ (13/5 : ℝ) := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hell (by norm_num : (1 : ℝ) ≤ 13/5)
    _ ≤ _ := le_mul_of_one_le_right (by positivity) hl

theorem factorCount_ge_cutoff {x : ℝ} (hell : 1 ≤ cutoffLog x) :
    cutoffLog x ≤ (factorCount x : ℝ) := by
  have hpow : cutoffLog x ≤ cutoffLog x ^ (51/50 : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hell (by norm_num : (1 : ℝ) ≤ 51/50)
  rw [factorCount_eq, partitionCount]
  linarith

theorem taylorOrder_lower {x : ℝ} (harg : 100 ≤ taylorArgument (cutoffLog x)) :
    99 * (factorCount x : ℝ) * taylorArgument (cutoffLog x) ≤ (taylorOrder x : ℝ) := by
  have hf := Nat.lt_floor_add_one (taylorArgument (cutoffLog x))
  have hfloor : 99 * taylorArgument (cutoffLog x) ≤
      100 * (⌊taylorArgument (cutoffLog x)⌋₊ : ℝ) := by linarith
  unfold taylorOrder
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left hfloor (Nat.cast_nonneg (factorCount x) :
    (0 : ℝ) ≤ factorCount x)]

theorem taylorOrder_bounds {x : ℝ} (hell : 100 ≤ cutoffLog x)
    (hlog : 1 ≤ Real.log (cutoffLog x)) :
    100 * (factorCount x : ℝ) ≤ (taylorOrder x : ℝ) ∧
    cutoffLog x ≤ (taylorOrder x : ℝ) ∧
    99 * (factorCount x : ℝ) *
        Real.log ((rangeCount (cutoffLog x) : ℝ) * cutoffLog x) ≤
      precision (cutoffLog x) ^ 2 * (taylorOrder x : ℝ) ∧
    3 * (rangeCount (cutoffLog x) : ℝ) ≤ precision (cutoffLog x) * (taylorOrder x : ℝ) := by
  have hellp : 0 < cutoffLog x := by linarith
  have hell1 : 1 ≤ cutoffLog x := by linarith
  have hd := precision_pos hellp
  have hd1 := precision_le_one hell1
  have hA := factorCount_ge_cutoff hell1
  have harg := hell.trans (taylorArgument_ge_self hell1 hlog)
  have hlow := taylorOrder_lower harg
  have hfloor : 1 ≤ ⌊taylorArgument (cutoffLog x)⌋₊ :=
    Nat.le_floor (by norm_num; linarith)
  have hS : 100 * (factorCount x : ℝ) ≤ (taylorOrder x : ℝ) := by
    unfold taylorOrder
    push_cast
    exact le_mul_of_one_le_right (by positivity) (by exact_mod_cast hfloor)
  have hscaled : 99 * (factorCount x : ℝ) *
        Real.log ((rangeCount (cutoffLog x) : ℝ) * cutoffLog x) ≤
      precision (cutoffLog x) ^ 2 * (taylorOrder x : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hlow (sq_nonneg (precision (cutoffLog x)))
    rw [mul_assoc (99 * (factorCount x : ℝ)), taylorArgument_cancel hellp] at h
    simpa only [mul_comm] using h
  have hr := rangeCount_bounds hellp hlog
  have hl : 1 ≤ Real.log ((rangeCount (cutoffLog x) : ℝ) * cutoffLog x) :=
    hlog.trans (Real.log_le_log hellp (by nlinarith [hr.1]))
  refine ⟨hS, by nlinarith, hscaled, ?_⟩
  have h1 : 99 * (factorCount x : ℝ) ≤ precision (cutoffLog x)^2 * (taylorOrder x : ℝ) :=
    (le_mul_of_one_le_right (by positivity) hl).trans hscaled
  have h2 : precision (cutoffLog x)^2 ≤ precision (cutoffLog x) := by nlinarith
  have h3 := mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg (taylorOrder x) : (0 : ℝ) ≤ taylorOrder x)
  nlinarith [hr.2.2.2]

theorem eventual_taylorOrder_bounds : ∀ᶠ x : ℝ in atTop,
    100 * (factorCount x : ℝ) ≤ (taylorOrder x : ℝ) ∧
    cutoffLog x ≤ (taylorOrder x : ℝ) ∧
    99 * (factorCount x : ℝ) *
        Real.log ((rangeCount (cutoffLog x) : ℝ) * cutoffLog x) ≤
      precision (cutoffLog x) ^ 2 * (taylorOrder x : ℝ) ∧
    3 * (rangeCount (cutoffLog x) : ℝ) ≤ precision (cutoffLog x) * (taylorOrder x : ℝ) := by
  filter_upwards [cutoffLog_tendsto.eventually_ge_atTop 100,
    (Real.tendsto_log_atTop.comp cutoffLog_tendsto).eventually_ge_atTop 1] with x hell hlog
  exact taylorOrder_bounds hell hlog

theorem taylorOrder_tendsto : Tendsto (fun x : ℝ => (taylorOrder x : ℝ)) atTop atTop :=
  tendsto_atTop_mono' atTop (eventual_taylorOrder_bounds.mono (fun _ h => h.2.1)) cutoffLog_tendsto

end NField.Alignment.HarperTaylorGrowth

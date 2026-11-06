/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StationaryMellinKernel
import Mathlib.Analysis.Complex.RealDeriv

/-! # Integration by parts continues the sawtooth Mellin transform -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.StationarySawtoothMellin
open MeasureTheory Set Filter StationaryDiagonalDefinitions StationaryBernoulliPrimitive
  StationarySawtoothIntegrals StationaryMellinKernel

def sawtoothKernel (s : ℂ) (x : ℝ) : ℂ := (psi x : ℂ) * (x : ℂ) ^ (-(s + 1))
def sawtoothMellin (s : ℂ) : ℂ := ∫ x in Ioi 1, sawtoothKernel s x
def continuedSawtoothMellin (s : ℂ) : ℂ := -1 / 12 + (s + 1) * bernoulliMellin s

theorem sawtoothKernel_measurable (s : ℂ) : Measurable (sawtoothKernel s) :=
  (Complex.measurable_ofReal.comp psi_measurable).mul (Complex.measurable_ofReal.pow_const (-(s + 1)))

theorem sawtoothKernel_integrable {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (sawtoothKernel s) (Ioi 1) := by
  have he : (-(s + 1)).re < -1 := by simp; linarith
  apply ((integrableOn_Ioi_norm_cpow_of_lt he (by norm_num : (0 : ℝ) < 1)).const_mul
    (1 / 2 : ℝ)).mono' (sawtoothKernel_measurable s).aestronglyMeasurable
  apply Eventually.of_forall
  intro x
  unfold sawtoothKernel
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (psi_abs_bound x) (norm_nonneg _)

theorem firstPrimitive_cpow_boundary_tendsto {s : ℂ} (hs : -1 < s.re) :
    Tendsto (fun x : ℝ => (firstPrimitive x : ℂ) * (x : ℂ) ^ (-(s + 1))) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have ht : Tendsto (fun x : ℝ => (1 / 12 : ℝ) * x ^ (-s.re - 1)) atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop (by linarith : 0 < s.re + 1)).const_mul (1 / 12 : ℝ)
    simpa only [neg_add_rev, mul_zero, show -(1 : ℝ) + -s.re = -s.re - 1 by ring] using h
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ ht
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have he : (-(s + 1)).re = -s.re - 1 := by simp; ring
  rw [he]
  exact mul_le_mul_of_nonneg_right (firstPrimitive_abs_bound x) (by positivity)

theorem complex_psi_interval_integrable (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => (psi x : ℂ)) volume a b := by
  apply (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 / 2 : ℝ)) volume a b).mono_fun'
  · exact (Complex.measurable_ofReal.comp psi_measurable).aestronglyMeasurable
  · exact Eventually.of_forall (fun x => by simpa only [Complex.norm_real, Real.norm_eq_abs] using psi_abs_bound x)

theorem sawtooth_cpow_derivative {s : ℂ} (hs : -1 < s.re) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => (x : ℂ) ^ (-(s + 1)))
      (-(s + 1) * (x : ℂ) ^ (-(s + 2))) x := by
  have hr : -(s + 1) ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp at h'
    linarith
  have h := hasDerivAt_ofReal_cpow_const hx.ne' hr
  convert! h using 1
  congr 2
  ring

/-- Title: `The finite sawtooth Mellin integral retains its exact Bernoulli boundary`. -/
theorem sawtoothMellin_finite {s : ℂ} (hs : -1 < s.re) {b : ℝ} (hb : 1 ≤ b) :
    (∫ x in 1..b, sawtoothKernel s x) =
      (firstPrimitive b : ℂ) * (b : ℂ) ^ (-(s + 1)) - 1 / 12 +
        (s + 1) * ∫ x in 1..b, mellinKernel s x := by
  have hx0 {x : ℝ} (hx : x ∈ uIcc 1 b) : 0 < x := by
    rw [uIcc_of_le hb] at hx
    linarith [hx.1]
  have hc (r : ℂ) : ContinuousOn (fun x : ℝ => (x : ℂ) ^ r) (uIcc 1 b) :=
    fun x hx => (Complex.continuousAt_ofReal_cpow_const x r (Or.inr (hx0 hx).ne')).continuousWithinAt
  have hdcont : ContinuousOn (fun x : ℝ => -(s + 1) * (x : ℂ) ^ (-(s + 2))) (uIcc 1 b) :=
    continuousOn_const.mul (hc _)
  have hh := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right (hc (-(s + 1)))
    (Complex.continuous_ofReal.comp firstPrimitive_continuous).continuousOn
    (fun x hx => (sawtooth_cpow_derivative hs (hx0 (by
      rw [uIcc_of_le hb]
      simpa only [min_eq_left hb, max_eq_right hb] using Ioo_subset_Icc_self hx))).hasDerivWithinAt)
    (fun x _ => (firstPrimitive_right_derivative x).ofReal_comp)
    hdcont.intervalIntegrable (complex_psi_interval_integrable 1 b)
  have hl (x : ℝ) : (x : ℂ) ^ (-(s + 1)) * (psi x : ℂ) = sawtoothKernel s x := by
    unfold sawtoothKernel
    ring
  have hr (x : ℝ) : (-(s + 1) * (x : ℂ) ^ (-(s + 2))) * (firstPrimitive x : ℂ) =
      -(s + 1) * mellinKernel s x := by unfold mellinKernel; ring
  simp only [Function.comp_apply, hl, hr, intervalIntegral.integral_const_mul] at hh
  have hB : firstPrimitive 1 = 1 / 12 := by simpa using firstPrimitive_integer 1
  simp only [Complex.ofReal_one, Complex.one_cpow, one_mul, hB] at hh
  push_cast at hh
  convert hh using 1 <;> ring

/-- Title: `Integration by parts gives the continued sawtooth Mellin transform`. -/
theorem sawtoothMellin_eq_continued {s : ℂ} (hs : 0 < s.re) :
    sawtoothMellin s = continuedSawtoothMellin s := by
  have hs' : -1 < s.re := by linarith
  have hl := intervalIntegral_tendsto_integral_Ioi 1 (sawtoothKernel_integrable hs) tendsto_id
  have hm := intervalIntegral_tendsto_integral_Ioi 1 (mellinKernel_integrable hs') tendsto_id
  have hr := ((firstPrimitive_cpow_boundary_tendsto hs').sub_const (1 / 12 : ℂ)).add (hm.const_mul (s + 1))
  change Tendsto _ atTop (nhds (0 - 1 / 12 + (s + 1) * bernoulliMellin s)) at hr
  have he : (0 : ℂ) - 1 / 12 + (s + 1) * bernoulliMellin s = continuedSawtoothMellin s := by
    unfold continuedSawtoothMellin
    ring
  rw [he] at hr
  apply tendsto_nhds_unique hl
  apply hr.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with b hb
  exact (sawtoothMellin_finite hs' hb).symm

end NField.Alignment.StationarySawtoothMellin

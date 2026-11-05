/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperCenteredPath
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Gaussian tail shifts and their integrable envelope

For a nonnegative threshold, shifting a centered Gaussian tail by r>=0
costs at most exp(-r²/(2v)). Integrating this envelope will control the
overshoot uniformly when the variance is positive and at most one.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperGaussianTail
open scoped Topology
open MeasureTheory ProbabilityTheory Set

theorem gaussianPDFReal_shift_le {v : NNReal} (hv : 0 < v) {z r : ℝ}
    (hz : 0 ≤ z) (hr : 0 ≤ r) :
    gaussianPDFReal 0 v (z+r) ≤ Real.exp (-r^2/(2*v))*gaussianPDFReal 0 v z := by
  have hv0 : (0 : ℝ) < v := hv
  have he : -(z+r)^2/(2*(v : ℝ)) ≤ -r^2/(2*v)+ -z^2/(2*v) := by
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  unfold gaussianPDFReal
  simp only [sub_zero]
  calc
    _ ≤ (Real.sqrt (2*Real.pi*v))⁻¹*Real.exp (-r^2/(2*v)+ -z^2/(2*v)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by positivity)
    _ = _ := by rw [Real.exp_add]; ring

theorem gaussian_tail_shift {v : NNReal} (hv : 0 < v) {a r : ℝ}
    (ha : 0 ≤ a) (hr : 0 ≤ r) :
    (gaussianReal 0 v).real (Ioi (a+r)) ≤
      Real.exp (-r^2/(2*v))*(gaussianReal 0 v).real (Ioi a) := by
  have hvne := ne_of_gt hv
  have hmap := gaussianReal_map_sub_const (μ := 0) (v := v) r
  simp only [zero_sub] at hmap
  have hpre : (fun z : ℝ => z-r) ⁻¹' Ioi a = Ioi (a+r) := by
    ext z
    simp only [Set.mem_preimage,Set.mem_Ioi]
    constructor <;> intro h <;> linarith
  have hmass : (gaussianReal (-r) v).real (Ioi a) = (gaussianReal 0 v).real (Ioi (a+r)) := by
    have hm : Measurable (fun z : ℝ => z-r) := by fun_prop
    simp only [measureReal_def]
    rw [← hmap,Measure.map_apply hm measurableSet_Ioi,hpre]
  have hreal (m : ℝ) (s : Set ℝ) :
      (gaussianReal m v).real s = ∫ z in s, gaussianPDFReal m v z := by
    rw [measureReal_def,gaussianReal_apply_eq_integral m hvne,
      ENNReal.toReal_ofReal (integral_nonneg (gaussianPDFReal_nonneg m v))]
  rw [← hmass,hreal,hreal,← integral_const_mul]
  apply integral_mono_ae (integrable_gaussianPDFReal (-r) v).integrableOn
    ((integrable_gaussianPDFReal 0 v).integrableOn.const_mul _)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  simpa only [gaussianPDFReal_add,zero_sub] using
    gaussianPDFReal_shift_le hv (ha.trans hz.le) hr

theorem gaussian_tail_envelope_integrable {v : NNReal} (hv : 0 < v) :
    Integrable (fun r : ℝ => Real.exp (-r^2/(2*v))) := by
  have hv0 : (0 : ℝ) < v := hv
  have h := integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < 1/(2*v))
  convert h using 1
  ext r
  congr 1
  ring

theorem gaussian_tail_envelope_integral {v : NNReal} (hv : 0 < v) :
    (∫ r in Ioi (0 : ℝ), Real.exp (-r^2/(2*v))) = Real.sqrt (2*Real.pi*v)/2 := by
  have hv0 : (0 : ℝ) < v := hv
  have he (r : ℝ) : -r^2/(2*(v : ℝ)) = -(1/(2*v))*r^2 := by ring
  simp_rw [he]
  rw [integral_gaussian_Ioi]
  congr 2
  field_simp

theorem gaussian_tail_envelope_integral_le_two {v : NNReal} (hv : 0 < v)
    (hv1 : (v : ℝ) ≤ 1) : (∫ r in Ioi (0 : ℝ), Real.exp (-r^2/(2*v))) ≤ 2 := by
  rw [gaussian_tail_envelope_integral hv]
  have hp : 2*Real.pi*(v : ℝ) ≤ 8 := by
    nlinarith [Real.pi_le_four,Real.pi_pos,v.coe_nonneg]
  have hs : Real.sqrt (2*Real.pi*(v : ℝ)) ≤ 4 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num,by linarith⟩
  linarith

end NField.Alignment.HarperGaussianTail

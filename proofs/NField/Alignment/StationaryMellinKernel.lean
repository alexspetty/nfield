/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StationaryConditionalConstants
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! # The actual Mellin transform of the bounded Bernoulli primitive -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.StationaryMellinKernel
open MeasureTheory Set Filter StationaryBernoulliPrimitive

def mellinKernel (s : ℂ) (x : ℝ) : ℂ := (firstPrimitive x : ℂ) * (x : ℂ) ^ (-(s + 2))
def mellinKernelDeriv (s : ℂ) (x : ℝ) : ℂ := -(Real.log x : ℂ) * mellinKernel s x
def bernoulliMellin (s : ℂ) : ℂ := ∫ x in Ioi 1, mellinKernel s x

theorem mellinKernel_measurable (s : ℂ) : Measurable (mellinKernel s) :=
  (Complex.measurable_ofReal.comp firstPrimitive_continuous.measurable).mul
    (Complex.measurable_ofReal.pow_const (-(s + 2)))

theorem mellinKernelDeriv_measurable (s : ℂ) : Measurable (mellinKernelDeriv s) :=
  (Complex.measurable_ofReal.comp Real.measurable_log).neg.mul (mellinKernel_measurable s)

theorem mellinKernel_norm_bound (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖mellinKernel s x‖ ≤ (1 / 12 : ℝ) * x ^ (-s.re - 2) := by
  unfold mellinKernel
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have he : (-(s + 2)).re = -s.re - 2 := by simp; ring
  rw [he]
  exact mul_le_mul_of_nonneg_right (firstPrimitive_abs_bound x) (Real.rpow_nonneg hx.le _)

theorem mellinKernel_integrable {s : ℂ} (hs : -1 < s.re) : IntegrableOn (mellinKernel s) (Ioi 1) := by
  apply ((integrableOn_Ioi_rpow_of_lt (by linarith : -s.re - 2 < -1) (by norm_num : (0 : ℝ) < 1)).const_mul
    (1 / 12 : ℝ)).mono' (mellinKernel_measurable s).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact mellinKernel_norm_bound s (by have hx' : 1 < x := hx; linarith : 0 < x)

theorem mellinKernel_hasDerivAt (s : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun z : ℂ => mellinKernel z x) (mellinKernelDeriv s x) s := by
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hd := ((((hasDerivAt_id s).add_const 2).neg).const_cpow (c := (x : ℂ)) (Or.inl hxC)).const_mul
    (firstPrimitive x : ℂ)
  convert! hd using 1
  unfold mellinKernelDeriv mellinKernel
  rw [← Complex.ofReal_log hx.le]
  simp only [id_eq, Pi.neg_apply]
  ring

theorem mellinKernelDeriv_norm_bound {δ σ : ℝ} (hδ : 0 < δ) {s : ℂ} (hs : σ ≤ s.re)
    {x : ℝ} (hx : 1 ≤ x) :
    ‖mellinKernelDeriv s x‖ ≤ (1 / (12 * δ)) * x ^ (δ - σ - 2) := by
  have hx0 : 0 < x := by linarith
  have hl := Real.log_nonneg hx
  have hp : x ^ (-s.re - 2) ≤ x ^ (-σ - 2) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  unfold mellinKernelDeriv
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hl]
  calc
    _ ≤ Real.log x * ((1 / 12 : ℝ) * x ^ (-s.re - 2)) :=
      mul_le_mul_of_nonneg_left (mellinKernel_norm_bound s hx0) hl
    _ ≤ (x ^ δ / δ) * ((1 / 12 : ℝ) * x ^ (-σ - 2)) := by
      apply mul_le_mul (Real.log_le_rpow_div hx0.le hδ)
        (mul_le_mul_of_nonneg_left hp (by norm_num))
        (by positivity) (by positivity)
    _ = _ := by
      rw [show δ - σ - 2 = δ + (-σ - 2) by ring, Real.rpow_add hx0]
      ring

theorem mellinKernelDeriv_integrable {s : ℂ} (hs : -1 < s.re) :
    IntegrableOn (mellinKernelDeriv s) (Ioi 1) := by
  let δ : ℝ := (s.re + 1) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hp : δ - s.re - 2 < -1 := by dsimp [δ]; linarith
  apply ((integrableOn_Ioi_rpow_of_lt hp (by norm_num : (0 : ℝ) < 1)).const_mul
    (1 / (12 * δ))).mono' (mellinKernelDeriv_measurable s).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact mellinKernelDeriv_norm_bound hδ le_rfl hx.le

/-- Title: `The Bernoulli Mellin transform is differentiable on the full half-plane beyond minus one`. -/
theorem bernoulliMellin_hasDerivAt {s : ℂ} (hs : -1 < s.re) :
    HasDerivAt bernoulliMellin (∫ x in Ioi 1, mellinKernelDeriv s x) s := by
  let δ : ℝ := (s.re + 1) / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hσ (z : ℂ) (hz : z ∈ Metric.ball s δ) : s.re - δ ≤ z.re := by
    have habs := Complex.abs_re_le_norm (z - s)
    have hn : ‖z - s‖ < δ := by simpa only [Metric.mem_ball, dist_eq_norm] using hz
    have hh := neg_abs_le (z.re - s.re)
    rw [Complex.sub_re] at habs
    linarith
  have hbound : ∀ᵐ x ∂volume.restrict (Ioi (1 : ℝ)), ∀ z ∈ Metric.ball s δ,
      ‖mellinKernelDeriv z x‖ ≤ (1 / (12 * δ)) * x ^ (δ - (s.re - δ) - 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    intro z hz
    exact mellinKernelDeriv_norm_bound hδ (hσ z hz) hx.le
  have hpower : δ - (s.re - δ) - 2 < -1 := by dsimp [δ]; linarith
  have hi : Integrable (fun x : ℝ => (1 / (12 * δ)) * x ^ (δ - (s.re - δ) - 2))
      (volume.restrict (Ioi 1)) :=
    (integrableOn_Ioi_rpow_of_lt hpower (by norm_num : (0 : ℝ) < 1)).const_mul _
  have hd : ∀ᵐ x ∂volume.restrict (Ioi (1 : ℝ)), ∀ z ∈ Metric.ball s δ,
      HasDerivAt (fun z : ℂ => mellinKernel z x) (mellinKernelDeriv z x) z := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    intro z hz
    exact mellinKernel_hasDerivAt z (by have hx' : 1 < x := hx; linarith : 0 < x)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds s hδ)
    (Eventually.of_forall (fun z => (mellinKernel_measurable z).aestronglyMeasurable))
    (mellinKernel_integrable hs) (mellinKernelDeriv_measurable s).aestronglyMeasurable hbound hi hd).2

end NField.Alignment.StationaryMellinKernel

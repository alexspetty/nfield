/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StationaryZetaContinuation
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! # Evaluation of the logarithmic conditional sawtooth integral -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.StationarySecondCenteringConstant
open MeasureTheory Set Filter StationaryConditionalConstants StationaryMellinKernel
  StationarySawtoothMellin StationaryEulerZeta StationaryZetaContinuation

theorem mellinKernel_zero (x : ℝ) : mellinKernel 0 x = (firstKernel x : ℂ) := by
  unfold mellinKernel firstKernel
  simp only [zero_add, Complex.cpow_neg, Complex.cpow_two]
  push_cast
  rfl

theorem mellinKernel_sum_deriv_zero (x : ℝ) :
    mellinKernel 0 x + mellinKernelDeriv 0 x = -(secondKernel x : ℂ) := by
  unfold mellinKernelDeriv
  rw [mellinKernel_zero]
  unfold firstKernel secondKernel
  push_cast
  ring

theorem mellin_value_add_deriv_zero :
    bernoulliMellin 0 + deriv bernoulliMellin 0 = -(integralOne : ℂ) := by
  rw [(bernoulliMellin_hasDerivAt (by norm_num : -1 < (0 : ℂ).re)).deriv]
  unfold bernoulliMellin
  rw [← integral_add (mellinKernel_integrable (by norm_num : -1 < (0 : ℂ).re))
    (mellinKernelDeriv_integrable (by norm_num : -1 < (0 : ℂ).re))]
  simp_rw [mellinKernel_sum_deriv_zero]
  rw [integral_neg, integral_complex_ofReal]
  rfl

def eulerDerivative (s : ℂ) : ℂ := -1 / (s - 1) ^ 2 + 1 / 12 -
  (2 * s + 1) * bernoulliMellin s - s * (s + 1) * deriv bernoulliMellin s

theorem eulerZeta_hasDerivAt {s : ℂ} (hs : -1 < s.re) (hs1 : s ≠ 1) :
    HasDerivAt eulerZeta (eulerDerivative s) s := by
  have hM := (bernoulliMellin_hasDerivAt hs).differentiableAt.hasDerivAt
  have hC := (hasDerivAt_const s (-1 / 12 : ℂ)).add
    (((hasDerivAt_id s).add_const 1).mul hM)
  have hE := (((hasDerivAt_const s (1 : ℂ)).div ((hasDerivAt_id s).sub_const 1)
    (sub_ne_zero.mpr hs1)).add_const (1 / 2)).sub ((hasDerivAt_id s).mul hC)
  convert! hE using 1
  unfold eulerDerivative
  simp only [id_eq, Pi.add_apply, Pi.mul_apply]
  ring

theorem mellin_deriv_differentiableAt_zero : DifferentiableAt ℂ (deriv bernoulliMellin) 0 := by
  have hd : DifferentiableOn ℂ bernoulliMellin {s : ℂ | -1 < s.re} :=
    fun s hs => (bernoulliMellin_hasDerivAt hs).differentiableAt.differentiableWithinAt
  exact ((hd.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re))
    0 (by norm_num)).deriv.differentiableAt

theorem eulerDerivative_hasDerivAt_zero :
    HasDerivAt eulerDerivative (-2 - 2 * bernoulliMellin 0 - 2 * deriv bernoulliMellin 0) 0 := by
  have hM := (bernoulliMellin_hasDerivAt (by norm_num : -1 < (0 : ℂ).re)).differentiableAt.hasDerivAt
  have hM' := mellin_deriv_differentiableAt_zero.hasDerivAt
  have hR := ((hasDerivAt_const (0 : ℂ) (-1 : ℂ)).div
    (((hasDerivAt_id (0 : ℂ)).sub_const 1).pow 2) (by norm_num)).add_const (1 / 12)
  have hP := (((hasDerivAt_id (0 : ℂ)).const_mul 2).add_const 1).mul hM
  have hQ := ((hasDerivAt_id (0 : ℂ)).mul ((hasDerivAt_id (0 : ℂ)).add_const 1)).mul hM'
  convert! (hR.sub hP).sub hQ using 1 <;> norm_num <;> ring

theorem second_zeta_derivative_zero :
    iteratedDeriv 2 riemannZeta 0 = -2 + 2 * (integralOne : ℂ) := by
  have he : deriv eulerZeta =ᶠ[nhds 0] eulerDerivative := by
    filter_upwards [centralStrip_open.mem_nhds
      (show (0 : ℂ) ∈ centralStrip by norm_num [centralStrip])] with s hs
    have hn : s ≠ 1 := by intro h; have hh := hs.2; simp [h] at hh
    exact (eulerZeta_hasDerivAt hs.1 hn).deriv
  have h1 := eulerZeta_eventually_eq_riemannZeta.deriv.deriv_eq
  have h2 := he.deriv_eq
  have h3 := eulerDerivative_hasDerivAt_zero.deriv
  have h4 := mellin_value_add_deriv_zero
  rw [iteratedDeriv_succ, iteratedDeriv_one, ← h1, h2, h3]
  linear_combination -2 * h4

/-- Title: `The logarithmic conditional integral equals one plus half the second zeta derivative`. -/
theorem integralOne_eq_zeta_second_derivative :
    (integralOne : ℂ) = 1 + iteratedDeriv 2 riemannZeta 0 / 2 := by
  rw [second_zeta_derivative_zero]
  ring

end NField.Alignment.StationarySecondCenteringConstant

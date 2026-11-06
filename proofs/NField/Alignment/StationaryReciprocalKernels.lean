/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StationaryRatioKernel

/-! # The two absolutely integrable kernels controlling conditional sawtooth tails -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.StationaryReciprocalKernels
open Filter MeasureTheory Set CollisionLogTailKernel

def inverseSquare (x : ℝ) : ℝ := 1 / x ^ 2
def logarithmicSquare (x : ℝ) : ℝ := (1 + Real.log x) / x ^ 2

theorem inverseSquare_nonneg (x : ℝ) : 0 ≤ inverseSquare x := by unfold inverseSquare; positivity

theorem negative_inverse_hasDerivAt {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun x : ℝ => -(1 / x)) (inverseSquare x) x := by
  have hd := ((hasDerivAt_id x).inv hx).neg
  convert! hd using 1
  · funext y
    simp only [one_div, Pi.neg_apply, Pi.inv_apply, id_eq]
  · simp only [inverseSquare, id_eq]
    ring

theorem inverseSquare_integrable {a : ℝ} (ha : 0 < a) : IntegrableOn inverseSquare (Ioi a) := by
  have ht : Tendsto (fun x : ℝ => -(1 / x)) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.div_atTop tendsto_id : Tendsto (fun x : ℝ => 1 / x) atTop (nhds 0)).neg
  exact integrableOn_Ioi_deriv_of_nonneg' (fun _ hx => negative_inverse_hasDerivAt (ne_of_gt (ha.trans_le hx)))
    (fun x _ => inverseSquare_nonneg x) ht

theorem inverseSquare_integral {a : ℝ} (ha : 0 < a) :
    (∫ x in Ioi a, inverseSquare x) = 1 / a := by
  have ht : Tendsto (fun x : ℝ => -(1 / x)) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.div_atTop tendsto_id : Tendsto (fun x : ℝ => 1 / x) atTop (nhds 0)).neg
  have hh := integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun _ hx => negative_inverse_hasDerivAt (ne_of_gt (ha.trans_le hx)))
    (fun x _ => inverseSquare_nonneg x) ht
  simpa only [zero_sub, neg_neg] using hh

theorem logarithmicSquare_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ logarithmicSquare x := by
  unfold logarithmicSquare
  exact div_nonneg (by linarith [Real.log_nonneg hx]) (sq_nonneg x)

theorem logarithmic_primitive_hasDerivAt {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun x : ℝ => -(Real.log x + 2) / x) (logarithmicSquare x) x := by
  have hd := (((Real.hasDerivAt_log hx).add_const 2).neg).div (hasDerivAt_id x) hx
  convert! hd using 1
  simp only [logarithmicSquare, id_eq, Pi.neg_apply]
  field_simp
  ring

theorem logarithmic_primitive_tendsto :
    Tendsto (fun x : ℝ => -(Real.log x + 2) / x) atTop (nhds 0) := by
  have ht := ((logPower_div_linear_tendsto 1).add
    (tendsto_const_nhds.div_atTop tendsto_id : Tendsto (fun x : ℝ => 2 / x) atTop (nhds 0))).neg
  norm_num only [zero_add, neg_zero] at ht
  convert! ht using 1
  funext x
  simp only [pow_one]
  ring

theorem logarithmicSquare_integrable {a : ℝ} (ha : 1 ≤ a) : IntegrableOn logarithmicSquare (Ioi a) :=
  integrableOn_Ioi_deriv_of_nonneg'
    (fun x hx => logarithmic_primitive_hasDerivAt (x := x) (by have hx' : a ≤ x := hx; linarith))
    (fun _ hx => logarithmicSquare_nonneg (ha.trans hx.le)) logarithmic_primitive_tendsto

/-- Title: `The logarithmic reciprocal-square tail has its exact inverse-linear integral`. -/
theorem logarithmicSquare_integral {a : ℝ} (ha : 1 ≤ a) :
    (∫ x in Ioi a, logarithmicSquare x) = (Real.log a + 2) / a := by
  have hh := integral_Ioi_of_hasDerivAt_of_nonneg' (a := a)
    (fun x hx => logarithmic_primitive_hasDerivAt (x := x) (by have hx' : a ≤ x := hx; linarith))
    (fun _ hx => logarithmicSquare_nonneg (ha.trans hx.le)) logarithmic_primitive_tendsto
  simpa only [zero_sub, neg_div, neg_neg] using hh

end NField.Alignment.StationaryReciprocalKernels

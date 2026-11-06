/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StationaryBoundaryKernel

/-! # A second exact Bernoulli integration gives the inverse-square boundary error -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.StationaryBernoulliBoundaryRemainder
open MeasureTheory Set Filter StationaryBernoulliPrimitive StationaryBoundaryKernel

theorem boundaryKernel_secondPrimitive_tendsto (A C : ℝ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x => boundaryKernel A C a x * secondPrimitive x) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hh := (boundaryKernel_tendsto A C ha).norm
  simp only [norm_zero] at hh
  apply squeeze_zero' (Eventually.of_forall (fun x => norm_nonneg _)) _ hh
  exact Eventually.of_forall (fun x => by
    simp only [norm_mul, Real.norm_eq_abs]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (secondPrimitive_abs_bound x)
      (abs_nonneg (boundaryKernel A C a x)))

theorem boundaryKernel_finite_integrationByParts (A C : ℝ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in a..b, firstPrimitive x * boundaryKernel A C a x) =
      boundaryKernel A C a b * secondPrimitive b - boundaryKernel A C a a * secondPrimitive a -
        ∫ x in a..b, boundaryKernelDeriv A C a x * secondPrimitive x := by
  have hpos {x : ℝ} (hx : x ∈ uIcc a b) : 0 < x := by
    rw [uIcc_of_le hab] at hx
    exact ha.trans_le hx.1
  have hc : ContinuousOn (boundaryKernel A C a) (uIcc a b) :=
    fun x hx => (boundaryKernel_hasDerivAt A C ha (hpos hx)).continuousAt.continuousWithinAt
  have hl : ContinuousOn (fun x : ℝ => Real.log (x / a)) (uIcc a b) :=
    (continuousOn_id.div_const a).log (fun x hx => div_ne_zero (hpos hx).ne' ha.ne')
  have hdc : ContinuousOn (boundaryKernelDeriv A C a) (uIcc a b) :=
    (continuousOn_const.add (continuousOn_const.mul hl)).div (continuousOn_id.pow 3)
      (fun x hx => pow_ne_zero 3 (hpos hx).ne')
  have hh := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right hc
    secondPrimitive_continuous.continuousOn
    (fun x hx => (boundaryKernel_hasDerivAt A C ha (hpos (by
      rw [uIcc_of_le hab]
      simpa only [min_eq_left hab, max_eq_right hab] using Ioo_subset_Icc_self hx))).hasDerivWithinAt)
    (fun x hx => secondPrimitive_right_derivative x)
    hdc.intervalIntegrable (firstPrimitive_continuous.intervalIntegrable a b)
  have he (x : ℝ) : boundaryKernel A C a x * firstPrimitive x =
      firstPrimitive x * boundaryKernel A C a x := mul_comm _ _
  simpa only [he] using hh

/-- Title: `The second Bernoulli primitive gives the exact improper boundary remainder`. -/
theorem boundaryRemainder_integrationByParts (A C : ℝ) {a : ℝ} (ha : 1 ≤ a) :
    boundaryRemainder A C a = -boundaryKernel A C a a * secondPrimitive a -
      ∫ x in Ioi a, boundaryKernelDeriv A C a x * secondPrimitive x := by
  have ha0 : 0 < a := by linarith
  have hl := intervalIntegral_tendsto_integral_Ioi a (firstPrimitive_boundaryKernel_integrable A C ha) tendsto_id
  have hd := intervalIntegral_tendsto_integral_Ioi a
    (secondPrimitive_boundaryKernelDeriv_integrable A C ha0) tendsto_id
  have hr := ((boundaryKernel_secondPrimitive_tendsto A C ha0).sub_const
    (boundaryKernel A C a a * secondPrimitive a)).sub hd
  have he : (0 : ℝ) - boundaryKernel A C a a * secondPrimitive a -
      (∫ x in Ioi a, boundaryKernelDeriv A C a x * secondPrimitive x) =
      -boundaryKernel A C a a * secondPrimitive a -
        ∫ x in Ioi a, boundaryKernelDeriv A C a x * secondPrimitive x := by ring
  rw [he] at hr
  apply tendsto_nhds_unique hl
  apply hr.congr'
  filter_upwards [eventually_ge_atTop a] with b hb
  exact (boundaryKernel_finite_integrationByParts A C ha0 hb).symm

/-- Title: `The Bernoulli boundary remainder has an explicit inverse-square bound`. -/
theorem boundaryRemainder_bound (A C : ℝ) {a : ℝ} (ha : 1 ≤ a) :
    |boundaryRemainder A C a| ≤ (2 * |C| + 3 * |A|) / a ^ 2 := by
  have ha0 : 0 < a := by linarith
  have hb : |boundaryKernel A C a a * secondPrimitive a| ≤ (|C| + |A|) / a ^ 2 := by
    rw [abs_mul]
    calc
      _ ≤ |boundaryKernel A C a a| * 1 :=
        mul_le_mul_of_nonneg_left (secondPrimitive_abs_bound a) (abs_nonneg _)
      _ = |C + A| / a ^ 2 := by
        simp only [boundaryKernel, div_self ha0.ne', Real.log_one, mul_zero, sub_zero,
          abs_div, abs_of_nonneg (sq_nonneg a), mul_one]
      _ ≤ _ := div_le_div_of_nonneg_right (abs_add_le C A) (sq_nonneg a)
  rw [boundaryRemainder_integrationByParts A C ha]
  calc
    _ ≤ |-boundaryKernel A C a a * secondPrimitive a| +
        |∫ x in Ioi a, boundaryKernelDeriv A C a x * secondPrimitive x| := abs_sub _ _
    _ ≤ (|C| + |A|) / a ^ 2 + (|C| + 2 * |A|) / a ^ 2 :=
      add_le_add (by simpa only [neg_mul, abs_neg] using hb) (boundaryDerivative_integral_bound A C ha0)
    _ = _ := by ring

end NField.Alignment.StationaryBernoulliBoundaryRemainder

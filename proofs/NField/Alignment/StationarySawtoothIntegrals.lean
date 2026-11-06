/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StationaryBernoulliPrimitive

/-! # Exact finite integration by parts for the two conditionally convergent source integrals -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.StationarySawtoothIntegrals
open MeasureTheory Set StationaryDiagonalDefinitions StationaryBernoulliPrimitive

theorem weighted_psi_integral {g g' : ℝ → ℝ} {a b : ℝ}
    (hg : ContinuousOn g (uIcc a b))
    (hd : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt g (g' x) (Ioi x) x)
    (hi : IntervalIntegrable g' volume a b) :
    (∫ x in a..b, g x * psi x) =
      g b * firstPrimitive b - g a * firstPrimitive a - ∫ x in a..b, g' x * firstPrimitive x :=
  intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right hg
    firstPrimitive_continuous.continuousOn hd (fun x _ => firstPrimitive_right_derivative x)
    hi (psi_interval_integrable a b)

theorem inverse_hasDerivAt {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun x : ℝ => 1 / x) (-1 / x ^ 2) x := by
  have hd := (hasDerivAt_id x).inv hx
  convert! hd using 1
  funext y
  simp only [one_div, Pi.inv_apply, id_eq]

theorem log_div_hasDerivAt {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun x : ℝ => Real.log x / x) ((1 - Real.log x) / x ^ 2) x := by
  have hd := (Real.hasDerivAt_log hx).div (hasDerivAt_id x) hx
  convert! hd using 1
  simp only [id_eq]
  field_simp

theorem positive_interval_ne_zero {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {x : ℝ} (hx : x ∈ uIcc a b) : x ≠ 0 := by
  rw [uIcc_of_le hab] at hx
  exact ne_of_gt (ha.trans_le hx.1)

/-- Title: `The reciprocal sawtooth integral has its exact Bernoulli boundary term`. -/
theorem reciprocal_psi_integral {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in a..b, psi x / x) = firstPrimitive b / b - firstPrimitive a / a +
      ∫ x in a..b, firstPrimitive x / x ^ 2 := by
  have hne : ∀ {x : ℝ}, x ∈ uIcc a b → x ≠ 0 := fun hx => positive_interval_ne_zero ha hab hx
  have hc : ContinuousOn (fun x : ℝ => 1 / x) (uIcc a b) :=
    continuousOn_const.div continuousOn_id (fun x hx => hne hx)
  have hdc : ContinuousOn (fun x : ℝ => -1 / x ^ 2) (uIcc a b) :=
    continuousOn_const.div (continuousOn_id.pow 2) (fun x hx => pow_ne_zero 2 (hne hx))
  have hh := weighted_psi_integral hc (fun x hx => (inverse_hasDerivAt (hne (by
    rw [uIcc_of_le hab]
    simpa only [min_eq_left hab, max_eq_right hab] using Ioo_subset_Icc_self hx))).hasDerivWithinAt)
    hdc.intervalIntegrable
  have hleft (x : ℝ) : (1 / x) * psi x = psi x / x := by ring
  have hright (x : ℝ) : (-1 / x ^ 2) * firstPrimitive x = -(firstPrimitive x / x ^ 2) := by ring
  simp_rw [hleft, hright, intervalIntegral.integral_neg] at hh
  convert hh using 1 <;> ring

/-- Title: `The logarithmic sawtooth integral has its exact Bernoulli boundary term`. -/
theorem logarithmic_psi_integral {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in a..b, psi x * Real.log x / x) =
      firstPrimitive b * Real.log b / b - firstPrimitive a * Real.log a / a +
        ∫ x in a..b, firstPrimitive x * (Real.log x - 1) / x ^ 2 := by
  have hne : ∀ {x : ℝ}, x ∈ uIcc a b → x ≠ 0 := fun hx => positive_interval_ne_zero ha hab hx
  have hlog : ContinuousOn Real.log (uIcc a b) := continuousOn_id.log (fun x hx => hne hx)
  have hc : ContinuousOn (fun x : ℝ => Real.log x / x) (uIcc a b) :=
    hlog.div continuousOn_id (fun x hx => hne hx)
  have hdc : ContinuousOn (fun x : ℝ => (1 - Real.log x) / x ^ 2) (uIcc a b) :=
    (continuousOn_const.sub hlog).div (continuousOn_id.pow 2) (fun x hx => pow_ne_zero 2 (hne hx))
  have hh := weighted_psi_integral hc (fun x hx => (log_div_hasDerivAt (hne (by
    rw [uIcc_of_le hab]
    simpa only [min_eq_left hab, max_eq_right hab] using Ioo_subset_Icc_self hx))).hasDerivWithinAt)
    hdc.intervalIntegrable
  have hleft (x : ℝ) : (Real.log x / x) * psi x = psi x * Real.log x / x := by ring
  have hright (x : ℝ) : ((1 - Real.log x) / x ^ 2) * firstPrimitive x =
      -(firstPrimitive x * (Real.log x - 1) / x ^ 2) := by ring
  simp_rw [hleft, hright, intervalIntegral.integral_neg] at hh
  convert hh using 1 <;> ring

end NField.Alignment.StationarySawtoothIntegrals

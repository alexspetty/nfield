/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimePeriodicCounting
import Mathlib.NumberTheory.Chebyshev
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # The logarithmic integral normalization used in the centered-prime proof -/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.PrimePeriodicLimits

open Filter Asymptotics MeasureTheory
open scoped Topology
open NField.External.ProgressionPNT

def logarithmicIntegral (x : ℝ) : ℝ := ∫ t in (2 : ℝ)..x, 1 / Real.log t

theorem intervalIntegrable_one_div_log {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    IntervalIntegrable (fun t => 1 / Real.log t) volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  have ht1 : 1 < t := by rcases Set.mem_uIcc.mp ht with ht | ht <;> linarith
  exact (continuousAt_const.div (Real.continuousAt_log (by linarith))
    (Real.log_pos ht1).ne').continuousWithinAt

theorem logarithmicIntegral_identity {x : ℝ} (hx : 2 ≤ x) :
    logarithmicIntegral x = x / Real.log x - 2 / Real.log 2 +
      ∫ t in (2 : ℝ)..x, 1 / (Real.log t) ^ 2 := by
  have h1 := intervalIntegrable_one_div_log (by norm_num : (1 : ℝ) < 2) (by linarith : 1 < x)
  have h2 := Chebyshev.intervalIntegrable_one_div_log_sq
    (by norm_num : (1 : ℝ) < 2) (by linarith : 1 < x)
  have hd (t : ℝ) (ht : t ∈ Set.uIcc (2 : ℝ) x) :
      HasDerivAt (fun u : ℝ => u / Real.log u)
        (1 / Real.log t - 1 / (Real.log t) ^ 2) t := by
    have ht2 : 2 ≤ t := (Set.uIcc_of_le hx ▸ ht).1
    have ht0 : t ≠ 0 := by linarith
    have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith)).ne'
    apply ((hasDerivAt_id t).div (Real.hasDerivAt_log ht0) hl).congr_deriv
    simp only [id_eq]
    field_simp
    <;> ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (h1.sub h2)
  rw [intervalIntegral.integral_sub h1 h2] at h
  exact eq_add_of_sub_eq h

/-- Title: `The logarithmic integral has its classical leading term`.
The remainder estimate reuses Mathlib's reciprocal-logarithm integral bound. -/
theorem logarithmicIntegral_normalized_tendsto :
    Tendsto (fun x : ℝ => logarithmicIntegral x / (x / Real.log x)) atTop (𝓝 1) := by
  have hsmall : (fun x : ℝ => x / (Real.log x) ^ 2) =o[atTop]
      (fun x => x / Real.log x) := by
    apply (isLittleO_iff_tendsto' (by simp)).mpr
    apply Real.tendsto_log_atTop.inv_tendsto_atTop.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    change (Real.log x)⁻¹ = (x / (Real.log x)^2) / (x / Real.log x)
    field_simp
  have htail := (Chebyshev.integral_one_div_log_sq_isBigO.trans_isLittleO hsmall).tendsto_div_nhds_zero
  have hconst := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.const_mul (2 / Real.log 2)
  have h := ((show Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) from
    tendsto_const_nhds).sub hconst).add htail
  simp only [mul_zero, sub_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  rw [logarithmicIntegral_identity hx]
  have hx0 : x ≠ 0 := by linarith
  have hl : Real.log x ≠ 0 := (Real.log_pos (by linarith)).ne'
  simp only [id_eq]
  field_simp
  <;> ring

/-- Title: `Prime progression counts have the logarithmic integral asymptotic`. -/
theorem prime_progression_logarithmic_integral_limit {q : ℕ} [NeZero q]
    (a : (ZMod q)ˣ) :
    Tendsto (fun x : ℝ => primeAPCountingReal q (a : ZMod q).val x / logarithmicIntegral x)
      atTop (𝓝 (q.totient : ℝ)⁻¹) := by
  have h := (unit_class_prime_density a).div logarithmicIntegral_normalized_tendsto
    (one_ne_zero : (1 : ℝ) ≠ 0)
  simp only [div_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  exact div_div_div_cancel_right₀ (ne_of_gt (div_pos (by linarith) (Real.log_pos hx))) _ _

end NField.Alignment.PrimePeriodicLimits

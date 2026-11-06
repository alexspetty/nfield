/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StationaryCenteringDefinitions

/-! # The explicit centering error in the truncated reciprocal integral -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.StationaryCenteringTail
open MeasureTheory Set StationaryDiagonalDefinitions StationaryBernoulliPrimitive
  StationarySawtoothIntegrals StationaryConditionalConstants StationaryWeightConstants
  StationaryCenteringDefinitions

def truncatedCentering (n a : ℝ) : ℝ := (2 / 3 : ℝ) *
  ∫ u in 1..a, ((alpha * Real.log n + beta - alpha * Real.log u) / u) * psi u

def centeringErrorConstant : ℝ := (2 * |alpha| + |beta|) / 9

theorem reciprocal_psi_interval_integrable {a : ℝ} (ha : 1 ≤ a) :
    IntervalIntegrable (fun x : ℝ => psi x / x) volume 1 a := by
  have hc : ContinuousOn (fun x : ℝ => 1 / x) (uIcc 1 a) :=
    continuousOn_const.div continuousOn_id (fun x hx => positive_interval_ne_zero (by norm_num) ha hx)
  simpa only [div_eq_mul_inv, one_mul] using (psi_interval_integrable 1 a).mul_continuousOn hc

theorem logarithmic_psi_interval_integrable {a : ℝ} (ha : 1 ≤ a) :
    IntervalIntegrable (fun x : ℝ => psi x * Real.log x / x) volume 1 a := by
  have hne : ∀ {x : ℝ}, x ∈ uIcc 1 a → x ≠ 0 :=
    fun hx => positive_interval_ne_zero (by norm_num) ha hx
  have hc : ContinuousOn (fun x : ℝ => Real.log x / x) (uIcc 1 a) :=
    (continuousOn_id.log (fun x hx => hne hx)).div continuousOn_id (fun x hx => hne hx)
  simpa only [div_eq_mul_inv, mul_assoc] using (psi_interval_integrable 1 a).mul_continuousOn hc

theorem truncatedCentering_split (n : ℝ) {a : ℝ} (ha : 1 ≤ a) :
    truncatedCentering n a = (2 / 3 : ℝ) *
      ((alpha * Real.log n + beta) * (∫ u in 1..a, psi u / u) -
        alpha * ∫ u in 1..a, psi u * Real.log u / u) := by
  unfold truncatedCentering
  have he (u : ℝ) : ((alpha * Real.log n + beta - alpha * Real.log u) / u) * psi u =
      (alpha * Real.log n + beta) * (psi u / u) - alpha * (psi u * Real.log u / u) := by ring
  simp_rw [he]
  rw [intervalIntegral.integral_sub ((reciprocal_psi_interval_integrable ha).const_mul _)
      ((logarithmic_psi_interval_integrable ha).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

theorem truncatedCentering_error (n : ℝ) {a : ℝ} (ha : 1 ≤ a) :
    |truncatedCentering n a - (biasCoefficient * Real.log n + biasConstant)| ≤
      (2 / 3 : ℝ) * (|alpha * Real.log n + beta| / (6 * a) +
        |alpha| * (1 + Real.log a) / (6 * a)) := by
  rw [truncatedCentering_split n ha, ← centering_combination n]
  have he : (2 / 3 : ℝ) * ((alpha * Real.log n + beta) * (∫ u in 1..a, psi u / u) -
      alpha * (∫ u in 1..a, psi u * Real.log u / u)) -
      (2 / 3 : ℝ) * ((alpha * Real.log n + beta) * integralZero - alpha * integralOne) =
      (2 / 3 : ℝ) * ((alpha * Real.log n + beta) * ((∫ u in 1..a, psi u / u) - integralZero) -
        alpha * ((∫ u in 1..a, psi u * Real.log u / u) - integralOne)) := by ring
  rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2 / 3)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    _ ≤ |(alpha * Real.log n + beta) * ((∫ u in 1..a, psi u / u) - integralZero)| +
        |alpha * ((∫ u in 1..a, psi u * Real.log u / u) - integralOne)| := abs_sub _ _
    _ ≤ |alpha * Real.log n + beta| * (1 / (6 * a)) +
        |alpha| * ((1 + Real.log a) / (6 * a)) := by
      simp only [abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left
        (by simpa only [abs_sub_comm] using integralZero_tail_bound ha) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left
          (by simpa only [abs_sub_comm] using integralOne_tail_bound ha) (abs_nonneg _))
    _ = _ := by ring

/-- Title: `Truncating the centering integral has a uniform logarithmic inverse-linear error`. -/
theorem truncatedCentering_uniform_error {n a : ℝ} (ha : 1 ≤ a) (han : a ≤ n) :
    |truncatedCentering n a - (biasCoefficient * Real.log n + biasConstant)| ≤
      centeringErrorConstant * (1 + Real.log n) / a := by
  have ha0 : 0 < a := by linarith
  have hn : 1 ≤ n := ha.trans han
  have hln := Real.log_nonneg hn
  have hla : Real.log a ≤ Real.log n := Real.log_le_log ha0 han
  have habs : |alpha * Real.log n + beta| ≤ |alpha| * Real.log n + |beta| := by
    simpa only [abs_mul, abs_of_nonneg hln] using abs_add_le (alpha * Real.log n) beta
  have hs : |alpha * Real.log n + beta| + |alpha| * (1 + Real.log a) ≤
      (2 * |alpha| + |beta|) * (1 + Real.log n) := by
    nlinarith [abs_nonneg alpha, abs_nonneg beta, mul_nonneg (abs_nonneg beta) hln,
      mul_le_mul_of_nonneg_left hla (abs_nonneg alpha)]
  calc
    _ ≤ (2 / 3 : ℝ) * (|alpha * Real.log n + beta| / (6 * a) +
        |alpha| * (1 + Real.log a) / (6 * a)) := truncatedCentering_error n ha
    _ = (|alpha * Real.log n + beta| + |alpha| * (1 + Real.log a)) / (9 * a) := by ring
    _ ≤ ((2 * |alpha| + |beta|) * (1 + Real.log n)) / (9 * a) :=
      div_le_div_of_nonneg_right hs (by positivity)
    _ = _ := by unfold centeringErrorConstant; ring

end NField.Alignment.StationaryCenteringTail

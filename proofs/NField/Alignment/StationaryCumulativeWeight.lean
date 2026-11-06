/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StationaryMainTail

/-! # The precise cumulative-weight asymptotic with its actual constant term -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.StationaryCumulativeWeight
open StationaryDiagonalDefinitions StationaryWeightConstants StationaryFiniteCumulative
  StationaryMainTail

def weightErrorConstant : ℝ := 4 * (6 + 10 * mainTailConstant)

theorem weightErrorConstant_pos : 0 < weightErrorConstant := by
  unfold weightErrorConstant
  linarith [mainTailConstant_ge_one]

theorem cumulative_weight_error_one_add_log {t : ℝ} (ht : 1 ≤ t) :
    |cumulativeWeight t - cumulativeMain t| ≤
      (6 + 10 * mainTailConstant) * (1 + Real.log t) ^ 2 / t := by
  have ht0 : 0 < t := by linarith
  have hl := Real.log_nonneg ht
  have hs : 1 ≤ (1 + Real.log t) ^ 2 := by nlinarith [sq_nonneg (Real.log t)]
  have hc : 0 ≤ 10 * mainTailConstant := by linarith [mainTailConstant_ge_one]
  calc
    _ ≤ |cumulativeWeight t - finiteMain t| + |finiteMain t - cumulativeMain t| := abs_sub_le _ _ _
    _ ≤ 6 * (1 + Real.log t) ^ 2 / t + 10 * mainTailConstant / t := by
      exact add_le_add (cumulative_finite_main_error ht)
        (by simpa only [abs_sub_comm] using main_tail_bound ht)
    _ ≤ 6 * (1 + Real.log t) ^ 2 / t +
        (10 * mainTailConstant) * (1 + Real.log t) ^ 2 / t := by
      exact add_le_add (le_refl _) (div_le_div_of_nonneg_right
        (le_mul_of_one_le_right hc hs) ht0.le)
    _ = _ := by ring

theorem one_add_log_le_two_log_two_mul {t : ℝ} (ht : 1 ≤ t) :
    1 + Real.log t ≤ 2 * Real.log (2 * t) := by
  have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  rw [Real.log_mul (by norm_num) (by linarith : t ≠ 0)]
  linarith [Real.log_nonneg ht]

/-- Title: `Precise cumulative weight with its Möbius constant term`. -/
theorem precise_cumulative_weight {t : ℝ} (ht : 2 ≤ t) :
    |cumulativeWeight t -
      (alpha * Real.log t ^ 2 / 2 + beta * Real.log t + constantWeight)| ≤
      weightErrorConstant * Real.log (2 * t) ^ 2 / t := by
  have ht1 : 1 ≤ t := by linarith
  have hc : 0 ≤ 6 + 10 * mainTailConstant := by linarith [mainTailConstant_ge_one]
  have hl := Real.log_nonneg ht1
  have hp : (1 + Real.log t) ^ 2 ≤ (2 * Real.log (2 * t)) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (one_add_log_le_two_log_two_mul ht1) 2
  calc
    _ ≤ (6 + 10 * mainTailConstant) * (1 + Real.log t) ^ 2 / t :=
      cumulative_weight_error_one_add_log ht1
    _ ≤ (6 + 10 * mainTailConstant) * (2 * Real.log (2 * t)) ^ 2 / t := by gcongr
    _ = _ := by unfold weightErrorConstant; ring

/-- Title: `A uniform absolute constant controls the real-cutoff weight remainder`. -/
theorem exists_precise_cumulative_weight_constant : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 2 ≤ t →
    |cumulativeWeight t -
      (alpha * Real.log t ^ 2 / 2 + beta * Real.log t + constantWeight)| ≤
      C * Real.log (2 * t) ^ 2 / t :=
  ⟨weightErrorConstant, weightErrorConstant_pos, fun _ ht => precise_cumulative_weight ht⟩

end NField.Alignment.StationaryCumulativeWeight

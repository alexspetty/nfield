/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StationaryBernoulliBoundaryRemainder
import NField.Alignment.StationaryCenteringTail
import NField.Alignment.StationaryCumulativeWeight

/-! # The signed Bernoulli endpoint of the centered smooth tail -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.StationaryCenteredBoundary
open StationaryBernoulliPrimitive StationaryBoundaryKernel StationaryBernoulliBoundaryRemainder
  StationaryCenteringDefinitions StationaryCenteringTail StationaryConditionalConstants
  StationaryWeightConstants StationaryCumulativeWeight

def boundaryCoefficient (n a : ℝ) : ℝ := alpha * Real.log n + beta - alpha * Real.log a
def smoothBoundary (n a : ℝ) : ℝ := (2 / 3 : ℝ) * boundaryCoefficient n a * firstPrimitive a / a
def sourceBoundary (M n : ℕ) : ℝ := (alpha * Real.log M + beta) * M / (3 * (n : ℝ)) *
  (Int.fract ((n : ℝ) / M) ^ 2 - Int.fract ((n : ℝ) / M) + 1 / 6)
def boundaryErrorConstant : ℝ := (4 / 3 : ℝ) * (3 * |alpha| + 2 * |beta|)

/-- Title: `The centered smooth tail retains the exact signed Bernoulli boundary`. -/
theorem truncatedCentering_boundary_identity (n : ℝ) {a : ℝ} (ha : 1 ≤ a) :
    truncatedCentering n a - (biasCoefficient * Real.log n + biasConstant) - smoothBoundary n a =
      -(2 / 3 : ℝ) * boundaryRemainder alpha (boundaryCoefficient n a) a := by
  have h0 := integralZero_remainder ha
  have h1 := integralOne_remainder ha
  rw [truncatedCentering_split n ha, ← centering_combination n,
    boundaryRemainder_split alpha (boundaryCoefficient n a) ha]
  unfold smoothBoundary boundaryCoefficient
  linear_combination -(2 / 3 : ℝ) * (alpha * Real.log n + beta) * h0 + (2 / 3 : ℝ) * alpha * h1

theorem truncatedCentering_boundary_error (n : ℝ) {a : ℝ} (ha : 1 ≤ a) :
    |truncatedCentering n a - (biasCoefficient * Real.log n + biasConstant) - smoothBoundary n a| ≤
      (2 / 3 : ℝ) * (2 * |boundaryCoefficient n a| + 3 * |alpha|) / a ^ 2 := by
  rw [truncatedCentering_boundary_identity n ha, abs_mul]
  norm_num only [abs_neg, abs_div]
  simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left
    (boundaryRemainder_bound alpha (boundaryCoefficient n a) ha) (by norm_num : (0 : ℝ) ≤ 2 / 3)

theorem boundaryCoefficient_at_ratio {M n : ℕ} (hM : 0 < M) (hn : 0 < n) :
    boundaryCoefficient n ((n : ℝ) / M) = alpha * Real.log M + beta := by
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold boundaryCoefficient
  rw [Real.log_div hnR hMR]
  ring

/-- Title: `The Bernoulli boundary has exactly the manuscript's sign and normalization`. -/
theorem smoothBoundary_eq_sourceBoundary {M n : ℕ} (hM : 0 < M) (hn : 0 < n) :
    smoothBoundary n ((n : ℝ) / M) = sourceBoundary M n := by
  unfold smoothBoundary
  rw [boundaryCoefficient_at_ratio hM hn]
  unfold sourceBoundary firstPrimitive
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

theorem boundaryCoefficient_log_bound {M : ℕ} (hM : 1 ≤ M) :
    (2 / 3 : ℝ) * (2 * |alpha * Real.log M + beta| + 3 * |alpha|) ≤
      boundaryErrorConstant * Real.log (2 * (M : ℝ)) := by
  have hl := Real.log_natCast_nonneg M
  have ha : |alpha * Real.log M + beta| ≤ |alpha| * Real.log M + |beta| := by
    simpa only [abs_mul, abs_of_nonneg hl] using abs_add_le (alpha * Real.log M) beta
  have h1 : 2 * |alpha * Real.log M + beta| + 3 * |alpha| ≤
      (3 * |alpha| + 2 * |beta|) * (1 + Real.log M) := by
    nlinarith [abs_nonneg alpha, abs_nonneg beta, mul_nonneg (abs_nonneg beta) hl]
  have h2 := mul_le_mul_of_nonneg_left
    (one_add_log_le_two_log_two_mul (by exact_mod_cast hM : (1 : ℝ) ≤ M))
    (show 0 ≤ 3 * |alpha| + 2 * |beta| by positivity)
  unfold boundaryErrorConstant
  nlinarith

/-- Title: `The omitted smooth tail has the exact cutoff-logarithm inverse-square error`. -/
theorem sourceBoundary_error {M n : ℕ} (hM : 1 ≤ M) (hMn : M ≤ n) :
    |truncatedCentering n ((n : ℝ) / M) - (biasCoefficient * Real.log n + biasConstant) -
        sourceBoundary M n| ≤
      boundaryErrorConstant * M ^ 2 * Real.log (2 * (M : ℝ)) / n ^ 2 := by
  have hM0 : 0 < M := hM
  have hn : 0 < n := hM0.trans_le hMn
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have ha : (1 : ℝ) ≤ (n : ℝ) / M := (le_div_iff₀ hMR).mpr (by
    simp only [one_mul]
    exact_mod_cast hMn)
  rw [← smoothBoundary_eq_sourceBoundary hM0 hn]
  calc
    _ ≤ (2 / 3 : ℝ) * (2 * |boundaryCoefficient n ((n : ℝ) / M)| + 3 * |alpha|) /
        ((n : ℝ) / M) ^ 2 := truncatedCentering_boundary_error n ha
    _ = ((2 / 3 : ℝ) * (2 * |alpha * Real.log M + beta| + 3 * |alpha|)) * M ^ 2 / n ^ 2 := by
      rw [boundaryCoefficient_at_ratio hM0 hn]
      field_simp
    _ ≤ (boundaryErrorConstant * Real.log (2 * (M : ℝ))) * M ^ 2 / n ^ 2 := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (boundaryCoefficient_log_bound hM)
        (sq_nonneg (M : ℝ))) (sq_nonneg (n : ℝ))
    _ = _ := by ring

end NField.Alignment.StationaryCenteredBoundary

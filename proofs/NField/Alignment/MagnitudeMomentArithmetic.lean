/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.FiniteMagnitudeDecorrelation

/-!
# Normalizations in the magnitude moment identities

These are exact algebraic consequences of the manuscript's character sums.
The finite character sums that supply their inputs are audited separately.
-/

namespace NField.Alignment.MagnitudeMomentArithmetic

open scoped Topology
open Filter

noncomputable def marginalL (b : ℝ) : ℝ :=
  Real.pi ^ 2 / 6 * (1 - 1 / b ^ 2)

noncomputable def mixedSquare (b E : ℝ) : ℝ :=
  Real.pi ^ 2 * E / (2 * b ^ 2 * (b - 1))

noncomputable def squareRatio (b E : ℝ) : ℝ :=
  3 * E / ((b - 1) * (b ^ 2 - 1))

theorem bernoulli_marginal_subtraction (b : ℝ) (hb : 1 < b) :
    (((b - 1) ^ 2 * (b ^ 3 - 2) / (12 * b) -
      (b - 1) ^ 2 * (b - 2) / (12 * b)) / ((b - 1) ^ 2 / 2)) =
      (b ^ 2 - 1) / 6 := by
  have hb0 : b ≠ 0 := by linarith
  have hb1 : b - 1 ≠ 0 := by linarith
  field_simp
  ring

theorem twisted_marginal_subtraction (b : ℝ) (hb : 1 < b) :
    (((b - 1) ^ 2 * (b ^ 3 - 5) / (24 * b) -
      (b - 1) ^ 2 * (b - 5) / (24 * b)) / ((b - 1) ^ 2 / 2)) =
      (b ^ 2 - 1) / 12 := by
  have hb0 : b ≠ 0 := by linarith
  have hb1 : b - 1 ≠ 0 := by linarith
  field_simp
  ring

theorem bernoulli_to_l_normalization (b : ℝ) (hb : b ≠ 0) :
    Real.pi ^ 2 / b ^ 2 * ((b ^ 2 - 1) / 6) = marginalL b := by
  unfold marginalL
  field_simp

theorem twist_to_l_normalization (b : ℝ) (hb : b ≠ 0) :
    Real.pi ^ 2 / b ^ 2 * ((b ^ 2 - 1) / 12) = marginalL b / 2 := by
  unfold marginalL
  field_simp
  ring

theorem marginal_positive (b : ℝ) (hb : 1 < b) : 0 < marginalL b := by
  have hb2 : 1 < b ^ 2 := by nlinarith
  have hrec : 1 / b ^ 2 < 1 := (div_lt_one (by positivity)).mpr hb2
  unfold marginalL
  exact mul_pos (by positivity) (by linarith)

theorem marginal_upper (b : ℝ) : marginalL b ≤ Real.pi ^ 2 / 6 := by
  unfold marginalL
  have hh : 0 ≤ 1 / b ^ 2 := by positivity
  nlinarith [sq_nonneg Real.pi]

theorem variance_constant (b : ℝ) (hb : 5 ≤ b) :
    Real.pi ^ 2 / 100 ≤ marginalL b / 16 := by
  have hb2 : (25 : ℝ) ≤ b ^ 2 := by nlinarith
  have hh : 1 / b ^ 2 ≤ (1 / 25 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) hb2
  unfold marginalL
  nlinarith [mul_nonneg (sq_nonneg Real.pi) (sub_nonneg.mpr hh)]

theorem mixed_square_ratio (b E : ℝ) (hb : 1 < b) :
    mixedSquare b E / marginalL b = squareRatio b E := by
  have hb0 : b ≠ 0 := by linarith
  have hb1 : b - 1 ≠ 0 := by linarith
  have hb2 : b ^ 2 - 1 ≠ 0 := by nlinarith
  have hpi := Real.pi_ne_zero
  unfold mixedSquare marginalL squareRatio
  field_simp
  ring

theorem square_ratio_normalization (b E : ℝ) (hb : b ≠ 0) :
    squareRatio b E =
      3 * (E / b ^ 3) / ((1 - 1 / b) * (1 - (1 / b) ^ 2)) := by
  unfold squareRatio
  field_simp

/-- The limiting constant three follows from normalized cubic energy and
the reciprocal base tending to zero. No energy estimate is assumed proved
by this algebraic transfer. -/
theorem square_ratio_limit_from_cubic
    {α : Type*} {l : Filter α} (b E : α → ℝ)
    (hb : ∀ a, b a ≠ 0)
    (hinv : Tendsto (fun a => 1 / b a) l (𝓝 0))
    (hcubic : Tendsto (fun a => E a / b a ^ 3) l (𝓝 1)) :
    Tendsto (fun a => squareRatio (b a) (E a)) l (𝓝 3) := by
  have hden : Tendsto (fun a => (1 - 1 / b a) * (1 - (1 / b a) ^ 2))
      l (𝓝 1) := by
    have hone : Tendsto (fun _ : α => (1 : ℝ)) l (𝓝 1) :=
      tendsto_const_nhds
    simpa using (hone.sub hinv).mul (hone.sub (hinv.pow 2))
  have h := (hcubic.const_mul 3).div hden (by norm_num : (1 : ℝ) ≠ 0)
  have heq : (fun a => squareRatio (b a) (E a)) =
      (fun a => 3 * (E a / b a ^ 3) /
        ((1 - 1 / b a) * (1 - (1 / b a) ^ 2))) := by
    funext a
    exact square_ratio_normalization (b a) (E a) (hb a)
  rw [heq]
  convert h using 1 <;> first | rfl | norm_num

end NField.Alignment.MagnitudeMomentArithmetic

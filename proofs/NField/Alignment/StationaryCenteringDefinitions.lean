/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StationarySecondCenteringConstant
import NField.Alignment.StationaryStirlingConstant
import NField.Alignment.StationaryWeightConstants
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # The exact real centering constants and their sign -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.StationaryCenteringDefinitions
open StationaryDiagonalDefinitions StationaryConditionalConstants StationaryWeightConstants
  StationaryStirlingConstant StationarySecondCenteringConstant

def biasCoefficient : ℝ := (2 / 3 : ℝ) * alpha * integralZero
def biasConstant : ℝ := (2 / 3 : ℝ) * (beta * integralZero - alpha * integralOne)
def centeredDiagonal (n : ℕ) : ℝ := diagonal n - biasCoefficient * Real.log n - biasConstant

theorem alpha_positive : 0 < alpha := by unfold alpha; positivity

/-- Title: `The diagonal logarithmic bias has the printed exact coefficient`. -/
theorem biasCoefficient_formula :
    biasCoefficient = 2 / Real.pi ^ 2 * (Real.log (2 * Real.pi) - 2) := by
  rw [biasCoefficient, integralZero_evaluation]
  unfold alpha
  ring

theorem log_two_pi_lt_two : Real.log (2 * Real.pi) < 2 := by
  apply (Real.log_lt_iff_lt_exp (by positivity : 0 < 2 * Real.pi)).mpr
  have hp := Real.pi_lt_d2
  have he := Real.exp_one_gt_d9
  have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  rw [he2]
  nlinarith [Real.exp_pos 1]

/-- Title: `The exact diagonal logarithmic drift is strictly negative`. -/
theorem biasCoefficient_negative : biasCoefficient < 0 := by
  rw [biasCoefficient_formula]
  exact mul_neg_of_pos_of_neg (by positivity) (sub_neg.mpr log_two_pi_lt_two)

theorem centering_combination (n : ℝ) :
    (2 / 3 : ℝ) * ((alpha * Real.log n + beta) * integralZero - alpha * integralOne) =
      biasCoefficient * Real.log n + biasConstant := by
  unfold biasCoefficient biasConstant
  ring

/-- Title: `The constant centering term uses the actual second zeta derivative`. -/
theorem biasConstant_zeta_formula :
    (biasConstant : ℂ) = (2 / 3 : ℂ) * ((beta : ℂ) *
      ((Real.log (2 * Real.pi) : ℂ) / 2 - 1) -
      (alpha : ℂ) * (1 + iteratedDeriv 2 riemannZeta 0 / 2)) := by
  unfold biasConstant
  push_cast
  rw [integralOne_eq_zeta_second_derivative, integralZero_evaluation]
  push_cast
  rfl

end NField.Alignment.StationaryCenteringDefinitions

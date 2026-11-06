/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StationaryHarmonicProducts

/-! # The absolutely convergent constants in the cumulative-weight polynomial -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.StationaryWeightConstants
open scoped BigOperators
open MobiusReciprocalSquare CollisionLogTailKernel StationaryHarmonicProducts

def mobiusLogTerm (j d : ℕ) : ℝ := mobiusReciprocalSquare d * Real.log d ^ j
def mobiusLogMoment (j : ℕ) : ℝ := ∑' d, mobiusLogTerm j d
def alpha : ℝ := 6 / Real.pi ^ 2
def beta : ℝ := Real.eulerMascheroniConstant * alpha - mobiusLogMoment 1
def constantWeight : ℝ := mobiusLogMoment 2 / 2 - Real.eulerMascheroniConstant * mobiusLogMoment 1 +
  (Real.eulerMascheroniConstant ^ 2 - Real.pi ^ 2 / 6) * alpha / 2
def cumulativeMain (t : ℝ) : ℝ := alpha * Real.log t ^ 2 / 2 + beta * Real.log t + constantWeight

theorem mobiusLogTerm_norm_bound (j d : ℕ) :
    ‖mobiusLogTerm j d‖ ≤ logPowerKernel j d := by
  have hm : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
  have hl : 0 ≤ Real.log (d : ℝ) := Real.log_natCast_nonneg d
  rw [Real.norm_eq_abs, mobiusLogTerm, abs_mul, abs_pow, abs_of_nonneg hl]
  unfold mobiusReciprocalSquare logPowerKernel
  simp only [abs_div, abs_pow, abs_of_nonneg (show (0 : ℝ) ≤ d by positivity)]
  calc
    _ ≤ (1 / (d : ℝ) ^ 2) * Real.log d ^ j := by gcongr
    _ = _ := by ring

theorem mobiusLogTerm_summable (j : ℕ) : Summable (mobiusLogTerm j) :=
  Summable.of_norm_bounded (logPowerKernel_nat_summable j) (mobiusLogTerm_norm_bound j)

theorem mobiusLogMoment_zero : mobiusLogMoment 0 = alpha := by
  simpa [mobiusLogMoment, mobiusLogTerm, alpha] using hasSum_mobiusReciprocalSquare.tsum_eq

theorem main_term_polynomial {t : ℝ} (ht : 0 < t) (d : ℕ) :
    mobiusReciprocalSquare d * harmonicMain (t / d) =
      harmonicMain t * mobiusLogTerm 0 d -
        (Real.log t + Real.eulerMascheroniConstant) * mobiusLogTerm 1 d +
        (1 / 2 : ℝ) * mobiusLogTerm 2 d := by
  by_cases hd : d = 0
  · subst d
    simp [mobiusReciprocalSquare, mobiusLogTerm]
  · have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd
    unfold harmonicMain mobiusLogTerm
    rw [Real.log_div ht.ne' hdR]
    ring

/-- Title: `The cumulative-weight polynomial has the exact Möbius constants`. -/
theorem main_series_hasSum {t : ℝ} (ht : 0 < t) :
    HasSum (fun d : ℕ => mobiusReciprocalSquare d * harmonicMain (t / d)) (cumulativeMain t) := by
  have hs := (((mobiusLogTerm_summable 0).hasSum.mul_left (harmonicMain t)).sub
    ((mobiusLogTerm_summable 1).hasSum.mul_left (Real.log t + Real.eulerMascheroniConstant))).add
      ((mobiusLogTerm_summable 2).hasSum.mul_left (1 / 2 : ℝ))
  have he : harmonicMain t * mobiusLogMoment 0 -
      (Real.log t + Real.eulerMascheroniConstant) * mobiusLogMoment 1 +
      (1 / 2 : ℝ) * mobiusLogMoment 2 = cumulativeMain t := by
    rw [mobiusLogMoment_zero]
    unfold harmonicMain cumulativeMain beta constantWeight
    ring
  change HasSum _ (harmonicMain t * mobiusLogMoment 0 -
    (Real.log t + Real.eulerMascheroniConstant) * mobiusLogMoment 1 +
      (1 / 2 : ℝ) * mobiusLogMoment 2) at hs
  rw [he] at hs
  exact hs.congr_fun (fun d => main_term_polynomial ht d)

end NField.Alignment.StationaryWeightConstants

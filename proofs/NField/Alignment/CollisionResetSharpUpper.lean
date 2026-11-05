/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionResetGlobalEnvelope
import NField.Alignment.CollisionLogLogEnvelopes

/-!
# The sharp global upper order of the actual integer reset

The envelope applies to every sufficiently large positive integer. The
constant is identified by the proved limiting prime product, not inferred
from the lcm subsequence that will eventually attain this upper bound.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionResetSharpUpper

open Filter Asymptotics CollisionResetGlobalEnvelope CollisionLogLogEnvelopes
open CollisionResetEulerProduct CollisionLimitingPrimeProduct CollisionLimitingPrimeLogSum
open CollisionLcmSharpOrders CollisionZetaMoments CollisionResetIntegrability
open ProfiniteRemainderMeasure

def resetGlobalUpper (n : ℕ) : ℝ :=
  primeEulerEnvelope (|Real.eulerMascheroniConstant|+2)
    (zetaNat 2*zetaNat 3/12+|Real.eulerMascheroniConstant|) (Real.log n)

theorem integer_reset_global_upper {n : ℕ} (hn : 0 < n) (hlog : 1 < Real.log n) :
    resetFunction (integerPhase n) ≤ resetGlobalUpper n := by
  have hlog0 : Real.log (n : ℝ) ≠ 0 := (zero_lt_one.trans hlog).ne'
  have he : Real.log (n : ℝ)/(Real.log n*Real.log (Real.log n))=1/Real.log (Real.log n) := by
    field_simp
  have hP := resetEulerProduct_global_bound hn hlog
  rw [he] at hP
  have hS : resetEulerLogSum n ≤ limitingPrimeLogSum (Real.log n)+2 := by
    simpa only [mul_div_cancel_right₀ _ hlog0] using resetEulerLogSum_global_bound hn hlog
  have hB : 0 ≤ |Real.eulerMascheroniConstant|+limitingPrimeLogSum (Real.log n)+2 := by
    have h := (resetEulerLogSum_nonneg n).trans hS
    linarith [abs_nonneg Real.eulerMascheroniConstant]
  have hmain : resetEulerProduct n*(Real.eulerMascheroniConstant+resetEulerLogSum n) ≤
      limitingPrimeProduct (Real.log n)*Real.exp (1/Real.log (Real.log n))*
        (|Real.eulerMascheroniConstant|+limitingPrimeLogSum (Real.log n)+2) := by
    calc
      _ ≤ resetEulerProduct n*(|Real.eulerMascheroniConstant|+limitingPrimeLogSum (Real.log n)+2) :=
        mul_le_mul_of_nonneg_left (by linarith [le_abs_self Real.eulerMascheroniConstant])
          (resetEulerProduct_nonneg n)
      _ ≤ _ := mul_le_mul_of_nonneg_right hP hB
  have herr := (le_abs_self _).trans (integer_reset_euler_error hn)
  unfold resetGlobalUpper primeEulerEnvelope
  nlinarith

theorem integer_reset_eventual_upper :
    ∀ᶠ n : ℕ in atTop, resetFunction (integerPhase n) ≤ resetGlobalUpper n := by
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    log_nat_tendsto_atTop.eventually_gt_atTop 1] with n hn hlog
  exact integer_reset_global_upper hn hlog

theorem resetGlobalUpper_asymptotic :
    resetGlobalUpper ~[atTop] (fun n : ℕ => alignmentKappa*(Real.log (Real.log n))^2) :=
  primeEulerEnvelope_log_nat_asymptotic _ _

theorem integer_reset_sharp_upper {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop, resetFunction (integerPhase n) ≤
      (alignmentKappa+epsilon)*(Real.log (Real.log n))^2 := by
  have herror := isLittleO_iff.mp resetGlobalUpper_asymptotic.isLittleO
    (div_pos hepsilon alignmentKappa_pos)
  have he : (epsilon/alignmentKappa)*alignmentKappa=epsilon :=
    div_mul_cancel₀ epsilon alignmentKappa_pos.ne'
  filter_upwards [integer_reset_eventual_upper,herror] with n hn herr
  change ‖resetGlobalUpper n-alignmentKappa*(Real.log (Real.log n))^2‖ ≤
    (epsilon/alignmentKappa)*‖alignmentKappa*(Real.log (Real.log n))^2‖ at herr
  rw [Real.norm_eq_abs,Real.norm_of_nonneg (mul_nonneg alignmentKappa_pos.le (sq_nonneg _)),
    ← mul_assoc,he] at herr
  have h := (le_abs_self _).trans herr
  nlinarith

end NField.Alignment.CollisionResetSharpUpper

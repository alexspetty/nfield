/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionSharpMaximalOrders

/-!
# The complete maximal alignment and reset theorem

The exact integer increment is an affine function of the reset. Its
constant part vanishes at global scale, giving twice Gamma. The final
declaration assembles the attained lcm orders and all three limsups.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionMaximalOrderTheorem

open Filter Asymptotics CollisionSharpMaximalOrders CollisionSharpLimsupTransfer
open CollisionLcmLogLogScale CollisionLcmSharpOrders CollisionResetSharpUpper CollisionLogLogEnvelopes
open CollisionLimitingPrimeProduct CollisionResetIntegrability CollisionPotentialCoboundary
open CollisionOdometerRecurrence ProfiniteRemainderMeasure CollisionCylinderMeans

theorem inverse_loglog_square_tendsto_zero :
    Tendsto (fun n : ℕ => 1/(Real.log (Real.log n))^2) atTop (nhds 0) := by
  have h : Tendsto (fun n : ℕ => (Real.log (Real.log n))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp loglog_nat_tendsto_atTop
  simpa only [one_div,inv_pow,show (0 : ℝ)^2=0 by norm_num] using h.pow 2

theorem negative_increment_ratio_formula (n : ℕ) :
    -increment (integerPhase n)/(Real.log (Real.log n))^2=
      (2/3 : ℝ)*(resetFunction (integerPhase n)/(Real.log (Real.log n))^2)-
      (2/3 : ℝ)*(1/(Real.log (Real.log n))^2) := by
  unfold increment
  ring

theorem negative_increment_sharp_upper {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop, -increment (integerPhase n) ≤
      (2*alignmentGamma+epsilon)*(Real.log (Real.log n))^2 := by
  filter_upwards [integer_reset_sharp_upper (show 0 < 3*epsilon/2 by positivity)] with n hn
  unfold increment alignmentGamma
  nlinarith

theorem negative_increment_ratio_eventual_lower :
    ∀ᶠ n : ℕ in atTop, -1 ≤ -increment (integerPhase n)/(Real.log (Real.log n))^2 := by
  filter_upwards [loglog_nat_tendsto_atTop.eventually_ge_atTop 1] with n hn
  have hs : 1 ≤ (Real.log (Real.log n))^2 := by nlinarith
  apply (le_div_iff₀ (show 0 < (Real.log (Real.log n))^2 by linarith)).mpr
  have hF := resetFunction_pointwise_nonneg (integerPhase n)
  unfold increment
  nlinarith

theorem lcm_negative_increment_ratio_tendsto :
    Tendsto (fun m : ℕ => -increment (integerPhase (cutoffPeriod m))/
      (Real.log (Real.log (cutoffPeriod m)))^2) atTop (nhds (2*alignmentGamma)) := by
  simp_rw [negative_increment_ratio_formula]
  have hz := inverse_loglog_square_tendsto_zero.comp cutoffPeriod_tendsto_atTop
  have h := (lcm_reset_global_ratio_tendsto.const_mul (2/3 : ℝ)).sub (hz.const_mul (2/3 : ℝ))
  have he : (2/3 : ℝ)*alignmentKappa-(2/3 : ℝ)*0=2*alignmentGamma := by
    unfold alignmentGamma
    ring
  rw [he] at h
  simpa only [Function.comp_def] using h

theorem negative_increment_global_limsup :
    limsup (fun n : ℕ => -increment (integerPhase n)/(Real.log (Real.log n))^2) atTop=
      2*alignmentGamma := by
  apply limsup_eq_of_upper_and_attained (m := cutoffPeriod)
  · exact ⟨-1,negative_increment_ratio_eventual_lower⟩
  · exact scaled_upper_to_ratio_upper loglog_square_eventually_pos
      (fun _ hepsilon => negative_increment_sharp_upper hepsilon)
  · exact cutoffPeriod_tendsto_atTop
  · exact lcm_negative_increment_ratio_tendsto

theorem maximal_alignment_and_reset_orders :
    ((fun m : ℕ => resetFunction (integerPhase (cutoffPeriod m))) ~[atTop]
      (fun m : ℕ => alignmentKappa*(Real.log m)^2)) ∧
    ((fun m : ℕ => alignmentConstant (cutoffPeriod m)) ~[atTop]
      (fun m : ℕ => alignmentGamma*(Real.log m)^2)) ∧
    (limsup (fun n : ℕ => resetFunction (integerPhase n)/(Real.log (Real.log n))^2) atTop=
      alignmentKappa) ∧
    (limsup (fun L : ℕ => alignmentConstant L/(Real.log (Real.log L))^2) atTop=
      alignmentGamma) ∧
    (limsup (fun n : ℕ => -increment (integerPhase n)/(Real.log (Real.log n))^2) atTop=
      2*alignmentGamma) :=
  ⟨lcm_reset_sharp_order,lcm_alignment_sharp_order,reset_global_limsup,
    alignment_global_limsup,negative_increment_global_limsup⟩

end NField.Alignment.CollisionMaximalOrderTheorem

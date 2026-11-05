/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionLcmAlignmentEulerAsymptotic
import NField.Alignment.CollisionLogSquareAsymptotic
import NField.Alignment.CollisionBoundaryTesting

/-!
# Sharp orders of the actual reset and alignment values on the lcm sequence

All infinite products, logarithmic sums, finite-exponent errors and uniform
harmonic remainders have been proved before this assembly. The reset value
is the actual forcing function evaluated at the actual integer phase.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionLcmSharpOrders

open Filter Asymptotics CollisionLcmAlignmentEulerAsymptotic CollisionLogSquareAsymptotic
open CollisionLcmFiniteProducts CollisionLcmFiniteLogSums CollisionLimitingPrimeProduct
open CollisionResetEulerProduct CollisionAlignmentEulerProduct CollisionAlignmentPrimeLogSum
open CollisionOdometerRecurrence CollisionZetaMoments CollisionCylinderMeans
open CollisionBoundaryTesting CollisionResetIntegrability CollisionPotentialCoboundary
open ProfiniteRemainderMeasure

theorem integer_reset_euler_error {n : ℕ} (hn : 0 < n) :
    |resetFunction (integerPhase n)-
      resetEulerProduct n*(Real.eulerMascheroniConstant+resetEulerLogSum n)| ≤
      zetaNat 2*zetaNat 3/12+|Real.eulerMascheroniConstant| := by
  have h := reset_euler_uniform_error hn
  rw [CollisionResolutionLaw.resetTerm_tsum hn,← resetFunction_integer hn] at h
  exact shifted_uniform_error_bound h

theorem alignment_euler_scaled_error {L : ℕ} (hL : 0 < L) :
    |alignmentConstant L-
      (alignmentEulerProduct L*(Real.eulerMascheroniConstant+alignmentEulerLogSum L))/3| ≤
      (zetaNat 2*zetaNat 3/12+|Real.eulerMascheroniConstant+1|)/3 :=
  scaled_alignment_error_bound (alignment_euler_uniform_error hL)

theorem lcm_reset_sharp_order :
    (fun m : ℕ => resetFunction (integerPhase (cutoffPeriod m))) ~[atTop]
      (fun m : ℕ => alignmentKappa*(Real.log m)^2) := by
  have hmain := euler_main_log_square_asymptotic lcmResetEulerProduct_asymptotic
    lcmResetEulerLogSum_asymptotic
  apply asymptotic_of_uniform_log_square_error alignmentKappa_pos.ne' hmain
  intro m hm
  exact integer_reset_euler_error (show 0 < cutoffPeriod m from Nat.lcmUpto_pos m)

theorem lcm_alignment_sharp_order :
    (fun m : ℕ => alignmentConstant (cutoffPeriod m)) ~[atTop]
      (fun m : ℕ => alignmentGamma*(Real.log m)^2) := by
  have hmain := euler_main_log_square_asymptotic lcm_alignment_euler_product_asymptotic
    lcm_alignment_euler_log_sum_asymptotic
  have hthree : (fun _ : ℕ => (3 : ℝ)) ~[atTop] (fun _ : ℕ => (3 : ℝ)) := IsEquivalent.refl
  have hscaled : (fun m : ℕ =>
      (alignmentEulerProduct (cutoffPeriod m)*
        (Real.eulerMascheroniConstant+alignmentEulerLogSum (cutoffPeriod m)))/3) ~[atTop]
      (fun m : ℕ => alignmentGamma*(Real.log m)^2) := by
    have h := hmain.div hthree
    convert! h using 1
    funext m
    dsimp only [Pi.div_apply]
    unfold alignmentGamma
    ring
  apply asymptotic_of_uniform_log_square_error alignmentGamma_pos.ne' hscaled
  intro m hm
  exact alignment_euler_scaled_error (show 0 < cutoffPeriod m from Nat.lcmUpto_pos m)

theorem lcm_sharp_alignment_and_reset_orders :
    (fun m : ℕ => resetFunction (integerPhase (cutoffPeriod m))) ~[atTop]
      (fun m : ℕ => alignmentKappa*(Real.log m)^2) ∧
    (fun m : ℕ => alignmentConstant (cutoffPeriod m)) ~[atTop]
      (fun m : ℕ => alignmentGamma*(Real.log m)^2) :=
  ⟨lcm_reset_sharp_order,lcm_alignment_sharp_order⟩

end NField.Alignment.CollisionLcmSharpOrders

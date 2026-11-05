/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionLcmSharpOrders
import NField.Alignment.CollisionPrimeDistribution
import NField.Alignment.CollisionLogLogEnvelopes
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# The attained lcm orders in the global log-log scale

The unconditional logarithmic lcm asymptotic identifies the normalizing
scale. The lcm moduli themselves tend to infinity, so these values form
a valid sequence for the arbitrary-integer limsup.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionLcmLogLogScale

open Filter Asymptotics CollisionLcmSharpOrders CollisionPrimeDistribution
open CollisionLogLogEnvelopes CollisionLimitingPrimeProduct CollisionOdometerRecurrence
open CollisionResetIntegrability ProfiniteRemainderMeasure CollisionCylinderMeans

theorem cutoffPeriod_tendsto_atTop : Tendsto cutoffPeriod atTop atTop := by
  apply tendsto_atTop_mono _ tendsto_id
  intro m
  change m ≤ cutoffPeriod m
  by_cases hm : m=0
  · simp only [hm,Nat.zero_le]
  · have hd : m ∣ cutoffPeriod m := dvd_cutoffPeriod (by omega) le_rfl
    exact Nat.le_of_dvd (Nat.lcmUpto_pos m) hd

theorem lcm_loglog_asymptotic :
    (fun m : ℕ => Real.log (Real.log (cutoffPeriod m))) ~[atTop]
      (fun m : ℕ => Real.log m) :=
  log_cutoffPeriod_asymptotic.log (tendsto_natCast_atTop_atTop (R := ℝ))

theorem lcm_loglog_square_asymptotic (c : ℝ) :
    (fun m : ℕ => c*(Real.log (Real.log (cutoffPeriod m)))^2) ~[atTop]
      (fun m : ℕ => c*(Real.log m)^2) := by
  have hc : (fun _ : ℕ => c) ~[atTop] (fun _ : ℕ => c) := IsEquivalent.refl
  have h := hc.mul (lcm_loglog_asymptotic.mul lcm_loglog_asymptotic)
  convert! h using 1 <;> funext m <;> dsimp only [Pi.mul_apply] <;> ring

theorem lcm_reset_global_scale_asymptotic :
    (fun m : ℕ => resetFunction (integerPhase (cutoffPeriod m))) ~[atTop]
      (fun m : ℕ => alignmentKappa*(Real.log (Real.log (cutoffPeriod m)))^2) :=
  lcm_reset_sharp_order.trans (lcm_loglog_square_asymptotic alignmentKappa).symm

theorem lcm_alignment_global_scale_asymptotic :
    (fun m : ℕ => alignmentConstant (cutoffPeriod m)) ~[atTop]
      (fun m : ℕ => alignmentGamma*(Real.log (Real.log (cutoffPeriod m)))^2) :=
  lcm_alignment_sharp_order.trans (lcm_loglog_square_asymptotic alignmentGamma).symm

theorem ratio_tendsto_of_asymptotic {α : Type*} {l : Filter α} {f s : α → ℝ} {c : ℝ}
    (h : f ~[l] (fun a => c*s a)) (hs : ∀ᶠ a in l, s a ≠ 0) :
    Tendsto (fun a => f a/s a) l (nhds c) := by
  have hdiv := h.div (show s ~[l] s from IsEquivalent.refl)
  have hconstant : (fun a => c*s a/s a) =ᶠ[l] (fun _ => c) :=
    hs.mono (fun a ha => mul_div_cancel_right₀ c ha)
  exact (hdiv.congr_right hconstant).tendsto_const

theorem lcm_loglog_square_eventually_ne_zero :
    ∀ᶠ m : ℕ in atTop, (Real.log (Real.log (cutoffPeriod m)))^2 ≠ 0 := by
  have h := (loglog_nat_tendsto_atTop.comp cutoffPeriod_tendsto_atTop).eventually_gt_atTop 0
  filter_upwards [h] with m hm
  exact pow_ne_zero _ (ne_of_gt hm)

theorem lcm_reset_global_ratio_tendsto :
    Tendsto (fun m : ℕ => resetFunction (integerPhase (cutoffPeriod m))/
      (Real.log (Real.log (cutoffPeriod m)))^2) atTop (nhds alignmentKappa) :=
  ratio_tendsto_of_asymptotic lcm_reset_global_scale_asymptotic
    lcm_loglog_square_eventually_ne_zero

theorem lcm_alignment_global_ratio_tendsto :
    Tendsto (fun m : ℕ => alignmentConstant (cutoffPeriod m)/
      (Real.log (Real.log (cutoffPeriod m)))^2) atTop (nhds alignmentGamma) :=
  ratio_tendsto_of_asymptotic lcm_alignment_global_scale_asymptotic
    lcm_loglog_square_eventually_ne_zero

end NField.Alignment.CollisionLcmLogLogScale

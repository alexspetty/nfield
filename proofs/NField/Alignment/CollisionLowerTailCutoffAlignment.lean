/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionExponentialFloorScale

/-!
# Alignment above the threshold at the exact lower-tail cutoff

The attained sharp coefficient gives an excess of at least one above H
for every scale d > 1/sqrt(Gamma). The logarithm of the actual modulus is
bounded using the unconditional prime number theorem for lcm(1,...,m).
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionLowerTailCutoffAlignment

open Filter Asymptotics CollisionExponentialFloorScale CollisionTailCutoffScales
open CollisionLcmSharpOrders CollisionLimitingPrimeProduct CollisionOdometerRecurrence
open CollisionCylinderMeans CollisionPrimeDistribution

theorem cutoff_alignment_asymptotic {d : ℝ} (hd : 0 < d) :
    (fun H : ℝ => alignmentConstant (cutoffPeriod (tailCutoff d H))) ~[atTop]
      (fun H : ℝ => (alignmentGamma*d^2)*H) := by
  have hC := lcm_alignment_sharp_order.comp_tendsto (tailCutoff_tendsto hd)
  have hG : (fun _ : ℝ => alignmentGamma) ~[atTop] (fun _ : ℝ => alignmentGamma) := IsEquivalent.refl
  have hmain : (fun H : ℝ => alignmentGamma*(Real.log (tailCutoff d H))^2) ~[atTop]
      (fun H : ℝ => (alignmentGamma*d^2)*H) := by
    have h := hG.mul (log_tailCutoff_square_asymptotic hd)
    convert! h using 1
    funext H
    dsimp only [Pi.mul_apply]
    ring
  exact hC.trans hmain

theorem alignment_scale_coefficient_gt_one {d : ℝ} (hd : 1/Real.sqrt alignmentGamma < d) :
    0 < d ∧ 1 < alignmentGamma*d^2 := by
  have hroot : 0 < Real.sqrt alignmentGamma := Real.sqrt_pos.mpr alignmentGamma_pos
  have hd0 : 0 < d := (div_pos zero_lt_one hroot).trans hd
  have hmul : 1 < d*Real.sqrt alignmentGamma := (div_lt_iff₀ hroot).mp hd
  have hs : 1 < (d*Real.sqrt alignmentGamma)^2 := by nlinarith
  rw [mul_pow,Real.sq_sqrt alignmentGamma_pos.le] at hs
  exact ⟨hd0,by nlinarith⟩

theorem asymptotic_linear_excess {f : ℝ → ℝ} {c : ℝ} (hc : 1 < c)
    (hf : f ~[atTop] (fun H : ℝ => c*H)) : ∀ᶠ H : ℝ in atTop, H+1 ≤ f H := by
  have hc0 : 0 < c := by linarith
  let epsilon : ℝ := (c-1)/(2*c)
  have hepsilon : 0 < epsilon := div_pos (sub_pos.mpr hc) (by positivity)
  have herr := isLittleO_iff.mp hf.isLittleO hepsilon
  have hec : epsilon*c=(c-1)/2 := by unfold epsilon; field_simp
  filter_upwards [herr,eventually_ge_atTop (0 : ℝ),eventually_ge_atTop (2/(c-1))]
    with H h H0 HH
  change ‖f H-c*H‖ ≤ epsilon*‖c*H‖ at h
  rw [Real.norm_eq_abs,Real.norm_of_nonneg (mul_nonneg hc0.le H0)] at h
  have hlo := (abs_le.mp h).1
  have hheight : 2 ≤ H*(c-1) := (div_le_iff₀ (sub_pos.mpr hc)).mp HH
  have he : epsilon*(c*H)=((c-1)/2)*H := by rw [← mul_assoc,hec]
  rw [he] at hlo
  nlinarith

theorem cutoff_alignment_excess {d : ℝ} (hd : 1/Real.sqrt alignmentGamma < d) :
    ∀ᶠ H : ℝ in atTop, H+1 ≤ alignmentConstant (cutoffPeriod (tailCutoff d H)) :=
  asymptotic_linear_excess (alignment_scale_coefficient_gt_one hd).2
    (cutoff_alignment_asymptotic (alignment_scale_coefficient_gt_one hd).1)

theorem log_cutoffPeriod_eventual_upper :
    ∀ᶠ m : ℕ in atTop, Real.log (cutoffPeriod m) ≤ 2*(m : ℝ) := by
  have h := isLittleO_iff.mp log_cutoffPeriod_asymptotic.isLittleO (by norm_num : (0 : ℝ) < 1)
  filter_upwards [h] with m hm
  change ‖Real.log (cutoffPeriod m)-(m : ℝ)‖ ≤ 1*‖(m : ℝ)‖ at hm
  rw [Real.norm_eq_abs,Real.norm_natCast,one_mul] at hm
  have hu := (le_abs_self _).trans hm
  linarith

theorem lower_tail_modulus_log_bound {d : ℝ} (hd : 0 < d) :
    ∀ᶠ H : ℝ in atTop,
      Real.log (cutoffPeriod (tailCutoff d H)) ≤ 2*Real.exp (d*Real.sqrt H) := by
  have h := (tailCutoff_tendsto hd).eventually log_cutoffPeriod_eventual_upper
  filter_upwards [h] with H hH
  have hfloor : (tailCutoff d H : ℝ) ≤ Real.exp (d*Real.sqrt H) :=
    Nat.floor_le (Real.exp_pos _).le
  linarith

end NField.Alignment.CollisionLowerTailCutoffAlignment

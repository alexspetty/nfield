/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.External.ConservationPNT.MediumPNT
import NField.Alignment.CollisionMertensInput
import NField.Alignment.CollisionOdometerRecurrence

/-!
# Unconditional prime distribution inputs for conductor extrema

The checked prime number theorem gives the Chebyshev asymptotic and primes
in every fixed relative terminal interval. The finite CRT construction and
the eventual classification of minimizers are separate assertions.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionPrimeDistribution

open scoped BigOperators Topology
open Filter Asymptotics
open CollisionMertensInput

theorem prime_error_factor_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => Real.exp (-c*(Real.log x)^((1 : ℝ)/10))) atTop (𝓝 0) := by
  have hpow := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/10)).comp
    Real.tendsto_log_atTop
  have hmul := hpow.const_mul_atTop hc
  convert! Real.tendsto_exp_neg_atTop_nhds_zero.comp hmul using 1
  ext x
  simp [neg_mul]

theorem psi_asymptotic : Chebyshev.psi ~[atTop] (fun x : ℝ => x) := by
  obtain ⟨c,hc,hbound⟩ := MediumPNT
  have hsmall : (fun x : ℝ => Real.exp (-c*(Real.log x)^((1 : ℝ)/10))) =o[atTop]
      (fun _ : ℝ => (1 : ℝ)) :=
    (isLittleO_one_iff ℝ).mpr (prime_error_factor_tendsto hc)
  have hprod := (isBigO_refl (fun x : ℝ => x) atTop).mul_isLittleO hsmall
  have herr : (Chebyshev.psi-id) =o[atTop] (fun x : ℝ => x) := by
    simpa only [mul_one] using hbound.trans_isLittleO hprod
  exact herr.isEquivalent

theorem sqrt_isLittleO_id : Real.sqrt =o[atTop] (fun x : ℝ => x) := by
  apply (isLittleO_iff_tendsto (fun x hx => by simp [hx])).mpr
  apply (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/2)).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.sqrt_eq_rpow,show -(1/2 : ℝ)=1/2-1 by norm_num,Real.rpow_sub hx,Real.rpow_one]

theorem theta_asymptotic : Chebyshev.theta ~[atTop] (fun x : ℝ => x) := by
  have hdiff := Chebyshev.isBigO_psi_sub_theta_sqrt.trans_isLittleO sqrt_isLittleO_id
  have h := psi_asymptotic.isLittleO.sub hdiff
  have herr : (Chebyshev.theta-(fun x : ℝ => x)) =o[atTop] (fun x : ℝ => x) := by
    convert! h using 1
    ext x
    simp only [Pi.sub_apply]
    ring
  exact herr.isEquivalent

theorem theta_ratio_tendsto :
    Tendsto (fun x : ℝ => Chebyshev.theta x/x) atTop (𝓝 1) := by
  apply (isEquivalent_iff_tendsto_one (u := Chebyshev.theta) (v := fun x : ℝ => x) ?_).mp
    theta_asymptotic
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx using hx.ne'

theorem exists_prime_of_theta_lt {x y : ℝ} (h : Chebyshev.theta x < Chebyshev.theta y) :
    ∃ p : ℕ, p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ y := by
  by_contra hnone
  have hsub : primesUpTo y ⊆ primesUpTo x := by
    intro p hp
    have hm := primesUpTo_mem.mp hp
    have hnp : ¬x < (p : ℝ) := fun hxp => hnone ⟨p,hm.1,hxp,hm.2⟩
    exact primesUpTo_mem.mpr ⟨hm.1,le_of_not_gt hnp⟩
  have hle : Chebyshev.theta y ≤ Chebyshev.theta x := by
    change (∑ p ∈ primesUpTo y, Real.log p) ≤ ∑ p ∈ primesUpTo x, Real.log p
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro p hp _
    have hpp := (primesUpTo_mem.mp hp).1
    exact Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
  linarith

theorem prime_in_relative_interval {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    ∀ᶠ x : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ c*x < (p : ℝ) ∧ (p : ℝ) ≤ x := by
  have hscaled : Tendsto (fun x : ℝ => Chebyshev.theta (c*x)/(c*x)) atTop (𝓝 1) :=
    theta_ratio_tendsto.comp (tendsto_id.const_mul_atTop hc)
  have hscaled' : Tendsto (fun x : ℝ => Chebyshev.theta (c*x)/x) atTop (𝓝 c) := by
    convert! hscaled.const_mul c using 1
    · ext x
      by_cases hx : x=0
      · simp [hx]
      · field_simp
    · simp
  have hgap := theta_ratio_tendsto.sub hscaled'
  have hpos : ∀ᶠ x : ℝ in atTop, 0 < Chebyshev.theta x/x-Chebyshev.theta (c*x)/x :=
    (tendsto_order.mp hgap).1 0 (by linarith)
  filter_upwards [hpos,eventually_gt_atTop (0 : ℝ)] with x hx hx0
  apply exists_prime_of_theta_lt
  apply (div_lt_div_iff_of_pos_right hx0).mp
  linarith

theorem prime_in_relative_interval_nat {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    ∀ᶠ Q : ℕ in atTop, ∃ p : ℕ, p.Prime ∧ c*(Q : ℝ) < (p : ℝ) ∧ p ≤ Q := by
  have h := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (prime_in_relative_interval hc hc1)
  filter_upwards [h] with Q hQ
  obtain ⟨p,hp,hpgt,hple⟩ := hQ
  exact ⟨p,hp,hpgt,by exact_mod_cast hple⟩

theorem cutoffPeriod_eq_lcmUpto (Q : ℕ) :
    CollisionOdometerRecurrence.cutoffPeriod Q=Nat.lcmUpto Q := rfl

theorem log_cutoffPeriod_eq_psi (Q : ℕ) :
    Real.log (CollisionOdometerRecurrence.cutoffPeriod Q)=Chebyshev.psi Q := by
  rw [cutoffPeriod_eq_lcmUpto,Chebyshev.psi_eq_log_lcmUpto]

theorem log_cutoffPeriod_asymptotic :
    (fun Q : ℕ => Real.log (CollisionOdometerRecurrence.cutoffPeriod Q)) ~[atTop]
      (fun Q : ℕ => (Q : ℝ)) := by
  have h := psi_asymptotic.comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [Function.comp_def,log_cutoffPeriod_eq_psi] using h

end NField.Alignment.CollisionPrimeDistribution

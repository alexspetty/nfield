/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StationaryConditionalConstants
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Evaluation of the first conditional integral by Mathlib's Stirling theorem -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.StationaryStirlingConstant
open scoped BigOperators
open Filter MeasureTheory Set StationaryDiagonalDefinitions StationaryBernoulliPrimitive
  StationarySawtoothIntegrals StationaryConditionalConstants

theorem log_factorial_eq_sum (N : ℕ) :
    Real.log (N.factorial : ℝ) = ∑ k ∈ Finset.Icc 1 N, Real.log k := by
  have hp : (∏ k ∈ Finset.Icc 1 N, k) = N.factorial := by
    simpa only [Finset.Ico_add_one_right_eq_Icc] using Finset.prod_Ico_id_eq_factorial N
  rw [← hp, Nat.cast_prod]
  apply Real.log_prod
  intro k hk
  have hk0 : 0 < k := (Finset.mem_Icc.mp hk).1
  exact_mod_cast hk0.ne'

theorem sum_log_Ioc_factorial (N : ℕ) :
    (∑ k ∈ Finset.Ioc 1 N, Real.log (k : ℝ)) = Real.log (N.factorial : ℝ) := by
  rw [log_factorial_eq_sum]
  apply Finset.sum_subset
  · intro k hk
    have hh := Finset.mem_Ioc.mp hk
    exact Finset.mem_Icc.mpr ⟨by omega, hh.2⟩
  · intro k hk hn
    have hh := Finset.mem_Icc.mp hk
    have hk1 : k = 1 := by simp only [Finset.mem_Ioc] at hn; omega
    simp [hk1]

theorem floor_integral_identity {N : ℕ} (hN : 1 ≤ N) :
    (∫ x in Ioc (1 : ℝ) N, x⁻¹ * ((⌊x⌋₊ : ℝ) + 1)) =
      (N : ℝ) - 1 + (1 / 2 : ℝ) * Real.log N - ∫ x in (1 : ℝ)..N, psi x / x := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hne : ∀ x ∈ uIcc (1 : ℝ) N, x ≠ 0 := fun _ hx => positive_interval_ne_zero (by norm_num) hNR hx
  have hc : ContinuousOn (fun x : ℝ => 1 / x) (uIcc 1 N) :=
    continuousOn_const.div continuousOn_id hne
  have hi : IntervalIntegrable (fun x : ℝ => 1 / x) volume 1 N := hc.intervalIntegrable
  have hp : IntervalIntegrable (fun x : ℝ => psi x / x) volume 1 N := by
    simpa only [one_div, div_eq_mul_inv, one_mul] using (psi_interval_integrable 1 N).mul_continuousOn hc
  rw [← intervalIntegral.integral_of_le hNR]
  calc
    _ = ∫ x in (1 : ℝ)..N, (1 + (1 / 2 : ℝ) * (1 / x) - psi x / x) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hNR
      intro x hx
      have hx0 : 0 < x := by linarith [hx.1]
      dsimp only
      rw [natCast_floor_eq_intCast_floor hx0.le]
      unfold psi Int.fract
      field_simp
      ring
    _ = _ := by
      rw [intervalIntegral.integral_sub (intervalIntegrable_const.add (hi.const_mul _)) hp,
        intervalIntegral.integral_add intervalIntegrable_const (hi.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
        integral_one_div_of_pos (by norm_num) (by linarith : (0 : ℝ) < N)]
      simp

theorem reciprocal_psi_integral_natural {N : ℕ} (hN : 1 ≤ N) :
    (∫ x in (1 : ℝ)..N, psi x / x) =
      (N : ℝ) - 1 - ((N : ℝ) + 1 / 2) * Real.log N + Real.log (N.factorial : ℝ) := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hdiff : ∀ x ∈ Icc (1 : ℝ) N, DifferentiableAt ℝ Real.log x := by
    intro x hx
    exact (Real.hasDerivAt_log (by linarith [hx.1] : x ≠ 0)).differentiableAt
  have hi : IntegrableOn (deriv Real.log) (Icc (1 : ℝ) N) := by
    have hc : ContinuousOn (fun x : ℝ => x⁻¹) (Icc 1 N) :=
      continuousOn_id.inv₀ (fun x hx => by change x ≠ 0; linarith [hx.1])
    rw [Real.deriv_log']
    exact hc.integrableOn_Icc
  have h := sum_mul_eq_sub_sub_integral_mul' (fun _ : ℕ => (1 : ℝ)) (f := Real.log) hN
    (by simpa using hdiff) (by simpa using hi)
  simp only [mul_one, Finset.sum_const, Nat.card_Icc, Nat.sub_zero, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one, Real.log_one, zero_mul, sub_zero, Real.deriv_log] at h
  rw [sum_log_Ioc_factorial, floor_integral_identity hN] at h
  linarith

theorem reciprocal_psi_integral_stirling {N : ℕ} (hN : 1 ≤ N) :
    (∫ x in (1 : ℝ)..N, psi x / x) = Real.log (Stirling.stirlingSeq N) + Real.log 2 / 2 - 1 := by
  rw [reciprocal_psi_integral_natural hN, Stirling.log_stirlingSeq_formula]
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  rw [Real.log_div hN0 (Real.exp_ne_zero _), Real.log_exp,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hN0]
  ring

/-- Title: `The conditional reciprocal sawtooth integral equals one half log two pi minus one`. -/
theorem integralZero_evaluation : integralZero = Real.log (2 * Real.pi) / 2 - 1 := by
  have hleft := integralZero_tendsto.comp (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  have hright := ((Stirling.tendsto_stirlingSeq_sqrt_pi.log
    (ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos))).add_const (Real.log 2 / 2)).sub_const 1
  have hvalue : Real.log (Real.sqrt Real.pi) + Real.log 2 / 2 - 1 = Real.log (2 * Real.pi) / 2 - 1 := by
    rw [Real.log_sqrt Real.pi_pos.le, Real.log_mul (by norm_num) Real.pi_ne_zero]
    ring
  rw [hvalue] at hright
  apply tendsto_nhds_unique hleft
  apply hright.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  exact (reciprocal_psi_integral_stirling hN).symm

end NField.Alignment.StationaryStirlingConstant

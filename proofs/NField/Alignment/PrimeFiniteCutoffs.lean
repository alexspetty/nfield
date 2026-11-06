/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimePeriodicCounting

/-! # Literal finite cutoffs and normalization by the prime counting function -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000

namespace NField.Alignment.PrimePeriodicLimits

open Filter Finset
open scoped BigOperators Topology
open NField.External.ProgressionPNT

theorem sum_Ioc_cutoff_eventually (F : ℕ → ℂ) (c : ℕ) :
    (fun x : ℝ => ∑ n ∈ Finset.Ioc c ⌊x⌋₊, F n) =ᶠ[atTop]
      (fun x : ℝ => (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, F n) - ∑ n ∈ Finset.Ioc 0 c, F n) := by
  filter_upwards [tendsto_nat_floor_atTop.eventually (eventually_ge_atTop c)] with x hx
  have h := Finset.sum_Ioc_consecutive F (Nat.zero_le c) hx
  exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using h)

theorem sum_Ioc_cutoff_limit (F : ℕ → ℂ) (c : ℕ) {L : ℂ}
    (hL : Tendsto (fun x : ℝ => ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, F n) atTop (𝓝 L)) :
    Tendsto (fun x : ℝ => ∑ n ∈ Finset.Ioc c ⌊x⌋₊, F n)
      atTop (𝓝 (L - ∑ n ∈ Finset.Ioc 0 c, F n)) :=
  (hL.sub_const _).congr' (sum_Ioc_cutoff_eventually F c).symm

theorem primeAP_one_eq_primeCounting (x : ℝ) :
    primeAPCountingReal 1 0 x = (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  unfold primeAPCountingReal
  have heq : ((Icc 0 ⌊x⌋₊).filter fun p => p.Prime ∧ p % 1 = 0) =
      (Iic ⌊x⌋₊).filter Nat.Prime := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Iic, Nat.zero_le,
      true_and, Nat.mod_one, and_true]
  rw [heq, card_filter_prime_Iic]

theorem primeCounting_normalized_tendsto :
    Tendsto (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) / (x / Real.log x))
      atTop (𝓝 1) := by
  have h := primeAPCountingReal_normalized_tendsto (A := 1) (a := 0)
    (by omega) (by simp) (by omega)
  simpa only [primeAP_one_eq_primeCounting, Nat.totient_one, Nat.cast_one, inv_one] using h

theorem primeCounting_inv_tendsto_zero :
    Tendsto (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℂ)⁻¹) atTop (𝓝 0) := by
  have hreal : Tendsto (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (Nat.tendsto_primeCounting.comp tendsto_nat_floor_atTop)
  have h : Tendsto (fun x : ℝ => (((Nat.primeCounting ⌊x⌋₊ : ℝ)⁻¹ : ℝ) : ℂ))
      atTop (𝓝 (0 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_inv_atTop_zero.comp hreal)
  simpa only [Complex.ofReal_inv, Complex.ofReal_natCast] using h

theorem prime_count_zero_normalized_by_pi {F : ℝ → ℂ}
    (hF : Tendsto (fun x : ℝ => F x / (x / Real.log x : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun x : ℝ => F x / (Nat.primeCounting ⌊x⌋₊ : ℂ)) atTop (𝓝 0) := by
  have hpi : Tendsto (fun x : ℝ =>
      (((Nat.primeCounting ⌊x⌋₊ : ℝ) / (x / Real.log x) : ℝ) : ℂ)) atTop (𝓝 (1 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp primeCounting_normalized_tendsto
  simp only [Complex.ofReal_div, Complex.ofReal_natCast] at hpi
  have h := hF.div hpi (one_ne_zero : (1 : ℂ) ≠ 0)
  simp only [zero_div] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hscale : (↑(x / Real.log x) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (div_pos (by linarith) (Real.log_pos hx))
  simpa only [Pi.div_apply, Complex.ofReal_div] using
    div_div_div_cancel_right₀ hscale (F x) (Nat.primeCounting ⌊x⌋₊ : ℂ)

theorem sum_Ioc_cutoff_pi_limit (F : ℕ → ℂ) (c : ℕ)
    (hF : Tendsto (fun x : ℝ => (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, F n) /
      (Nat.primeCounting ⌊x⌋₊ : ℂ)) atTop (𝓝 0)) :
    Tendsto (fun x : ℝ => (∑ n ∈ Finset.Ioc c ⌊x⌋₊, F n) /
      (Nat.primeCounting ⌊x⌋₊ : ℂ)) atTop (𝓝 0) := by
  have hconstant := primeCounting_inv_tendsto_zero.const_mul (∑ n ∈ Finset.Ioc 0 c, F n)
  simp only [mul_zero] at hconstant
  have h := hF.sub hconstant
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [sum_Ioc_cutoff_eventually F c] with x hx
  simp only [hx, div_eq_mul_inv, sub_mul]

theorem centered_periodic_prime_tail_reciprocal_limit
    {q : ℕ} [NeZero q] (f : (ZMod q)ˣ → ℂ)
    (hzero : ∑ a, f a = 0) (c : ℕ) :
    ∃ L : ℂ, Tendsto (fun x : ℝ => ∑ p ∈ Finset.Ioc c ⌊x⌋₊,
      if p.Prime then unitExtension f p / (p : ℂ) else 0) atTop (𝓝 L) := by
  obtain ⟨L, hL⟩ := centered_periodic_prime_reciprocal_limit f hzero
  exact ⟨_, sum_Ioc_cutoff_limit _ c hL⟩

theorem centered_periodic_prime_tail_pi_limit
    {q : ℕ} [NeZero q] (f : (ZMod q)ˣ → ℂ)
    (hzero : ∑ a, f a = 0) (c : ℕ) :
    Tendsto (fun x : ℝ => (∑ p ∈ Finset.Ioc c ⌊x⌋₊,
      if p.Prime then unitExtension f p else 0) / (Nat.primeCounting ⌊x⌋₊ : ℂ))
      atTop (𝓝 0) :=
  sum_Ioc_cutoff_pi_limit _ c
    (prime_count_zero_normalized_by_pi (centered_periodic_prime_count_limit f hzero))

end NField.Alignment.PrimePeriodicLimits

/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimeVanishingAverage

/-! # Ordinary prime averages within a fixed coarse residue class -/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionPrimeLimits

open Filter Finset
open scoped BigOperators Topology
open NField.Alignment.PrimePeriodicLimits
open NField.Alignment.ProgressionMertens
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.NeutralityTheorem
open NField.Alignment.CollisionTransformStrip
open NField.Alignment.CollisionTransform

theorem periodic_prime_pi_limit {q : ℕ} [NeZero q] (f : (ZMod q)ˣ → ℂ) :
    Tendsto (fun x : ℝ => weightedPrimeCountSum f x / (Nat.primeCounting ⌊x⌋₊ : ℂ))
      atTop (𝓝 ((q.totient : ℂ)⁻¹ * ∑ a, f a)) := by
  have hpi : Tendsto (fun x : ℝ =>
      (Nat.primeCounting ⌊x⌋₊ : ℂ) / (x / Real.log x : ℝ)) atTop (𝓝 1) := by
    have h := Complex.continuous_ofReal.continuousAt.tendsto.comp primeCounting_normalized_tendsto
    simpa only [Function.comp_def, Complex.ofReal_div, Complex.ofReal_natCast,
      Complex.ofReal_one] using h
  have h := (periodic_prime_count_limit f).div hpi (one_ne_zero : (1 : ℂ) ≠ 0)
  simp only [div_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hn : (↑(x / Real.log x) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (div_pos (by linarith) (Real.log_pos hx)))
  exact div_div_div_cancel_right₀ hn _ _

theorem periodic_prime_tail_pi_limit {q : ℕ} [NeZero q]
    (f : (ZMod q)ˣ → ℂ) (c : ℕ) :
    Tendsto (fun x : ℝ => (∑ p ∈ Ioc c ⌊x⌋₊, if p.Prime then unitExtension f p else 0) /
      (Nat.primeCounting ⌊x⌋₊ : ℂ)) atTop (𝓝 ((q.totient : ℂ)⁻¹ * ∑ a, f a)) := by
  have hc := primeCounting_inv_tendsto_zero.const_mul
    (∑ p ∈ Ioc 0 c, if p.Prime then unitExtension f p else 0)
  simp only [mul_zero] at hc
  have h := (periodic_prime_pi_limit f).sub hc
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [sum_Ioc_cutoff_eventually
    (fun p => if p.Prime then unitExtension f p else 0) c] with x hx
  simp only [weightedPrimeCountSum, hx, div_eq_mul_inv, sub_mul]

theorem coarse_reduction_prime_unit {b ell p : ℕ} [NeZero b]
    [NeZero (allLagModulus b ell)] (hq : IsUnit (p : ZMod (allLagModulus b ell)))
    (hb : IsUnit (p : ZMod b)) : coarseUnitReduction b ell hq.unit = hb.unit := by
  exact unitReduction_nat_unit (show b ∣ allLagModulus b ell by
    exact dvd_pow_self b (by omega)) hq hb

theorem coarse_restricted_extension {b ell p : ℕ} [NeZero b]
    [NeZero (allLagModulus b ell)] (u : (ZMod b)ˣ) (hb : 2 ≤ b)
    (hell : 1 ≤ ell) (hp : p.Prime) (hbp : b < p) :
    unitExtension (restrictedUnitSignal (centeredCollisionTransform b ell)
      (fun a => coarseUnitReduction b ell a = u)) p =
      if (p : ZMod b) = u then directCenteredCollisionValue b ell p else 0 := by
  classical
  have hq := prime_unit_at_all_lag_modulus (ell := ell) (by omega : 0 < b) hp hbp
  have hub := prime_unit_of_modulus_lt hp hbp
  have hr := coarse_reduction_prime_unit hq hub
  have hc : hub.unit = u ↔ (p : ZMod b) = u := by rw [Units.ext_iff, hub.unit_spec]
  rw [directCenteredCollisionValue_eq_unitExtension hb hell]
  simp only [unitExtension, dif_pos hq, restrictedUnitSignal, hr, hc]

/-- Title: `Every coarse prime class has zero centered ordinary mean`. -/
theorem coarse_centered_prime_average_zero {b ell : ℕ} [NeZero b]
    [NeZero (allLagModulus b ell)] (hb : 2 ≤ b) (hell : 1 ≤ ell)
    (u : (ZMod b)ˣ) (c : ℕ) (hc : b ≤ c) :
    Tendsto (fun x : ℝ => realPrimeTailSum
      (fun p => if (p : ZMod b) = u then realDirectCenteredCollisionValue b ell p else 0) c x /
      (Nat.primeCounting ⌊x⌋₊ : ℝ)) atTop (𝓝 0) := by
  classical
  let F := restrictedUnitSignal (centeredCollisionTransform b ell)
    (fun a => coarseUnitReduction b ell a = u)
  have hzero : ∑ a, F a = 0 := by
    rw [restrictedUnitSignal_sum]
    apply centeredSignal_fiber_sum_zero
    obtain ⟨a, ha⟩ := coarseUnitReduction_surjective b ell u
    exact ⟨⟨a, ha⟩⟩
  have h := centered_periodic_prime_tail_pi_limit F hzero c
  have hr := Complex.continuous_re.continuousAt.tendsto.comp h
  simp only [Complex.zero_re] at hr
  apply hr.congr'
  apply Filter.Eventually.of_forall
  intro x
  have heq : (∑ p ∈ Ioc c ⌊x⌋₊, if p.Prime then unitExtension F p else 0) =
      (realPrimeTailSum (fun p => if (p : ZMod b) = u then
        realDirectCenteredCollisionValue b ell p else 0) c x : ℂ) := by
    rw [ofReal_realPrimeTailSum]
    apply Finset.sum_congr rfl
    intro p hmem
    by_cases hp : p.Prime
    · simp only [hp, ↓reduceIte, F, coarse_restricted_extension u hb hell hp
        (hc.trans_lt (mem_Ioc.mp hmem).1), apply_ite,
        ofReal_realDirectCenteredCollisionValue, Complex.ofReal_zero]
      split_ifs <;> rfl
    · simp [hp]
  change ((∑ p ∈ Ioc c ⌊x⌋₊, if p.Prime then unitExtension F p else 0) /
    (Nat.primeCounting ⌊x⌋₊ : ℂ)).re = _
  rw [heq]
  simp

end NField.Alignment.CollisionPrimeLimits

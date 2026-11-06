/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimePeriodicLimits

/-! # The ordinary prime average of a finite periodic unit signal -/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.PrimePeriodicLimits

open Filter Finset
open scoped BigOperators Topology
open NField.Alignment.ProgressionMertens
open NField.External.ProgressionPNT

variable {q : ℕ} [NeZero q]

theorem unit_class_count_eq (a : (ZMod q)ˣ) (x : ℝ) :
    (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
      if n.Prime ∧ (n : ZMod q) = a then (1 : ℂ) else 0) =
        (primeAPCountingReal q (a : ZMod q).val x : ℂ) := by
  classical
  have heq (n : ℕ) : ((n : ZMod q) = (a : ZMod q)) ↔
      n % q = (a : ZMod q).val := by
    simpa only [ZMod.natCast_zmod_val, Nat.mod_eq_of_lt (ZMod.val_lt (a : ZMod q))] using
      ZMod.natCast_eq_natCast_iff' n (a : ZMod q).val q
  have hset : Finset.Icc 0 ⌊x⌋₊ = Finset.range (⌊x⌋₊ + 1) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_range, zero_le, true_and]
    omega
  rw [sum_Ioc_eq_range_succ (by simp [Nat.not_prime_zero] :
    (if Nat.Prime 0 ∧ (0 : ZMod q) = a then (1 : ℂ) else 0) = 0)]
  simp only [primeAPCountingReal, hset, Complex.ofReal_natCast, Finset.card_eq_sum_ones,
    Finset.sum_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro n _
  simp only [heq]
  split_ifs <;> simp

theorem weightedPrimeCountSum_eq_classes (f : (ZMod q)ˣ → ℂ) (x : ℝ) :
    weightedPrimeCountSum f x =
      ∑ a : (ZMod q)ˣ, f a * (primeAPCountingReal q (a : ZMod q).val x : ℂ) := by
  classical
  simp_rw [← unit_class_count_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold weightedPrimeCountSum
  apply Finset.sum_congr rfl
  intro n _
  rw [unitExtension_eq_sum]
  by_cases hn : n.Prime
  · simp only [hn, ↓reduceIte, true_and]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  · simp [hn]

theorem periodic_prime_count_limit (f : (ZMod q)ˣ → ℂ) :
    Tendsto (fun x : ℝ => weightedPrimeCountSum f x / (x / Real.log x : ℝ))
      atTop (𝓝 ((q.totient : ℂ)⁻¹ * ∑ a : (ZMod q)ˣ, f a)) := by
  have hclass (a : (ZMod q)ˣ) :
      Tendsto (fun x : ℝ => f a *
        ((primeAPCountingReal q (a : ZMod q).val x : ℂ) / (x / Real.log x : ℝ)))
        atTop (𝓝 (f a * (q.totient : ℂ)⁻¹)) := by
    have h := (Complex.continuous_ofReal.tendsto ((q.totient : ℝ)⁻¹)).comp
      (unit_class_prime_density a)
    simpa only [Function.comp_apply, Complex.ofReal_div, Complex.ofReal_inv,
      Complex.ofReal_natCast] using h.const_mul (f a)
  have hsum := tendsto_finsetSum Finset.univ (fun a _ => hclass a)
  convert hsum using 1
  · ext x
    rw [weightedPrimeCountSum_eq_classes, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a _
    ring
  · rw [← Finset.sum_mul, mul_comm]

/-- Title: `Centered periodic prime count limit`.
This is the unweighted fixed-period prime-density limit. -/
theorem centered_periodic_prime_count_limit (f : (ZMod q)ˣ → ℂ)
    (hzero : ∑ a : (ZMod q)ˣ, f a = 0) :
    Tendsto (fun x : ℝ => weightedPrimeCountSum f x / (x / Real.log x : ℝ))
      atTop (𝓝 0) := by
  simpa only [hzero, mul_zero] using periodic_prime_count_limit f

end NField.Alignment.PrimePeriodicLimits

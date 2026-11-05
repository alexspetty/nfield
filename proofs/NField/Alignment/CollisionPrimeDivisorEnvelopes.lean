/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionLimitingPrimeProduct
import NField.Alignment.CollisionLimitingPrimeLogSum
import NField.Alignment.CollisionLargePrimeFactors

/-!
# Uniform envelopes for the prime divisors of any integer

The small prime factors are bounded by the complete limiting prime
product and logarithmic sum. Large dividing primes contribute an explicit
exponential multiplier and additive logarithmic error. These are finite
inequalities for every positive integer before choosing y = log(n).
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionPrimeDivisorEnvelopes

open scoped Classical
open CollisionLimitingPrimeProduct CollisionLimitingPrimeLogSum
open CollisionLargePrimeFactors CollisionMertensInput

def smallPrimeFactors (n : ℕ) (y : ℝ) : Finset ℕ :=
  n.primeFactors.filter (fun p => (p : ℝ) ≤ y)

theorem smallPrimeFactors_subset (n : ℕ) (y : ℝ) :
    smallPrimeFactors n y ⊆ primesUpTo y := by
  intro p hp
  obtain ⟨hpn,hpy⟩ := Finset.mem_filter.mp hp
  exact primesUpTo_mem.mpr ⟨Nat.prime_of_mem_primeFactors hpn,hpy⟩

theorem small_prime_product_bound (n : ℕ) (y : ℝ) :
    (∏ p ∈ smallPrimeFactors n y, (1+(p : ℝ)⁻¹)) ≤ limitingPrimeProduct y := by
  apply Finset.prod_le_prod_of_subset_of_one_le (smallPrimeFactors_subset n y)
  · intro p hp
    positivity
  · intro p hp hps
    have hi : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg p)
    linarith

theorem small_prime_log_sum_bound (n : ℕ) (y : ℝ) :
    (∑ p ∈ smallPrimeFactors n y, Real.log p/((p : ℝ)-1)) ≤ limitingPrimeLogSum y := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (smallPrimeFactors_subset n y)
  intro p hp hps
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast (primesUpTo_mem.mp hp).1.one_lt
  exact div_nonneg (Real.log_nonneg hp1.le) (sub_pos.mpr hp1).le

theorem large_prime_product_bound {n : ℕ} (hn : 0 < n) {y : ℝ} (hy : 1 < y) :
    (∏ p ∈ largePrimeFactors n y, (1+(p : ℝ)⁻¹)) ≤
      Real.exp (Real.log (n : ℝ)/(y*Real.log y)) := by
  have h := Real.prod_one_add_le_exp_sum (largePrimeFactors n y)
    (fun p => inv_nonneg.mpr (Nat.cast_nonneg p) : ∀ p : ℕ, 0 ≤ (p : ℝ)⁻¹)
  exact h.trans (Real.exp_le_exp.mpr (by
    simpa only [one_div] using large_prime_reciprocal_bound hn hy))

theorem prime_divisor_product_envelope {n : ℕ} (hn : 0 < n) {y : ℝ} (hy : 1 < y) :
    (∏ p ∈ n.primeFactors, (1+(p : ℝ)⁻¹)) ≤
      limitingPrimeProduct y*Real.exp (Real.log (n : ℝ)/(y*Real.log y)) := by
  have hs : (∏ p ∈ n.primeFactors, (1+(p : ℝ)⁻¹))=
      (∏ p ∈ smallPrimeFactors n y, (1+(p : ℝ)⁻¹))*
        (∏ p ∈ largePrimeFactors n y, (1+(p : ℝ)⁻¹)) := by
    simpa only [smallPrimeFactors,largePrimeFactors,not_le] using
      (Finset.prod_filter_mul_prod_filter_not n.primeFactors
        (fun p : ℕ => (p : ℝ) ≤ y) (fun p : ℕ => 1+(p : ℝ)⁻¹)).symm
  rw [hs]
  exact mul_le_mul (small_prime_product_bound n y) (large_prime_product_bound hn hy)
    (Finset.prod_nonneg (fun p hp => by positivity))
    (Finset.prod_nonneg (fun p hp => by positivity))

theorem prime_divisor_log_sum_envelope {n : ℕ} (hn : 0 < n) {y : ℝ} (hy : 1 < y) :
    (∑ p ∈ n.primeFactors, Real.log p/((p : ℝ)-1)) ≤
      limitingPrimeLogSum y+2*Real.log (n : ℝ)/y := by
  have hs : (∑ p ∈ n.primeFactors, Real.log p/((p : ℝ)-1))=
      (∑ p ∈ smallPrimeFactors n y, Real.log p/((p : ℝ)-1))+
        (∑ p ∈ largePrimeFactors n y, Real.log p/((p : ℝ)-1)) := by
    simpa only [smallPrimeFactors,largePrimeFactors,not_le] using
      (Finset.sum_filter_add_sum_filter_not n.primeFactors
        (fun p : ℕ => (p : ℝ) ≤ y) (fun p : ℕ => Real.log p/((p : ℝ)-1))).symm
  rw [hs]
  exact add_le_add (small_prime_log_sum_bound n y) (large_prime_logarithmic_bound hn hy)

end NField.Alignment.CollisionPrimeDivisorEnvelopes

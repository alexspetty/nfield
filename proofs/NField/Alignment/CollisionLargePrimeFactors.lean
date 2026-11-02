/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionAlignmentEulerProduct

/-!
# The contribution of large prime divisors

The logarithms of the distinct prime divisors have total at most log(n).
This gives both estimates in display 088 for every cutoff y > 1, before
specializing to y = log(n) in the maximal-order argument.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionLargePrimeFactors

open scoped Classical

def largePrimeFactors (n : ℕ) (y : ℝ) : Finset ℕ :=
  n.primeFactors.filter (fun p => y < (p : ℝ))

theorem prime_factor_log_sum_le {n : ℕ} (hn : 0 < n) :
    (∑ p ∈ n.primeFactors, Real.log (p : ℝ)) ≤ Real.log (n : ℝ) := by
  have hp (p : ℕ) (h : p ∈ n.primeFactors) : 0 < (p : ℝ) := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors h).pos
  have hprod : 0 < ∏ p ∈ n.primeFactors, (p : ℝ) := Finset.prod_pos hp
  have hle : (∏ p ∈ n.primeFactors, (p : ℝ)) ≤ (n : ℝ) := by
    have hnat : ((∏ p ∈ n.primeFactors, p : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)
    simpa only [Nat.cast_prod] using hnat
  rw [← Real.log_prod (fun p h => ne_of_gt (hp p h))]
  exact Real.log_le_log hprod hle

theorem prime_factor_subset_log_sum_le {n : ℕ} (hn : 0 < n)
    {s : Finset ℕ} (hs : s ⊆ n.primeFactors) :
    (∑ p ∈ s, Real.log (p : ℝ)) ≤ Real.log (n : ℝ) := by
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hs ?_) (prime_factor_log_sum_le hn)
  intro p hp hps
  exact Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le)

theorem large_prime_reciprocal_bound {n : ℕ} (hn : 0 < n) {y : ℝ} (hy : 1 < y) :
    (∑ p ∈ largePrimeFactors n y, 1/(p : ℝ)) ≤ Real.log (n : ℝ)/(y*Real.log y) := by
  have hy0 : 0 < y := lt_trans zero_lt_one hy
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hden : 0 < y*Real.log y := mul_pos hy0 hlogy
  have hterm (p : ℕ) (hp : p ∈ largePrimeFactors n y) :
      1/(p : ℝ) ≤ Real.log (p : ℝ)/(y*Real.log y) := by
    have hyp : y < (p : ℝ) := (Finset.mem_filter.mp hp).2
    have hp0 : 0 < (p : ℝ) := hy0.trans hyp
    calc
      1/(p : ℝ) ≤ 1/y := one_div_le_one_div_of_le hy0 hyp.le
      _ = Real.log y/(y*Real.log y) := by field_simp
      _ ≤ Real.log (p : ℝ)/(y*Real.log y) :=
        div_le_div_of_nonneg_right (Real.log_le_log hy0 hyp.le) hden.le
  calc
    _ ≤ ∑ p ∈ largePrimeFactors n y, Real.log (p : ℝ)/(y*Real.log y) :=
      Finset.sum_le_sum hterm
    _ = (∑ p ∈ largePrimeFactors n y, Real.log (p : ℝ))/(y*Real.log y) := by
      rw [Finset.sum_div]
    _ ≤ _ := div_le_div_of_nonneg_right
      (prime_factor_subset_log_sum_le hn (Finset.filter_subset _ _)) hden.le

theorem large_prime_logarithmic_bound {n : ℕ} (hn : 0 < n) {y : ℝ} (hy : 1 < y) :
    (∑ p ∈ largePrimeFactors n y, Real.log (p : ℝ)/((p : ℝ)-1)) ≤
      2*Real.log (n : ℝ)/y := by
  have hy0 : 0 < y := lt_trans zero_lt_one hy
  have hterm (p : ℕ) (hp : p ∈ largePrimeFactors n y) :
      Real.log (p : ℝ)/((p : ℝ)-1) ≤ (2/y)*Real.log (p : ℝ) := by
    have hmem := (Finset.mem_filter.mp hp).1
    have hyp : y < (p : ℝ) := (Finset.mem_filter.mp hp).2
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hmem).two_le
    have hp1 : 0 < (p : ℝ)-1 := by linarith
    have hrec : 1/((p : ℝ)-1) ≤ 2/y := by
      apply (div_le_div_iff₀ hp1 hy0).mpr
      linarith
    have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith)
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using mul_le_mul_of_nonneg_right hrec hlog
  calc
    _ ≤ ∑ p ∈ largePrimeFactors n y, (2/y)*Real.log (p : ℝ) := Finset.sum_le_sum hterm
    _ = (2/y)*(∑ p ∈ largePrimeFactors n y, Real.log (p : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ (2/y)*Real.log (n : ℝ) := mul_le_mul_of_nonneg_left
      (prime_factor_subset_log_sum_le hn (Finset.filter_subset _ _)) (by positivity)
    _ = _ := by ring

theorem large_prime_factor_bounds {n : ℕ} (hn : 0 < n) {y : ℝ} (hy : 1 < y) :
    (∑ p ∈ n.primeFactors.filter (fun (p : ℕ) => y < (p : ℝ)), 1/(p : ℝ)) ≤
      Real.log (n : ℝ)/(y*Real.log y) ∧
    (∑ p ∈ n.primeFactors.filter (fun (p : ℕ) => y < (p : ℝ)), Real.log (p : ℝ)/((p : ℝ)-1)) ≤
      2*Real.log (n : ℝ)/y :=
  ⟨large_prime_reciprocal_bound hn hy, large_prime_logarithmic_bound hn hy⟩

end NField.Alignment.CollisionLargePrimeFactors

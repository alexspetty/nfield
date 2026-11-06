/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionMertensInput
import NField.Alignment.CollisionLargePrimeFactors
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Small and large prime-factor bounds for near-one reciprocal weights -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.NearOnePrimeWeights
open CollisionMertensInput CollisionLargePrimeFactors
open scoped BigOperators Classical

/-- A bounded logarithmic power costs a uniform absolute factor. -/
theorem power_le_three {x ε : ℝ} (hx : 0 < x) (he : ε*Real.log x ≤ 1) : x^ε ≤ 3 := by
  rw [Real.rpow_def_of_pos hx]
  exact (Real.exp_le_exp.mpr (by nlinarith only [he])).trans Real.exp_one_lt_three.le

/-- Every prime local reciprocal weight stays uniformly away from one. -/
theorem prime_weight_le_three_quarters {p ε : ℝ} (hp : 2 ≤ p) (he : ε ≤ 1/2) :
    p^(ε-1) ≤ 3/4 := by
  have hp0 : 0 < p := by linarith
  have hs : 4/3 ≤ Real.sqrt p := by nlinarith [Real.sqrt_nonneg p, Real.sq_sqrt hp0.le]
  calc
    _ ≤ p^(-(1/2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ = (Real.sqrt p)⁻¹ := by rw [Real.rpow_neg hp0.le, ← Real.sqrt_eq_rpow]
    _ ≤ _ := by
      rw [← one_div]
      apply (div_le_iff₀ (Real.sqrt_pos.mpr hp0)).mpr
      nlinarith

/-- Small primes have at most three times their ordinary reciprocal weight. -/
theorem small_prime_weight_bound {p Y ε : ℝ} (hp : 0 < p) (hpY : p ≤ Y)
    (he0 : 0 ≤ ε) (he : ε*Real.log Y ≤ 1) : p^(ε-1) ≤ 3/p := by
  rw [Real.rpow_sub_one hp.ne']
  apply div_le_div_of_nonneg_right _ hp.le
  apply power_le_three hp
  exact (mul_le_mul_of_nonneg_left (Real.log_le_log hp hpY) he0).trans he

/-- Large primes are controlled at the split point because the reciprocal exponent is negative. -/
theorem large_prime_weight_bound {p Y ε : ℝ} (hY : 1 < Y) (hYp : Y ≤ p)
    (he : ε ≤ 1/2) (hlog : ε*Real.log Y ≤ 1) : p^(ε-1) ≤ 3/Y := by
  have hY0 : 0 < Y := by linarith
  calc
    _ ≤ Y^(ε-1) := Real.rpow_le_rpow_of_nonpos hY0 hYp (by linarith)
    _ = Y^ε/Y := Real.rpow_sub_one hY0.ne' ε
    _ ≤ _ := div_le_div_of_nonneg_right (power_le_three hY0 hlog) hY0.le

/-- The logarithmic prime-factor budget bounds the large-prime contribution pointwise in n. -/
theorem large_prime_weight_sum {n : ℕ} (hn : 0 < n) {Y ε : ℝ}
    (hY : 1 < Y) (he : ε ≤ 1/2) (hlog : ε*Real.log Y ≤ 1) :
    (∑ p ∈ largePrimeFactors n Y, (p : ℝ)^(ε-1)) ≤
      3*Real.log (n : ℝ)/(Y*Real.log Y) := by
  have hY0 : 0 < Y := by linarith
  have hlY : 0 < Real.log Y := Real.log_pos hY
  have hterm : ∀ p ∈ largePrimeFactors n Y, (p : ℝ)^(ε-1) ≤
      (3/(Y*Real.log Y))*Real.log (p : ℝ) := by
    intro p hp
    have hYp : Y < (p : ℝ) := (Finset.mem_filter.mp hp).2
    have hp0 : (0 : ℝ) < p := hY0.trans hYp
    calc
      _ ≤ 3/Y := large_prime_weight_bound hY hYp.le he hlog
      _ = (3/(Y*Real.log Y))*Real.log Y := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.log_le_log hY0 hYp.le) (by positivity)
  calc
    _ ≤ ∑ p ∈ largePrimeFactors n Y, (3/(Y*Real.log Y))*Real.log (p : ℝ) := Finset.sum_le_sum hterm
    _ = (3/(Y*Real.log Y)) * ∑ p ∈ largePrimeFactors n Y, Real.log (p : ℝ) := by rw [Finset.mul_sum]
    _ ≤ (3/(Y*Real.log Y))*Real.log (n : ℝ) := mul_le_mul_of_nonneg_left
      (prime_factor_subset_log_sum_le hn (Finset.filter_subset _ _)) (by positivity)
    _ = _ := by ring

/-- Splitting at log n leaves a small-prime reciprocal sum and a uniformly bounded large-prime term. -/
theorem prime_factor_weight_sum {n : ℕ} (hn : 0 < n) {ε : ℝ}
    (hL : 1 < Real.log (n : ℝ)) (he0 : 0 ≤ ε) (he : ε ≤ 1/2)
    (hlog : ε*Real.log (Real.log (n : ℝ)) ≤ 1) :
    (∑ p ∈ n.primeFactors, (p : ℝ)^(ε-1)) ≤
      3*(∑ p ∈ primesUpTo (Real.log n), 1/(p : ℝ))+3/Real.log (Real.log n) := by
  let Y := Real.log (n : ℝ)
  let S : Finset ℕ := n.primeFactors.filter (fun (p : ℕ) => (p : ℝ) ≤ Y)
  have hsplit : (∑ p ∈ n.primeFactors, (p : ℝ)^(ε-1)) =
      (∑ p ∈ S, (p : ℝ)^(ε-1)) + ∑ p ∈ largePrimeFactors n Y, (p : ℝ)^(ε-1) := by
    simp only [S, largePrimeFactors, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hs : (p : ℝ) ≤ Y
    · simp [hs, not_lt.mpr hs]
    · simp [hs, lt_of_not_ge hs]
  have hsmall : (∑ p ∈ S, (p : ℝ)^(ε-1)) ≤ 3*∑ p ∈ primesUpTo Y, 1/(p : ℝ) := by
    calc
      _ ≤ ∑ p ∈ S, 3/(p : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        have hmem := Finset.mem_filter.mp hp
        have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hmem.1).pos
        exact small_prime_weight_bound hp0 hmem.2 he0 hlog
      _ = 3*∑ p ∈ S, 1/(p : ℝ) := by rw [Finset.mul_sum]; simp only [mul_one_div]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          have hmem := Finset.mem_filter.mp hp
          exact primesUpTo_mem.mpr ⟨Nat.prime_of_mem_primeFactors hmem.1, hmem.2⟩
        · intro p hp hn
          positivity
  have hlarge := large_prime_weight_sum hn hL he hlog
  have hY0 : 0 < Y := by dsimp [Y]; linarith
  have heq : 3*Real.log (n : ℝ)/(Y*Real.log Y) = 3/Real.log Y := by
    change 3*Y/(Y*Real.log Y) = _
    field_simp
  rw [heq] at hlarge
  rw [hsplit]
  exact add_le_add hsmall hlarge

end NField.Alignment.NearOnePrimeWeights

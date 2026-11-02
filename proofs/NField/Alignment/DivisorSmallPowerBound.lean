/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.PSeries

/-!
# Small-power bounds for the number of divisors

The constant is independent of the integer being factored. Large primes
absorb the local factor `(k+1)^m`; only the finitely many primes below `2^m`
cost a constant. The local exponential bound is proved by rising factorials
and binomial coefficients, so no divisor-growth estimate is an input.
-/

set_option autoImplicit false

namespace NField.Alignment.DivisorSmallPowerBound

open scoped BigOperators

def localConstant (m : ℕ) : ℕ := m.factorial * 2^m

def divisorConstant (m : ℕ) : ℕ := localConstant m ^ (2^m)

theorem localConstant_pos (m : ℕ) : 0 < localConstant m := by
  unfold localConstant
  exact Nat.mul_pos (Nat.factorial_pos m) (by positivity)

theorem divisorConstant_pos (m : ℕ) : 0 < divisorConstant m :=
  pow_pos (localConstant_pos m) _

theorem power_succ_le_exponential (m k : ℕ) :
    (k+1)^m ≤ localConstant m * 2^k := by
  calc
    (k+1)^m ≤ (k+1).ascFactorial m := Nat.pow_succ_le_ascFactorial _ _
    _ = m.factorial * (k+m).choose m := Nat.ascFactorial_eq_factorial_mul_choose _ _
    _ ≤ m.factorial * 2^(k+m) := Nat.mul_le_mul_left _ (Nat.choose_le_two_pow _ _)
    _ = _ := by simp only [localConstant, pow_add]; ring

theorem prime_power_factor_bound (m k p : ℕ) (hp : p.Prime) :
    (k+1)^m ≤ (if p < 2^m then localConstant m else 1) * p^k := by
  by_cases hsmall : p < 2^m
  · rw [if_pos hsmall]
    exact (power_succ_le_exponential m k).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hp.two_le k))
  · rw [if_neg hsmall, one_mul]
    calc
      (k+1)^m ≤ (2^k)^m := Nat.pow_le_pow_left (Nat.succ_le_of_lt k.lt_two_pow_self) m
      _ = (2^m)^k := by rw [← pow_mul, ← pow_mul, Nat.mul_comm k m]
      _ ≤ p^k := Nat.pow_le_pow_left (Nat.le_of_not_lt hsmall) k

/-- A uniform integer-power divisor bound with an explicit absolute
constant for each exponent. -/
theorem divisor_count_pow_le (m n : ℕ) (hn : n ≠ 0) :
    n.divisors.card^m ≤ divisorConstant m * n := by
  classical
  have hcard : (n.primeFactors.filter (fun p => p < 2^m)).card ≤ 2^m := by
    calc
      _ ≤ (Finset.range (2^m)).card := Finset.card_le_card (by
        intro p hp
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
      _ = _ := Finset.card_range _
  have hconstants :
      (∏ p ∈ n.primeFactors, if p < 2^m then localConstant m else 1) ≤
        divisorConstant m := by
    simp only [← Finset.prod_filter, Finset.prod_const]
    exact Nat.pow_le_pow_right (localConstant_pos m) hcard
  calc
    n.divisors.card^m = ∏ p ∈ n.primeFactors, (n.factorization p + 1)^m := by
      rw [Nat.card_divisors hn, Finset.prod_pow]
    _ ≤ ∏ p ∈ n.primeFactors,
        (if p < 2^m then localConstant m else 1) * p^(n.factorization p) := by
      apply Finset.prod_le_prod'
      intro p hp
      exact prime_power_factor_bound m _ p (Nat.prime_of_mem_primeFactors hp)
    _ = (∏ p ∈ n.primeFactors, if p < 2^m then localConstant m else 1) * n := by
      rw [Finset.prod_mul_distrib, ← Nat.prod_primeFactors_pow_factorization hn]
    _ ≤ divisorConstant m * n := Nat.mul_le_mul_right n hconstants

theorem divisor_count_le_reciprocal_power (m : ℕ) (hm : 0 < m)
    (n : ℕ) (hn : n ≠ 0) :
    (n.divisors.card : ℝ) ≤ (divisorConstant m : ℝ)^((m : ℝ)⁻¹) *
      (n : ℝ)^((m : ℝ)⁻¹) := by
  have h : (n.divisors.card : ℝ)^m ≤ (divisorConstant m : ℝ)*(n : ℝ) := by
    exact_mod_cast divisor_count_pow_le m n hn
  have hr := Real.rpow_le_rpow (by positivity) h (by positivity : 0 ≤ (m : ℝ)⁻¹)
  rw [Real.pow_rpow_inv_natCast (Nat.cast_nonneg _) hm.ne',
    Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)] at hr
  exact hr

/-- The elementary divisor estimate for every positive real exponent.
The constant depends only on the exponent, not on the integer. -/
theorem divisor_count_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      (n.divisors.card : ℝ) ≤ C * (n : ℝ)^ε := by
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  let C : ℝ := (divisorConstant (m+1) : ℝ)^(((m+1 : ℕ) : ℝ)⁻¹)
  have hC : 0 < C := Real.rpow_pos_of_pos (by
    exact_mod_cast divisorConstant_pos (m+1)) _
  refine ⟨C, hC, ?_⟩
  intro n hn
  calc
    (n.divisors.card : ℝ) ≤ C * (n : ℝ)^(((m+1 : ℕ) : ℝ)⁻¹) :=
      divisor_count_le_reciprocal_power (m+1) (Nat.succ_pos m) n hn.ne'
    _ ≤ C * (n : ℝ)^ε := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
      simpa only [Nat.cast_add, Nat.cast_one, one_div] using hm.le

/-- The particular exponent in Proposition 10. -/
theorem divisor_count_sixteenth :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      (n.divisors.card : ℝ) ≤ C * (n : ℝ)^(1/16 : ℝ) :=
  divisor_count_small_power _ (by norm_num)

/-- The two divisor factors in the paper's `q^4` box cost only `q^(1/2)`,
with one constant for all moduli and all positive residue-pair indices. -/
theorem divisor_pair_box_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ q u v : ℕ, 0 < q →
      u ∈ Finset.Icc 1 (q^4) → v ∈ Finset.Icc 1 (q^4) →
      (u.divisors.card : ℝ) * (v.divisors.card : ℝ) ≤ C * (q : ℝ)^(1/2 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := divisor_count_sixteenth
  refine ⟨C^2, sq_pos_of_pos hC, ?_⟩
  intro q u v _ hu hv
  have hsingle (a : ℕ) (ha : a ∈ Finset.Icc 1 (q^4)) :
      (a.divisors.card : ℝ) ≤ C*(q : ℝ)^(1/4 : ℝ) := by
    obtain ⟨hapos, hale⟩ := Finset.mem_Icc.mp ha
    calc
      (a.divisors.card : ℝ) ≤ C*(a : ℝ)^(1/16 : ℝ) := hbound a hapos
      _ ≤ C*((q : ℝ)^4)^(1/16 : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ hC.le
        apply Real.rpow_le_rpow (Nat.cast_nonneg a) _ (by norm_num)
        exact_mod_cast hale
      _ = C*(q : ℝ)^(1/4 : ℝ) := by
        congr 1
        rw [← Real.rpow_natCast (q : ℝ) 4, ← Real.rpow_mul (Nat.cast_nonneg q)]
        norm_num
  calc
    _ ≤ (C*(q : ℝ)^(1/4 : ℝ)) * (C*(q : ℝ)^(1/4 : ℝ)) :=
      mul_le_mul (hsingle u hu) (hsingle v hv) (Nat.cast_nonneg _)
        (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg q) _))
    _ = C^2 * (q : ℝ)^(1/2 : ℝ) := by
      rw [show (C*(q : ℝ)^(1/4 : ℝ)) * (C*(q : ℝ)^(1/4 : ℝ)) =
        C^2 * ((q : ℝ)^(1/4 : ℝ))^2 by ring]
      rw [← Real.rpow_mul_natCast (Nat.cast_nonneg q) (1/4 : ℝ) 2]
      norm_num

noncomputable def divisorSquareWeight (n : ℕ) : ℝ :=
  (n.divisors.card : ℝ)^2/(n : ℝ)^2

theorem divisorSquareWeight_nonneg (n : ℕ) : 0 ≤ divisorSquareWeight n := by
  unfold divisorSquareWeight
  positivity

/-- The diagonal series in the fourth-moment argument converges. -/
theorem summable_divisor_square_weight : Summable divisorSquareWeight := by
  obtain ⟨C, hC, hbound⟩ := divisor_count_sixteenth
  have hmajorant (n : ℕ) :
      divisorSquareWeight n ≤ C^2 * (n : ℝ)^(-15/8 : ℝ) := by
    by_cases hn : n = 0
    · subst n
      simp only [divisorSquareWeight, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0),
        div_zero]
      positivity
    have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    calc
      divisorSquareWeight n ≤ (C*(n : ℝ)^(1/16 : ℝ))^2/(n : ℝ)^2 := by
        unfold divisorSquareWeight
        gcongr
        exact hbound n (Nat.pos_of_ne_zero hn)
      _ = C^2 * (n : ℝ)^(-15/8 : ℝ) := by
        rw [mul_pow, mul_div_assoc]
        congr 1
        rw [← Real.rpow_mul_natCast hnR.le (1/16 : ℝ) 2,
          ← Real.rpow_natCast (n : ℝ) 2, ← Real.rpow_sub hnR]
        norm_num
  have hs : Summable (fun n : ℕ => (n : ℝ)^(-15/8 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  exact (hs.mul_left (C^2)).of_nonneg_of_le divisorSquareWeight_nonneg hmajorant

theorem divisor_square_sum_le (s : Finset ℕ) :
    (∑ n ∈ s, divisorSquareWeight n) ≤ ∑' n : ℕ, divisorSquareWeight n := by
  apply Summable.sum_le_tsum s
  · intro n _
    exact divisorSquareWeight_nonneg n
  · exact summable_divisor_square_weight

end NField.Alignment.DivisorSmallPowerBound

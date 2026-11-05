/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionPrimeDivisorEnvelopes
import NField.Alignment.CollisionLcmSharpOrders

/-!
# Finite global envelopes for the reset Euler factors

The estimates hold for every positive observation and every cutoff above
one. They retain the actual integer factorization before the asymptotic
specialization to the logarithm of the observation.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionResetGlobalEnvelope

open scoped Classical
open CollisionPrimeDivisorEnvelopes CollisionResetEulerProduct CollisionResetLocalFactors
open CollisionLimitingPrimeProduct CollisionLimitingPrimeLogSum

theorem resetEulerProduct_nonneg (n : ℕ) : 0 ≤ resetEulerProduct n := by
  apply Finset.prod_nonneg
  intro p hp
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  exact zero_le_one.trans (resetPrimeFactor_bounds hp1 _).1

theorem resetEulerLogSum_nonneg (n : ℕ) : 0 ≤ resetEulerLogSum n := by
  apply Finset.sum_nonneg
  intro p hp
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  exact mul_nonneg (resetPrimeAverage_bounds hp1 _).1 (Real.log_nonneg hp1.le)

theorem resetEulerProduct_global_bound {n : ℕ} (hn : 0 < n) {y : ℝ} (hy : 1 < y) :
    resetEulerProduct n ≤
      limitingPrimeProduct y*Real.exp (Real.log (n : ℝ)/(y*Real.log y)) := by
  apply le_trans _ (prime_divisor_product_envelope hn hy)
  apply Finset.prod_le_prod
  · intro p hp
    have hp1 : 1 < (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    exact zero_le_one.trans (resetPrimeFactor_bounds hp1 _).1
  · intro p hp
    have hp1 : 1 < (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    exact (resetPrimeFactor_bounds hp1 _).2

theorem resetEulerLogSum_global_bound {n : ℕ} (hn : 0 < n) {y : ℝ} (hy : 1 < y) :
    resetEulerLogSum n ≤ limitingPrimeLogSum y+2*Real.log (n : ℝ)/y := by
  apply le_trans _ (prime_divisor_log_sum_envelope hn hy)
  apply Finset.sum_le_sum
  intro p hp
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  have h := mul_le_mul_of_nonneg_right (resetPrimeAverage_bounds hp1 (n.factorization p)).2
    (Real.log_nonneg hp1.le)
  simpa only [one_div,div_eq_mul_inv,one_mul,mul_comm] using h

end NField.Alignment.CollisionResetGlobalEnvelope

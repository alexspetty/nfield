/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionAlignmentEnvelopeSet
import NField.Alignment.CollisionAbsentPrimeProducts

/-!
# Exact global head and absent-prime splits for alignment

The finite head includes all small primes, whether or not they divide L,
and all remaining divisors. The complementary product and logarithmic
sum retain every absent-prime contribution with exponent zero.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionAlignmentGlobalSplit

open scoped Classical
open CollisionAlignmentEnvelopeSet CollisionAlignmentEulerProduct CollisionAlignmentPrimeLogSum
open CollisionAlignmentLocalSeries CollisionAbsentPrimeProducts CollisionAbsentPrimeSums

def alignmentGlobalHeadProduct (L : ℕ) (y : ℝ) : ℝ :=
  ∏ p ∈ envelopePrimeSet L y, alignmentPrimeFactor (p : ℝ) (L.factorization p)

def alignmentGlobalHeadLogSum (L : ℕ) (y : ℝ) : ℝ :=
  ∑ p ∈ envelopePrimeSet L y, alignmentPrimeAverage (p : ℝ) (L.factorization p)*Real.log p

theorem alignment_global_prime_factor_split (L : ℕ) (y : ℝ) (p : Nat.Primes) :
    alignmentPrimeFactor (p.val : ℝ) (L.factorization p.val)=
      (if p.val ∈ envelopePrimeSet L y then
        alignmentPrimeFactor (p.val : ℝ) (L.factorization p.val) else 1)*
      (if y < (p.val : ℝ) ∧ p.val ∉ L.primeFactors then
        alignmentPrimeFactor (p.val : ℝ) 0 else 1) := by
  by_cases hp : p.val ∈ envelopePrimeSet L y
  · have ha : ¬(y < (p.val : ℝ) ∧ p.val ∉ L.primeFactors) :=
      fun h => (envelopePrimeSet_complement p.property).mpr h hp
    simp only [if_pos hp,if_neg ha,mul_one]
  · have ha := (envelopePrimeSet_complement p.property).mp hp
    rw [factorization_zero_of_not_primeFactor ha.2,if_neg hp,if_pos ha,one_mul]

theorem alignment_global_prime_log_split (L : ℕ) (y : ℝ) (p : Nat.Primes) :
    alignmentPrimeLogTerm L p=
      (if p.val ∈ envelopePrimeSet L y then
        alignmentPrimeAverage (p.val : ℝ) (L.factorization p.val)*Real.log p.val else 0)+
      absentPrimeLogTerm L y p := by
  unfold alignmentPrimeLogTerm absentPrimeLogTerm
  by_cases hp : p.val ∈ envelopePrimeSet L y
  · have ha : ¬(y < (p.val : ℝ) ∧ p.val ∉ L.primeFactors) :=
      fun h => (envelopePrimeSet_complement p.property).mpr h hp
    simp only [if_pos hp,if_neg ha,add_zero]
  · have ha := (envelopePrimeSet_complement p.property).mp hp
    rw [factorization_zero_of_not_primeFactor ha.2,if_neg hp,if_pos ha,zero_add]

theorem alignment_global_product_split (L : ℕ) (y : ℝ) :
    alignmentEulerProduct L=alignmentGlobalHeadProduct L y*absentPrimeProduct L y := by
  have hh := finite_prime_set_product (envelopePrimeSet L y)
    (fun _ hp => envelopePrimeSet_prime hp)
    (fun p => alignmentPrimeFactor (p : ℝ) (L.factorization p))
  have ht := absentPrimeProduct_multipliable L y
  calc
    _ = ∏' p : Nat.Primes,
        ((if p.val ∈ envelopePrimeSet L y then
          alignmentPrimeFactor (p.val : ℝ) (L.factorization p.val) else 1)*
        (if y < (p.val : ℝ) ∧ p.val ∉ L.primeFactors then
          alignmentPrimeFactor (p.val : ℝ) 0 else 1)) :=
      tprod_congr (alignment_global_prime_factor_split L y)
    _ = _ := by
      rw [hh.1.tprod_mul ht,hh.2]
      rfl

theorem alignment_global_log_sum_split (L : ℕ) {y : ℝ} (hy : 1 ≤ y) :
    alignmentEulerLogSum L=alignmentGlobalHeadLogSum L y+absentPrimeLogSum L y := by
  have hh := finite_prime_set_sum (envelopePrimeSet L y)
    (fun _ hp => envelopePrimeSet_prime hp)
    (fun p => alignmentPrimeAverage (p : ℝ) (L.factorization p)*Real.log p)
  have ht := absentPrimeLogTerm_summable L hy
  calc
    _ = ∑' p : Nat.Primes,
        ((if p.val ∈ envelopePrimeSet L y then
          alignmentPrimeAverage (p.val : ℝ) (L.factorization p.val)*Real.log p.val else 0)+
        absentPrimeLogTerm L y p) :=
      tsum_congr (alignment_global_prime_log_split L y)
    _ = _ := by
      rw [hh.1.tsum_add ht,hh.2]
      rfl

end NField.Alignment.CollisionAlignmentGlobalSplit

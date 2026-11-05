/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionLcmFiniteLogSums

/-!
# The finite and absent-prime parts of the actual lcm alignment product

The full infinite alignment product and logarithmic sum are split exactly.
The finite part uses the actual lcm exponents; every prime above the
cutoff remains in the separately convergent absent-prime tail.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionLcmAlignmentTailSplit

open scoped Classical
open CollisionLcmFiniteProducts CollisionLcmPrimeLosses CollisionOdometerRecurrence
open CollisionAlignmentEulerProduct CollisionAlignmentPrimeLogSum CollisionAlignmentLocalSeries
open CollisionAbsentPrimeProducts CollisionAbsentPrimeSums

def primeCutoffSet (m : ℕ) : Finset Nat.Primes := (Nat.primesLE m).subtype Nat.Prime

theorem primeCutoffSet_mem (m : ℕ) (p : Nat.Primes) : p ∈ primeCutoffSet m ↔ p.val ≤ m := by
  constructor
  · intro hp
    exact Nat.le_of_mem_primesLE (Finset.mem_subtype.mp hp)
  · intro hp
    exact Finset.mem_subtype.mpr (Nat.mem_primesLE.mpr ⟨hp,p.property⟩)

theorem finite_prime_head_product (m : ℕ) (f : ℕ → ℝ) :
    Multipliable (fun p : Nat.Primes => if p ∈ primeCutoffSet m then f p.val else 1) ∧
    (∏' p : Nat.Primes, if p ∈ primeCutoffSet m then f p.val else 1)=∏ n ∈ Nat.primesLE m, f n := by
  constructor
  · apply multipliable_of_ne_finset_one (s := primeCutoffSet m)
    intro p hp
    exact if_neg hp
  · rw [tprod_eq_prod (s := primeCutoffSet m) (fun p hp => if_neg hp)]
    calc
      _ = ∏ p ∈ primeCutoffSet m, f p.val := Finset.prod_congr rfl (fun p hp => if_pos hp)
      _ = _ := Finset.prod_subtype_of_mem f (fun p hp => Nat.prime_of_mem_primesLE hp)

theorem finite_prime_head_sum (m : ℕ) (f : ℕ → ℝ) :
    Summable (fun p : Nat.Primes => if p ∈ primeCutoffSet m then f p.val else 0) ∧
    (∑' p : Nat.Primes, if p ∈ primeCutoffSet m then f p.val else 0)=∑ n ∈ Nat.primesLE m, f n := by
  constructor
  · apply summable_of_ne_finset_zero (s := primeCutoffSet m)
    intro p hp
    exact if_neg hp
  · rw [tsum_eq_sum (s := primeCutoffSet m) (fun p hp => if_neg hp)]
    calc
      _ = ∑ p ∈ primeCutoffSet m, f p.val := Finset.sum_congr rfl (fun p hp => if_pos hp)
      _ = _ := Finset.sum_subtype_of_mem f (fun p hp => Nat.prime_of_mem_primesLE hp)

theorem lcm_prime_absent_iff (m : ℕ) (p : Nat.Primes) :
    ((m : ℝ) < (p.val : ℝ) ∧ p.val ∉ (cutoffPeriod m).primeFactors) ↔ p ∉ primeCutoffSet m := by
  rw [cutoffPeriod_primeFactors,primeCutoffSet_mem]
  constructor
  · intro h
    have hm : m < p.val := by exact_mod_cast h.1
    omega
  · intro h
    have hm : m < p.val := by omega
    exact ⟨by exact_mod_cast hm,fun hp => h (Nat.le_of_mem_primesLE hp)⟩

theorem lcm_alignment_prime_factor_split (m : ℕ) (p : Nat.Primes) :
    alignmentPrimeFactor (p.val : ℝ) ((cutoffPeriod m).factorization p.val)=
      (if p ∈ primeCutoffSet m then
        alignmentPrimeFactor (p.val : ℝ) ((cutoffPeriod m).factorization p.val) else 1)*
      (if (m : ℝ) < (p.val : ℝ) ∧ p.val ∉ (cutoffPeriod m).primeFactors then
        alignmentPrimeFactor (p.val : ℝ) 0 else 1) := by
  by_cases hp : p ∈ primeCutoffSet m
  · have hn := not_iff_not.mpr (lcm_prime_absent_iff m p)
    simp only [if_pos hp,if_neg (hn.mpr (not_not.mpr hp)),mul_one]
  · have ha := (lcm_prime_absent_iff m p).mpr hp
    rw [factorization_zero_of_not_primeFactor ha.2,if_neg hp,if_pos ha,one_mul]

theorem lcm_alignment_prime_log_split (m : ℕ) (p : Nat.Primes) :
    alignmentPrimeLogTerm (cutoffPeriod m) p=
      (if p ∈ primeCutoffSet m then
        alignmentPrimeAverage (p.val : ℝ) ((cutoffPeriod m).factorization p.val)*Real.log p.val else 0)+
      absentPrimeLogTerm (cutoffPeriod m) m p := by
  unfold alignmentPrimeLogTerm absentPrimeLogTerm
  by_cases hp : p ∈ primeCutoffSet m
  · have hn := not_iff_not.mpr (lcm_prime_absent_iff m p)
    simp only [if_pos hp,if_neg (hn.mpr (not_not.mpr hp)),add_zero]
  · have ha := (lcm_prime_absent_iff m p).mpr hp
    rw [factorization_zero_of_not_primeFactor ha.2,if_neg hp,if_pos ha,zero_add]

theorem lcm_alignment_product_split (m : ℕ) :
    alignmentEulerProduct (cutoffPeriod m)=lcmAlignmentFiniteProduct m*absentPrimeProduct (cutoffPeriod m) m := by
  have hh := finite_prime_head_product m
    (fun p => alignmentPrimeFactor (p : ℝ) ((cutoffPeriod m).factorization p))
  have ht := absentPrimeProduct_multipliable (cutoffPeriod m) (m : ℝ)
  calc
    _ = ∏' p : Nat.Primes,
        ((if p ∈ primeCutoffSet m then
          alignmentPrimeFactor (p.val : ℝ) ((cutoffPeriod m).factorization p.val) else 1)*
        (if (m : ℝ) < (p.val : ℝ) ∧ p.val ∉ (cutoffPeriod m).primeFactors then
          alignmentPrimeFactor (p.val : ℝ) 0 else 1)) :=
      tprod_congr (lcm_alignment_prime_factor_split m)
    _ = _ := by
      rw [hh.1.tprod_mul ht,hh.2]
      rfl

theorem lcm_alignment_log_sum_split {m : ℕ} (hm : 1 ≤ m) :
    alignmentEulerLogSum (cutoffPeriod m)=lcmAlignmentFiniteLogSum m+absentPrimeLogSum (cutoffPeriod m) m := by
  have hh := finite_prime_head_sum m
    (fun p => alignmentPrimeAverage (p : ℝ) ((cutoffPeriod m).factorization p)*Real.log p)
  have ht := absentPrimeLogTerm_summable (cutoffPeriod m) (by exact_mod_cast hm : (1 : ℝ) ≤ m)
  calc
    _ = ∑' p : Nat.Primes,
        ((if p ∈ primeCutoffSet m then
          alignmentPrimeAverage (p.val : ℝ) ((cutoffPeriod m).factorization p.val)*Real.log p.val else 0)+
        absentPrimeLogTerm (cutoffPeriod m) m p) :=
      tsum_congr (lcm_alignment_prime_log_split m)
    _ = _ := by
      rw [hh.1.tsum_add ht,hh.2]
      rfl

end NField.Alignment.CollisionLcmAlignmentTailSplit

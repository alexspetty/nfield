/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionAlignmentEulerLocalSums

/-!
# Convergence of the logarithmic prime sum for alignment

Only finitely many primes divide the fixed modulus. Every other prime
retains the exact exponent-zero factor; its logarithmic contribution is
dominated by twice log(p)/p^2. This proves the actual prime sum convergent.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionAlignmentPrimeLogSum

open scoped Classical
open CollisionAlignmentLocalSeries CollisionAlignmentLocalBounds CollisionZetaMoments

def alignmentPrimeLogTerm (L : ℕ) (p : Nat.Primes) : ℝ :=
  alignmentPrimeAverage (p.val : ℝ) (L.factorization p.val)*Real.log p.val

def alignmentEulerLogSum (L : ℕ) : ℝ := ∑' p : Nat.Primes, alignmentPrimeLogTerm L p

theorem factorization_zero_of_not_primeFactor {L p : ℕ} (hp : p ∉ L.primeFactors) :
    L.factorization p=0 := by
  apply Finsupp.notMem_support_iff.mp
  rwa [Nat.support_factorization]

theorem alignmentPrimeLogTerm_nonneg (L : ℕ) (p : Nat.Primes) :
    0 ≤ alignmentPrimeLogTerm L p := by
  have hp1 : 1 < (p.val : ℝ) := by exact_mod_cast p.property.one_lt
  exact mul_nonneg (alignmentPrimeAverage_bounds hp1 _).1 (Real.log_nonneg hp1.le)

theorem alignmentPrimeLogTerm_absent_bound (L : ℕ) (p : Nat.Primes)
    (hp : p.val ∉ L.primeFactors) :
    ‖alignmentPrimeLogTerm L p‖ ≤ 2*logSquareTerm p.val := by
  have hp2 : 2 ≤ (p.val : ℝ) := by exact_mod_cast p.property.two_le
  have hl : 0 ≤ Real.log (p.val : ℝ) := Real.log_nonneg (by linarith)
  rw [Real.norm_of_nonneg (alignmentPrimeLogTerm_nonneg L p)]
  unfold alignmentPrimeLogTerm
  rw [factorization_zero_of_not_primeFactor hp]
  calc
    _ ≤ (2/(p.val : ℝ)^2)*Real.log p.val :=
      mul_le_mul_of_nonneg_right (alignmentPrimeAverage_zero_bound hp2) hl
    _ = _ := by unfold logSquareTerm; ring

theorem alignmentPrimeLogTerm_summable (L : ℕ) : Summable (alignmentPrimeLogTerm L) := by
  let s : Finset Nat.Primes := L.primeFactors.subtype Nat.Prime
  have hbase : Summable (fun p : Nat.Primes => 2*logSquareTerm p.val) :=
    (logSquareTerm_summable.mul_left 2).comp_injective (Subtype.val_injective (p := Nat.Prime))
  have hhead : Summable (fun p : Nat.Primes => if p ∈ s then alignmentPrimeLogTerm L p else 0) := by
    apply summable_of_ne_finset_zero (s := s)
    intro p hp
    exact if_neg hp
  have htail : Summable (fun p : Nat.Primes => if p ∈ s then 0 else alignmentPrimeLogTerm L p) := by
    apply Summable.of_norm_bounded hbase
    intro p
    by_cases hp : p ∈ s
    · simp only [if_pos hp,norm_zero]
      have hp1 : 1 ≤ (p.val : ℝ) := by exact_mod_cast p.property.one_lt.le
      have hl := Real.log_nonneg hp1
      unfold logSquareTerm
      positivity
    · simp only [if_neg hp]
      apply alignmentPrimeLogTerm_absent_bound L p
      intro hmem
      apply hp
      exact Finset.mem_subtype.mpr hmem
  apply (hhead.add htail).congr
  intro p
  by_cases hp : p ∈ s <;> simp [hp]

theorem alignmentEulerLogSum_hasSum (L : ℕ) :
    HasSum (alignmentPrimeLogTerm L) (alignmentEulerLogSum L) :=
  (alignmentPrimeLogTerm_summable L).hasSum

end NField.Alignment.CollisionAlignmentPrimeLogSum

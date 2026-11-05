/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionPrimeDivisorEnvelopes

/-!
# The complete finite prime head for a global alignment bound

The head includes every prime at most y and every larger prime dividing
the modulus. Its complement is exactly the absent-prime tail, so no
nontrivial exponent-zero factor can be lost.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionAlignmentEnvelopeSet

open scoped Classical
open CollisionPrimeDivisorEnvelopes CollisionMertensInput CollisionLargePrimeFactors
open CollisionLimitingPrimeProduct CollisionLimitingPrimeLogSum

def envelopePrimeSet (L : ℕ) (y : ℝ) : Finset ℕ :=
  primesUpTo y ∪ largePrimeFactors L y

def liftPrimeSet (s : Finset ℕ) : Finset Nat.Primes := s.subtype Nat.Prime

theorem liftPrimeSet_mem (s : Finset ℕ) (p : Nat.Primes) :
    p ∈ liftPrimeSet s ↔ p.val ∈ s := Finset.mem_subtype

theorem envelopePrimeSet_prime {L p : ℕ} {y : ℝ} (hp : p ∈ envelopePrimeSet L y) : p.Prime := by
  rcases Finset.mem_union.mp hp with hsmall|hlarge
  · exact (primesUpTo_mem.mp hsmall).1
  · exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hlarge).1

theorem envelopePrimeSet_mem {L p : ℕ} {y : ℝ} (hp : p.Prime) :
    p ∈ envelopePrimeSet L y ↔ (p : ℝ) ≤ y ∨ p ∈ L.primeFactors := by
  simp only [envelopePrimeSet,Finset.mem_union,primesUpTo_mem,hp,true_and,
    largePrimeFactors,Finset.mem_filter]
  constructor
  · rintro (h|⟨h,_⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h|h)
    · exact Or.inl h
    · by_cases hy : (p : ℝ) ≤ y
      · exact Or.inl hy
      · exact Or.inr ⟨h,lt_of_not_ge hy⟩

theorem envelopePrimeSet_complement {L p : ℕ} {y : ℝ} (hp : p.Prime) :
    p ∉ envelopePrimeSet L y ↔ y < (p : ℝ) ∧ p ∉ L.primeFactors := by
  rw [envelopePrimeSet_mem hp,not_or,not_le]

theorem envelopePrimeSet_disjoint (L : ℕ) (y : ℝ) :
    Disjoint (primesUpTo y) (largePrimeFactors L y) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact (not_lt_of_ge (primesUpTo_mem.mp hp).2) (Finset.mem_filter.mp hq).2

theorem envelopePrimeSet_product_bound {L : ℕ} (hL : 0 < L) {y : ℝ} (hy : 1 < y) :
    (∏ p ∈ envelopePrimeSet L y, (1+(p : ℝ)⁻¹)) ≤
      limitingPrimeProduct y*Real.exp (Real.log (L : ℝ)/(y*Real.log y)) := by
  rw [envelopePrimeSet,Finset.prod_union (envelopePrimeSet_disjoint L y)]
  exact mul_le_mul_of_nonneg_left (large_prime_product_bound hL hy)
    (Finset.prod_nonneg (fun p hp => by positivity))

theorem envelopePrimeSet_log_sum_bound {L : ℕ} (hL : 0 < L) {y : ℝ} (hy : 1 < y) :
    (∑ p ∈ envelopePrimeSet L y, Real.log p/((p : ℝ)-1)) ≤
      limitingPrimeLogSum y+2*Real.log (L : ℝ)/y := by
  rw [envelopePrimeSet,Finset.sum_union (envelopePrimeSet_disjoint L y)]
  exact add_le_add le_rfl (large_prime_logarithmic_bound hL hy)

theorem finite_prime_set_product (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (f : ℕ → ℝ) :
    Multipliable (fun p : Nat.Primes => if p.val ∈ s then f p.val else 1) ∧
    (∏' p : Nat.Primes, if p.val ∈ s then f p.val else 1)=∏ n ∈ s, f n := by
  have he := liftPrimeSet_mem s
  constructor
  · apply multipliable_of_ne_finset_one (s := liftPrimeSet s)
    intro p hp
    exact if_neg (fun h => hp ((he p).mpr h))
  · rw [tprod_eq_prod (s := liftPrimeSet s) (fun p hp => if_neg (fun h => hp ((he p).mpr h)))]
    calc
      _ = ∏ p ∈ liftPrimeSet s, f p.val :=
        Finset.prod_congr rfl (fun p hp => if_pos ((he p).mp hp))
      _ = _ := Finset.prod_subtype_of_mem f hs

theorem finite_prime_set_sum (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (f : ℕ → ℝ) :
    Summable (fun p : Nat.Primes => if p.val ∈ s then f p.val else 0) ∧
    (∑' p : Nat.Primes, if p.val ∈ s then f p.val else 0)=∑ n ∈ s, f n := by
  have he := liftPrimeSet_mem s
  constructor
  · apply summable_of_ne_finset_zero (s := liftPrimeSet s)
    intro p hp
    exact if_neg (fun h => hp ((he p).mpr h))
  · rw [tsum_eq_sum (s := liftPrimeSet s) (fun p hp => if_neg (fun h => hp ((he p).mpr h)))]
    calc
      _ = ∑ p ∈ liftPrimeSet s, f p.val :=
        Finset.sum_congr rfl (fun p hp => if_pos ((he p).mp hp))
      _ = _ := Finset.sum_subtype_of_mem f hs

end NField.Alignment.CollisionAlignmentEnvelopeSet

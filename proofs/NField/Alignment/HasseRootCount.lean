/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-!
# Root counting from Hasse derivative vanishing

This is the multiplicity-to-degree step used in Stepanov's method. It works
in every characteristic, without replacing Hasse derivatives by ordinary
derivatives or dividing by factorials. The auxiliary polynomial must still
be constructed and proved nonzero before these bounds can count points.
-/

set_option autoImplicit false
namespace NField.Alignment.HasseRootCount

open scoped BigOperators
open Polynomial

/-- Vanishing through order `n-1` is exactly divisibility by `(X-a)^n`,
including the zero polynomial and order zero. -/
theorem pow_X_sub_C_dvd_iff_hasse_eval_eq_zero {R : Type*} [CommRing R]
    (p : R[X]) (a : R) (n : ℕ) :
    (X - C a) ^ n ∣ p ↔ ∀ k < n, (hasseDeriv k p).eval a = 0 := by
  rw [X_sub_C_pow_dvd_iff, X_pow_dvd_iff]
  change (∀ k < n, (taylor a p).coeff k = 0) ↔ _
  simp only [taylor_coeff]

/-- For a nonzero polynomial, Hasse vanishing detects its root multiplicity. -/
theorem le_rootMultiplicity_iff_hasse_eval_eq_zero {R : Type*} [CommRing R]
    (p : R[X]) (hp : p ≠ 0) (a : R) (n : ℕ) :
    n ≤ p.rootMultiplicity a ↔ ∀ k < n, (hasseDeriv k p).eval a = 0 := by
  rw [le_rootMultiplicity_iff hp, pow_X_sub_C_dvd_iff_hasse_eval_eq_zero]

/-- Prescribed orders of vanishing at distinct points consume at least
their sum in degree. The nonzero premise is essential. -/
theorem sum_orders_le_natDegree {R : Type*} [CommRing R] [IsDomain R]
    (p : R[X]) (hp : p ≠ 0) (s : Finset R) (order : R → ℕ)
    (hvanish : ∀ a ∈ s, ∀ k < order a, (hasseDeriv k p).eval a = 0) :
    ∑ a ∈ s, order a ≤ p.natDegree := by
  classical
  calc
    ∑ a ∈ s, order a ≤ ∑ a ∈ s, p.rootMultiplicity a := by
      apply Finset.sum_le_sum
      intro a ha
      exact (le_rootMultiplicity_iff_hasse_eval_eq_zero p hp a (order a)).2
        (hvanish a ha)
    _ = ∑ a ∈ s, p.roots.count a := by simp only [count_roots]
    _ ≤ ∑ a ∈ s ∪ p.roots.toFinset, p.roots.count a :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_left) (by
        intro a _ _; exact Nat.zero_le _)
    _ = p.roots.card := Multiset.sum_count_eq_card (by
      intro a ha
      exact Finset.mem_union_right _ (Multiset.mem_toFinset.mpr ha))
    _ ≤ p.natDegree := card_roots' p

/-- Uniform vanishing of the first `n` Hasse derivatives bounds the number
of distinct points by degree divided by multiplicity, without division. -/
theorem card_mul_order_le_natDegree {R : Type*} [CommRing R] [IsDomain R]
    (p : R[X]) (hp : p ≠ 0) (s : Finset R) (n : ℕ)
    (hvanish : ∀ a ∈ s, ∀ k < n, (hasseDeriv k p).eval a = 0) :
    s.card * n ≤ p.natDegree := by
  simpa using sum_orders_le_natDegree p hp s (fun _ => n) hvanish

end NField.Alignment.HasseRootCount

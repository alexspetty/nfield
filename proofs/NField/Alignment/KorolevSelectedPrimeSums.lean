/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevPrimeWindows
import NField.Alignment.KorolevCanonicalPrimeSlices

/-! # Exact additive decompositions of both selected prime families

The P family consists of separated windows. The Q family is a contiguous
interval partitioned at consecutive upper endpoints. Arbitrary additive
summands may retain the global canonical cutoffs inside these sums.
-/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevSelectedPrimeSums
open KorolevPrimeWindows KorolevPrimeIntervals KorolevCanonicalPrimeSlices
open scoped BigOperators Classical

/-- Disjoint selected P windows permit any additive summand. -/
theorem sum_selected {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    {L : ℝ} (hL : 0 ≤ L) {a b : ℕ} (ha : 1 ≤ a) :
    ∑ p ∈ selectedPrimes L a b, f p =
      ∑ k ∈ Finset.Icc a b, ∑ p ∈ windowPrimes L k, f p := by
  unfold selectedPrimes
  apply Finset.sum_biUnion
  intro i hi j hj hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact window_disjoint hL (ha.trans (Finset.mem_Icc.mp hi).1) h
  · exact (window_disjoint hL (ha.trans (Finset.mem_Icc.mp hj).1) h).symm

/-- Open lower and closed upper endpoints split a prime interval exactly. -/
theorem interval_split {l t u : ℝ} (hlt : l ≤ t) (htu : t ≤ u) :
    intervalPrimes l u = intervalPrimes t u ∪ intervalPrimes l t := by
  ext p
  simp only [Finset.mem_union, intervalPrimes_mem]
  constructor
  · rintro ⟨hp, hlo, hhi⟩
    by_cases h : t < (p : ℝ)
    · exact Or.inl ⟨hp, h, hhi⟩
    · exact Or.inr ⟨hp, hlo, le_of_not_gt h⟩
  · rintro (⟨hp, hlo, hhi⟩ | ⟨hp, hlo, hhi⟩)
    · exact ⟨hp, hlt.trans_lt hlo, hhi⟩
    · exact ⟨hp, hlo, hhi.trans htu⟩

/-- The splitting intervals have no common prime, including at the breakpoint. -/
theorem interval_split_disjoint (l t u : ℝ) :
    Disjoint (intervalPrimes t u) (intervalPrimes l t) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact (not_lt_of_ge (intervalPrimes_mem.mp hq).2.2) (intervalPrimes_mem.mp hp).2.1

/-- The entire contiguous Q interval is the sum of its consecutive steps. -/
theorem sum_contiguous_range {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    {L : ℝ} (hL : 0 ≤ L) {a : ℕ} (ha : 1 ≤ a) (n : ℕ) :
    ∑ q ∈ intervalPrimes (upperEndpoint L (a+n)) (upperEndpoint L a), f q =
      ∑ i ∈ Finset.range n,
        ∑ q ∈ intervalPrimes (upperEndpoint L (a+i+1)) (upperEndpoint L (a+i)), f q := by
  induction n with
  | zero =>
    have hempty : intervalPrimes (upperEndpoint L a) (upperEndpoint L a) = ∅ := by
      ext p
      simp only [intervalPrimes_mem, Finset.notMem_empty, iff_false]
      intro h
      exact (not_lt_of_ge h.2.2) h.2.1
    simp [hempty]
  | succ n ih =>
    have hlow := upper_antitone hL (by omega : 1 ≤ a+n) (by omega : a+n ≤ a+(n+1))
    have hhi := upper_antitone hL ha (by omega : a ≤ a+n)
    rw [interval_split hlow hhi, Finset.sum_union (interval_split_disjoint _ _ _), ih,
      Finset.sum_range_succ]
    rfl

/-- The literal first/last convention includes every Q step exactly once. -/
theorem sum_contiguous {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    {L : ℝ} (hL : 0 ≤ L) {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ q ∈ intervalPrimes (upperEndpoint L (b+1)) (upperEndpoint L a), f q =
      ∑ s ∈ Finset.Icc a b,
        ∑ q ∈ intervalPrimes (upperEndpoint L (s+1)) (upperEndpoint L s), f q := by
  rw [show Finset.Icc a b = Finset.Ico a (b+1) by ext s; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega,
    Finset.sum_Ico_eq_sum_range]
  have he : a+(b+1-a) = b+1 := by omega
  simpa only [he, Nat.add_comm] using sum_contiguous_range f hL ha (b+1-a)

/-- Rectangular sums split over separated P windows and contiguous Q steps. -/
theorem double_sum_windows {M : Type*} [AddCommMonoid M] (f : ℕ → ℕ → M)
    {L : ℝ} (hL : 0 ≤ L) {a b c d : ℕ} (ha : 1 ≤ a) (hc : 1 ≤ c) (hcd : c ≤ d) :
    (∑ p ∈ selectedPrimes L a b,
      ∑ q ∈ intervalPrimes (upperEndpoint L (d+1)) (upperEndpoint L c), f p q) =
      ∑ k ∈ Finset.Icc a b, ∑ s ∈ Finset.Icc c d,
        ∑ p ∈ windowPrimes L k,
          ∑ q ∈ intervalPrimes (upperEndpoint L (s+1)) (upperEndpoint L s), f p q := by
  rw [sum_selected _ hL ha]
  apply Finset.sum_congr rfl
  intro k hk
  simp_rw [sum_contiguous _ hL hc hcd]
  exact Finset.sum_comm

/-- Global ambient cutoffs survive decomposition into the actual source windows. -/
theorem primeSliceOn_windows {G : Type*} [AddCommMonoid G]
    (P Q : Finset ℕ) (l h X m : ℕ) (f : ℕ → G)
    {L : ℝ} (hL : 0 ≤ L) {a b c d : ℕ} (ha : 1 ≤ a) (hc : 1 ≤ c) (hcd : c ≤ d) :
    primeSliceOn P Q (selectedPrimes L a b)
      (intervalPrimes (upperEndpoint L (d+1)) (upperEndpoint L c)) l h X m f =
      ∑ k ∈ Finset.Icc a b, ∑ s ∈ Finset.Icc c d,
        primeSliceOn P Q (windowPrimes L k)
          (intervalPrimes (upperEndpoint L (s+1)) (upperEndpoint L s)) l h X m f := by
  unfold primeSliceOn
  exact double_sum_windows _ hL ha hc hcd

/-- The full canonical tuple sum has the literal source-family window decomposition. -/
theorem sum_tuples_eq_windows {G : Type*} [AddCommMonoid G]
    (P Q : Finset ℕ) (B X m : ℕ) (f : ℕ → G)
    {L : ℝ} (hL : 0 ≤ L) {a b c d : ℕ} (ha : 1 ≤ a) (hc : 1 ≤ c) (hcd : c ≤ d)
    (hP : P = selectedPrimes L a b)
    (hQ : Q = intervalPrimes (upperEndpoint L (d+1)) (upperEndpoint L c)) :
    (∑ t ∈ (KorolevCanonicalTuples.tuples P Q B X).filter
      (fun t => (KorolevCanonicalTuples.value t).Coprime m),
      f (KorolevCanonicalTuples.value t)) =
      ∑ l ∈ (Finset.Icc 1 B).filter (fun l => l.Coprime m),
        ∑ h ∈ (Finset.Icc 1 X).filter (fun h => Squarefree h ∧ h.Coprime m),
          ∑ k ∈ Finset.Icc a b, ∑ s ∈ Finset.Icc c d,
            primeSliceOn P Q (windowPrimes L k)
              (intervalPrimes (upperEndpoint L (s+1)) (upperEndpoint L s)) l h X m f := by
  rw [sum_tuples_eq_slices]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro h hh
  simpa only [← hP, ← hQ, primeSlice] using
    primeSliceOn_windows P Q l h X m f (b := b) hL ha hc hcd

end NField.Alignment.KorolevSelectedPrimeSums

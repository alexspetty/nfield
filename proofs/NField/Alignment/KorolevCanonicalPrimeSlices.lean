/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevCanonicalTuples
import NField.Alignment.KorolevLogarithmicPartition

/-! # Exact canonical prime slices and their logarithmic block decomposition -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevCanonicalPrimeSlices
open KorolevCanonicalTuples KorolevCanonicalPrimeFactors KorolevLogarithmicPartition
open scoped BigOperators Classical

/-- The ambient families retain their canonical cutoffs when the summation domains shrink. -/
def primeSliceOn {G : Type*} [AddCommMonoid G] (P Q P₀ Q₀ : Finset ℕ)
    (l h X m : ℕ) (f : ℕ → G) : G :=
  ∑ p ∈ P₀, ∑ q ∈ Q₀,
    if p.Coprime m ∧ Cutoff P h p ∧ q.Coprime m ∧ Cutoff Q h q ∧ l^2*p*q*h ≤ X
    then f (l^2*p*q*h) else 0

/-- The complete prime slice has the original prime families as both ambient sets and domains. -/
def primeSlice {G : Type*} [AddCommMonoid G] (P Q : Finset ℕ)
    (l h X m : ℕ) (f : ℕ → G) : G := primeSliceOn P Q P Q l h X m f

/-- Fixed square/residual slicing keeps every canonical predicate and the product cutoff. -/
theorem sum_tuples_eq_slices {G : Type*} [AddCommMonoid G]
    (P Q : Finset ℕ) (L X m : ℕ) (f : ℕ → G) :
    (∑ t ∈ (tuples P Q L X).filter (fun t => (value t).Coprime m), f (value t)) =
      ∑ l ∈ (Finset.Icc 1 L).filter (fun l => l.Coprime m),
        ∑ h ∈ (Finset.Icc 1 X).filter (fun h => Squarefree h ∧ h.Coprime m),
          primeSlice P Q l h X m f := by
  rw [Finset.sum_filter]
  unfold tuples
  rw [Finset.sum_filter]
  simp only [Finset.product_eq_sprod, Finset.sum_product]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro l hl
  have hswap (F : ℕ → ℕ → ℕ → G) :
      (∑ p ∈ P, ∑ q ∈ Q, ∑ h ∈ Finset.Icc 1 X, F p q h) =
        ∑ h ∈ Finset.Icc 1 X, ∑ p ∈ P, ∑ q ∈ Q, F p q h := by
    simp_rw [Finset.sum_comm (s := Q) (t := Finset.Icc 1 X)]
    rw [Finset.sum_comm]
  rw [hswap]
  by_cases hlc : l.Coprime m
  · rw [if_pos hlc]
    apply Finset.sum_congr rfl
    intro h hh
    by_cases hsq : Squarefree h
    · by_cases hhc : h.Coprime m
      · rw [if_pos ⟨hsq, hhc⟩]
        simp only [hsq, true_and, primeSlice, primeSliceOn]
        apply Finset.sum_congr rfl
        intro p hp
        apply Finset.sum_congr rfl
        intro q hq
        simp only [value, Nat.coprime_mul_iff_left,
          Nat.coprime_pow_left_iff (by norm_num : 0 < 2)]
        split_ifs <;> simp_all
      · simp [value, Nat.coprime_mul_iff_left, hhc, hsq]
    · simp [hsq]
  · simp [value, Nat.coprime_mul_iff_left,
      Nat.coprime_pow_left_iff (by norm_num : 0 < 2), hlc]

/-- Exact rectangular summation across the two disjoint logarithmic partitions. -/
theorem double_sum_blocks {G : Type*} [AddCommMonoid G] (f : ℕ → ℕ → G)
    (lp lq : ℝ) {Dp Dq A : ℝ} (hA : 0 < A) (hDp : A ≤ Dp) (hDq : A ≤ Dq) :
    (∑ p ∈ KorolevPrimeIntervals.intervalPrimes (Real.exp lp) (Real.exp (lp+Dp)),
      ∑ q ∈ KorolevPrimeIntervals.intervalPrimes (Real.exp lq) (Real.exp (lq+Dq)), f p q) =
      ∑ i ∈ Finset.range (blockCount Dp A), ∑ j ∈ Finset.range (blockCount Dq A),
        ∑ p ∈ block lp Dp A i, ∑ q ∈ block lq Dq A j, f p q := by
  rw [sum_blocks (fun p => ∑ q ∈ KorolevPrimeIntervals.intervalPrimes
    (Real.exp lq) (Real.exp (lq+Dq)), f p q) lp hA hDp]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    _ = ∑ p ∈ block lp Dp A i, ∑ j ∈ Finset.range (blockCount Dq A),
        ∑ q ∈ block lq Dq A j, f p q := by
      apply Finset.sum_congr rfl
      intro p hp
      exact sum_blocks (f p) lq hA hDq
    _ = _ := Finset.sum_comm

/-- Block decomposition preserves the ambient canonical cutoffs and the coupled product cutoff. -/
theorem primeSliceOn_blocks {G : Type*} [AddCommMonoid G]
    (P Q : Finset ℕ) (l h X m : ℕ) (f : ℕ → G) (lp lq : ℝ)
    {Dp Dq A : ℝ} (hA : 0 < A) (hDp : A ≤ Dp) (hDq : A ≤ Dq) :
    primeSliceOn P Q
      (KorolevPrimeIntervals.intervalPrimes (Real.exp lp) (Real.exp (lp+Dp)))
      (KorolevPrimeIntervals.intervalPrimes (Real.exp lq) (Real.exp (lq+Dq))) l h X m f =
      ∑ i ∈ Finset.range (blockCount Dp A), ∑ j ∈ Finset.range (blockCount Dq A),
        primeSliceOn P Q (block lp Dp A i) (block lq Dq A j) l h X m f := by
  unfold primeSliceOn
  exact double_sum_blocks _ lp lq hA hDp hDq

/-- The canonical prime slice splits over blocks without redefining its ambient cutoffs. -/
theorem primeSlice_eq_blocks {G : Type*} [AddCommMonoid G]
    (P Q : Finset ℕ) (l h X m : ℕ) (f : ℕ → G) (lp lq : ℝ)
    {Dp Dq A : ℝ} (hA : 0 < A) (hDp : A ≤ Dp) (hDq : A ≤ Dq)
    (hP : P = KorolevPrimeIntervals.intervalPrimes (Real.exp lp) (Real.exp (lp+Dp)))
    (hQ : Q = KorolevPrimeIntervals.intervalPrimes (Real.exp lq) (Real.exp (lq+Dq))) :
    primeSlice P Q l h X m f =
      ∑ i ∈ Finset.range (blockCount Dp A), ∑ j ∈ Finset.range (blockCount Dq A),
        primeSliceOn P Q (block lp Dp A i) (block lq Dq A j) l h X m f := by
  simpa only [← hP, ← hQ, primeSlice] using primeSliceOn_blocks P Q l h X m f lp lq hA hDp hDq

/-- The full unit-filtered canonical tuple sum is exactly a sum of cutoff-preserving blocks. -/
theorem sum_tuples_eq_blocks {G : Type*} [AddCommMonoid G]
    (P Q : Finset ℕ) (L X m : ℕ) (f : ℕ → G) (lp lq : ℝ)
    {Dp Dq A : ℝ} (hA : 0 < A) (hDp : A ≤ Dp) (hDq : A ≤ Dq)
    (hP : P = KorolevPrimeIntervals.intervalPrimes (Real.exp lp) (Real.exp (lp+Dp)))
    (hQ : Q = KorolevPrimeIntervals.intervalPrimes (Real.exp lq) (Real.exp (lq+Dq))) :
    (∑ t ∈ (tuples P Q L X).filter (fun t => (value t).Coprime m), f (value t)) =
      ∑ l ∈ (Finset.Icc 1 L).filter (fun l => l.Coprime m),
        ∑ h ∈ (Finset.Icc 1 X).filter (fun h => Squarefree h ∧ h.Coprime m),
          ∑ i ∈ Finset.range (blockCount Dp A), ∑ j ∈ Finset.range (blockCount Dq A),
            primeSliceOn P Q (block lp Dp A i) (block lq Dq A j) l h X m f := by
  rw [sum_tuples_eq_slices]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro h hh
  exact primeSlice_eq_blocks P Q l h X m f lp lq hA hDp hDq hP hQ

end NField.Alignment.KorolevCanonicalPrimeSlices

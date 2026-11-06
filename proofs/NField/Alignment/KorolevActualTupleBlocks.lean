/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevActualPrimeBlocks
import NField.Alignment.KorolevSelectedPrimeSums

/-! # Exact source-window and block expansion with residual sums innermost -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevActualTupleBlocks
open KorolevPrimeWindows KorolevPrimeIntervals KorolevActualPrimeBlocks
  KorolevLogarithmicPartition KorolevCanonicalPrimeSlices KorolevCanonicalTuples
  KorolevSelectedPrimeSums
open scoped BigOperators Classical

/-- Literal source-window slices split into their actual logarithmic blocks. -/
theorem slice_blocks {G : Type*} [AddCommMonoid G]
    (P Q : Finset ℕ) (l h X m : ℕ) (f : ℕ → G) (L : ℝ) (k s : ℕ)
    {A : ℝ} (hA : 0 < A) (hDp : A ≤ pWidth L k) (hDq : A ≤ qWidth L s) :
    primeSliceOn P Q (windowPrimes L k)
      (intervalPrimes (upperEndpoint L (s+1)) (upperEndpoint L s)) l h X m f =
      ∑ i ∈ Finset.range (blockCount (pWidth L k) A),
        ∑ j ∈ Finset.range (blockCount (qWidth L s) A),
          primeSliceOn P Q (block (pLog L k) (pWidth L k) A i)
            (block (qLog L s) (qWidth L s) A j) l h X m f := by
  have hh := primeSliceOn_blocks P Q l h X m f (pLog L k) (qLog L s) hA hDp hDq
  rw [(p_endpoints L k).1, (p_endpoints L k).2,
    (q_endpoints L s).1, (q_endpoints L s).2] at hh
  exact hh

/-- The actual canonical tuple sum expands without overcounting, keeping residual sums innermost. -/
theorem sum_tuples_eq_blocks {G : Type*} [AddCommMonoid G]
    (P Q : Finset ℕ) (B X m : ℕ) (f : ℕ → G)
    {L A : ℝ} (hL : 0 ≤ L) (hA : 0 < A) {a b c d : ℕ}
    (ha : 1 ≤ a) (hc : 1 ≤ c) (hcd : c ≤ d)
    (hP : P = selectedPrimes L a b)
    (hQ : Q = intervalPrimes (upperEndpoint L (d+1)) (upperEndpoint L c))
    (hDp : ∀ k ∈ Finset.Icc a b, A ≤ pWidth L k)
    (hDq : ∀ s ∈ Finset.Icc c d, A ≤ qWidth L s) :
    (∑ t ∈ (tuples P Q B X).filter (fun t => (value t).Coprime m), f (value t)) =
      ∑ l ∈ (Finset.Icc 1 B).filter (fun l => l.Coprime m),
        ∑ k ∈ Finset.Icc a b, ∑ s ∈ Finset.Icc c d,
          ∑ i ∈ Finset.range (blockCount (pWidth L k) A),
            ∑ j ∈ Finset.range (blockCount (qWidth L s) A),
              ∑ h ∈ (Finset.Icc 1 X).filter (fun h => Squarefree h ∧ h.Coprime m),
                primeSliceOn P Q (block (pLog L k) (pWidth L k) A i)
                  (block (qLog L s) (qWidth L s) A j) l h X m f := by
  rw [sum_tuples_eq_windows P Q B X m f hL ha hc hcd hP hQ]
  apply Finset.sum_congr rfl
  intro l hl
  have hslice (h : ℕ) :
      (∑ k ∈ Finset.Icc a b, ∑ s ∈ Finset.Icc c d,
        primeSliceOn P Q (windowPrimes L k)
          (intervalPrimes (upperEndpoint L (s+1)) (upperEndpoint L s)) l h X m f) =
      ∑ k ∈ Finset.Icc a b, ∑ s ∈ Finset.Icc c d,
        ∑ i ∈ Finset.range (blockCount (pWidth L k) A),
          ∑ j ∈ Finset.range (blockCount (qWidth L s) A),
            primeSliceOn P Q (block (pLog L k) (pWidth L k) A i)
              (block (qLog L s) (qWidth L s) A j) l h X m f := by
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro s hs
    exact slice_blocks P Q l h X m f L k s hA (hDp k hk) (hDq s hs)
  simp_rw [hslice]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  exact Finset.sum_comm

end NField.Alignment.KorolevActualTupleBlocks

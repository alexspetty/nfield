/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.SpectralRepulsion

/-! # Actual ordered prime representations and the reflected sign -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.ReflectedPrimePairs
open scoped BigOperators
open SpectralRepulsion

abbrev OrderedPrimePair (N : ℕ) :=
  {pq : Fin (N + 1) × Fin (N + 1) //
    pq.1.val.Prime ∧ pq.2.val.Prime ∧ pq.1.val + pq.2.val = N}

def weightedGoldbach {m : ℕ} (f : ZMod m → ℝ) (N : ℕ) : ℝ :=
  ∑ pq : OrderedPrimePair N, f pq.val.1.val * f pq.val.2.val

theorem residue_reflection {m N : ℕ} (hN : m ∣ N) (pq : OrderedPrimePair N) :
    (pq.val.2.val : ZMod m) = -(pq.val.1.val : ZMod m) := by
  have hsum : (pq.val.1.val : ZMod m) + (pq.val.2.val : ZMod m) = 0 := by
    rw [← Nat.cast_add, pq.property.2.2]
    exact (ZMod.natCast_eq_zero_iff N m).mpr hN
  exact eq_neg_of_add_eq_zero_right hsum

theorem term_eq_neg_square {m N : ℕ} (f : ZMod m → ℝ)
    (hodd : ∀ a, f (-a) = -f a) (hN : m ∣ N) (pq : OrderedPrimePair N) :
    f pq.val.1.val * f pq.val.2.val = -(f pq.val.1.val) ^ 2 := by
  rw [residue_reflection hN pq, hodd]
  ring

theorem weightedGoldbach_eq_neg_squares {m N : ℕ} (f : ZMod m → ℝ)
    (hodd : ∀ a, f (-a) = -f a) (hN : m ∣ N) :
    weightedGoldbach f N = -(∑ pq : OrderedPrimePair N, (f pq.val.1.val) ^ 2) := by
  unfold weightedGoldbach
  simp_rw [term_eq_neg_square f hodd hN]
  rw [Finset.sum_neg_distrib]

theorem weightedGoldbach_nonpos {m N : ℕ} (f : ZMod m → ℝ)
    (hodd : ∀ a, f (-a) = -f a) (hN : m ∣ N) : weightedGoldbach f N ≤ 0 := by
  rw [weightedGoldbach_eq_neg_squares f hodd hN]
  exact neg_nonpos.mpr (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem weightedGoldbach_strict {m N : ℕ} (f : ZMod m → ℝ)
    (hodd : ∀ a, f (-a) = -f a) (hN : m ∣ N)
    (hw : ∃ pq : OrderedPrimePair N, f pq.val.1.val ≠ 0) : weightedGoldbach f N < 0 := by
  rw [weightedGoldbach_eq_neg_squares f hodd hN, neg_lt_zero]
  obtain ⟨pq, hpq⟩ := hw
  exact Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨pq, Finset.mem_univ _, sq_pos_of_ne_zero hpq⟩

theorem selfConvolution_strict {m : ℕ} [NeZero m] (f : ZMod m → ℝ)
    (hodd : ∀ a, f (-a) = -f a) (hw : ∃ a, f a ≠ 0) :
    additiveSelfConvolution f 0 < 0 := by
  rw [additiveSelfConvolution_zero f hodd, neg_lt_zero]
  obtain ⟨a, ha⟩ := hw
  exact Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨a, Finset.mem_univ _, sq_pos_of_ne_zero ha⟩

end NField.Alignment.ReflectedPrimePairs

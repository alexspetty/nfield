/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionFiniteActivationMixture

/-!
# Exact pair counts by return-time gap

The ordered-pair identity counts the coefficient N-h in the stationary
second-moment recurrence. No independence of the events is assumed.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionReturnPairCounting

open scoped BigOperators Classical

def strictPairSum (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ i∈Finset.range N, ∑ j∈Finset.range N, if i<j then a (j-i) else 0

def weightedGapSum (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ h∈Finset.range N, ((N-(h+1) : ℕ) : ℝ)*a (h+1)

theorem strictPairSum_succ (a : ℕ → ℝ) (N : ℕ) :
    strictPairSum a (N+1)=strictPairSum a N+∑ i∈Finset.range N, a (N-i) := by
  have hz : (∑ j∈Finset.range N, if N<j then a (j-N) else 0)=0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [if_neg (by have := Finset.mem_range.mp hj; omega)]
  unfold strictPairSum
  rw [Finset.sum_range_succ]
  simp_rw [Finset.sum_range_succ]
  rw [if_neg (lt_irrefl N),hz,add_zero,add_zero,Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [if_pos (Finset.mem_range.mp hi)]

theorem reverse_gap_sum (a : ℕ → ℝ) (N : ℕ) :
    (∑ i∈Finset.range N, a (N-i))=∑ j∈Finset.range N, a (j+1) := by
  have ht := Finset.sum_range_reflect (fun j => a (j+1)) N
  calc
    _ = ∑ i∈Finset.range N, a (N-1-i+1) := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      have := Finset.mem_range.mp hi
      omega
    _ = _ := ht

theorem weightedGapSum_succ (a : ℕ → ℝ) (N : ℕ) :
    weightedGapSum a (N+1)=weightedGapSum a N+∑ i∈Finset.range N, a (i+1) := by
  unfold weightedGapSum
  rw [Finset.sum_range_succ]
  simp only [Nat.sub_self,Nat.cast_zero,zero_mul,add_zero]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have he : N+1-(i+1)=(N-(i+1))+1 := by have := Finset.mem_range.mp hi; omega
  rw [he,Nat.cast_add,Nat.cast_one]
  ring

theorem strict_pair_gap_identity (a : ℕ → ℝ) (N : ℕ) : strictPairSum a N=weightedGapSum a N := by
  induction N with
  | zero => simp [strictPairSum,weightedGapSum]
  | succ N ih => rw [strictPairSum_succ,weightedGapSum_succ,ih,reverse_gap_sum]

theorem weightedGapSum_Icc (a : ℕ → ℝ) (N : ℕ) :
    weightedGapSum a N=∑ h∈Finset.Icc 1 (N-1), ((N : ℝ)-(h : ℝ))*a h := by
  have he : weightedGapSum a N=∑ h∈Finset.Icc 1 N, ((N-h : ℕ) : ℝ)*a h := by
    rw [← Finset.Ico_add_one_right_eq_Icc,Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    unfold weightedGapSum
    apply Finset.sum_congr rfl
    intro h _
    rw [Nat.add_comm 1 h]
  rw [he]
  by_cases hN : N=0
  · subst N
    simp
  have hn : N-1+1=N := by omega
  rw [← hn,Finset.sum_Icc_succ_top (by omega : 1≤N-1+1)]
  simp only [hn,Nat.sub_self,Nat.cast_zero,zero_mul,add_zero]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Nat.cast_sub (by have := (Finset.mem_Icc.mp hh).2; omega)]

end NField.Alignment.CollisionReturnPairCounting

/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.DedekindAbelRemainder

/-! # Finite partial summation for increasing conductor amplitudes -/

noncomputable section

namespace NField.Alignment.CommonResetLocalAbel

open scoped BigOperators

theorem sum_truncated_prefix {R : Type*} [AddCommMonoid R] (g : ℕ → R) (N n : ℕ) :
    (∑ i ∈ Finset.range n, if i < N then g i else 0) = ∑ i ∈ Finset.range (min n N), g i := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext i
    simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
  · intro i _
    rfl

/-- Title: `Increasing finite amplitudes cost at most three times their supremum in partial summation`. -/
theorem monotone_weighted_interval (w : ℕ → ℝ) (g : ℕ → ℂ) (N : ℕ) (W M : ℝ)
    (hW : 0 ≤ W) (hM : 0 ≤ M)
    (hw : ∀ i < N, 0 ≤ w i ∧ w i ≤ W)
    (hmono : ∀ i j, i ≤ j → j < N → w i ≤ w j)
    (hprefix : ∀ n ≤ N, ‖∑ i ∈ Finset.range n, g i‖ ≤ M) :
    ‖∑ i ∈ Finset.range N, (w i : ℂ)*g i‖ ≤ 3*W*M := by
  classical
  by_cases hN : N=0
  · subst N
    simp only [Finset.range_zero, Finset.sum_empty, norm_zero]
    positivity
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  let v (i : ℕ) : ℝ := W-w (min i (N-1))
  let G (i : ℕ) : ℂ := if i < N then g i else 0
  have hv0 (i : ℕ) : 0 ≤ v i := by
    exact sub_nonneg.mpr (hw _ (by have := min_le_right i (N-1); omega)).2
  have hv : Antitone v := by
    intro i j hij
    dsimp [v]
    exact sub_le_sub (le_refl _) (hmono _ _ (min_le_min_right _ hij)
      (by have := min_le_right j (N-1); omega))
  have hG (n : ℕ) : ‖∑ i ∈ Finset.range n, G i‖ ≤ M := by
    rw [show (∑ i ∈ Finset.range n, G i) =
      ∑ i ∈ Finset.range (min n N), g i from sum_truncated_prefix g N n]
    exact hprefix _ (min_le_right _ _)
  have habel := DedekindAbelRemainder.norm_antitone_weighted_sum_le v G hv0 hv M hM hG
    (s := 0) (t := N)
  simp only [← Finset.range_eq_Ico, Complex.real_smul] at habel
  have hvW : v 0 ≤ W := by
    dsimp [v]
    simp only [zero_min]
    linarith [(hw 0 hNpos).1]
  have hidentity : (∑ i ∈ Finset.range N, (w i : ℂ)*g i) =
      (W : ℂ)*(∑ i ∈ Finset.range N, G i) - ∑ i ∈ Finset.range N, (v i : ℂ)*G i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hiN := Finset.mem_range.mp hi
    simp only [G, if_pos hiN, v, min_eq_left (by omega : i ≤ N-1), Complex.ofReal_sub]
    ring
  rw [hidentity]
  calc
    _ ≤ ‖(W : ℂ)*(∑ i ∈ Finset.range N, G i)‖ + ‖∑ i ∈ Finset.range N, (v i : ℂ)*G i‖ :=
      norm_sub_le _ _
    _ ≤ W*M+2*v 0*M := by
      apply add_le_add _ habel
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hW]
      exact mul_le_mul_of_nonneg_left (hG N) hW
    _ ≤ W*M+2*W*M := by gcongr
    _ = _ := by ring

end NField.Alignment.CommonResetLocalAbel

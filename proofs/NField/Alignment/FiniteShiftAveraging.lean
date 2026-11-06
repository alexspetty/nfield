/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.RealPolynomialMomentBox

/-! # Bounded finite sums averaged over product shifts -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.FiniteShiftAveraging
open scoped BigOperators

theorem shift_difference_bound (f : ℕ → ℂ) (hf : ∀ i, ‖f i‖ ≤ 1) (M h : ℕ) :
    ‖(∑ i ∈ Finset.range M, f i)-(∑ i ∈ Finset.range M, f (i+h))‖ ≤ 2*h := by
  have he : (∑ i ∈ Finset.range M, f i)+(∑ i ∈ Finset.range h, f (M+i)) =
      (∑ i ∈ Finset.range h, f i)+(∑ i ∈ Finset.range M, f (i+h)) := by
    rw [← Finset.sum_range_add]
    simpa only [Nat.add_comm] using Finset.sum_range_add f h M
  have h₁ : ‖∑ i ∈ Finset.range h, f i‖ ≤ (h:ℝ) := by
    calc
      _ ≤ ∑ i ∈ Finset.range h, ‖f i‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ Finset.range h, (1:ℝ) := Finset.sum_le_sum fun i _ => hf i
      _ = _ := by simp
  have h₂ : ‖∑ i ∈ Finset.range h, f (M+i)‖ ≤ (h:ℝ) := by
    calc
      _ ≤ ∑ i ∈ Finset.range h, ‖f (M+i)‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ Finset.range h, (1:ℝ) := Finset.sum_le_sum fun i _ => hf (M+i)
      _ = _ := by simp
  have hd : (∑ i ∈ Finset.range M, f i)-(∑ i ∈ Finset.range M, f (i+h)) =
      (∑ i ∈ Finset.range h, f i)-(∑ i ∈ Finset.range h, f (M+i)) := by
    linear_combination he
  rw [hd]
  exact (norm_sub_le _ _).trans (by linarith)

theorem average_shift_bound {α : Type*} [Fintype α] (f : ℕ → ℂ)
    (hf : ∀ i, ‖f i‖ ≤ 1) (M : ℕ) (h : α → ℕ) (B : ℝ)
    (hh : ∀ a, (h a:ℝ) ≤ B) :
    (Fintype.card α:ℝ)*‖∑ i ∈ Finset.range M, f i‖ ≤
      ‖∑ i ∈ Finset.range M, ∑ a, f (i+h a)‖+2*Fintype.card α*B := by
  let S := ∑ i ∈ Finset.range M, f i
  let T := ∑ a : α, ∑ i ∈ Finset.range M, f (i+h a)
  have he : (Fintype.card α:ℂ)*S-T =
      ∑ a : α, (S-∑ i ∈ Finset.range M, f (i+h a)) := by
    rw [Finset.sum_sub_distrib]
    simp [T]
  have hd : ‖(Fintype.card α:ℂ)*S-T‖ ≤ 2*Fintype.card α*B := by
    rw [he]
    calc
      _ ≤ ∑ a : α, ‖S-∑ i ∈ Finset.range M, f (i+h a)‖ := norm_sum_le _ _
      _ ≤ ∑ _a : α, 2*B := Finset.sum_le_sum fun a _ =>
        (shift_difference_bound f hf M (h a)).trans (by nlinarith [hh a])
      _ = _ := by simp; ring
  rw [norm_sub_rev] at hd
  have ht : ‖(Fintype.card α:ℂ)*S‖ ≤ ‖T‖+2*Fintype.card α*B :=
    (norm_le_norm_add_norm_sub _ _).trans (add_le_add (le_refl _) hd)
  simp only [norm_mul, Complex.norm_natCast, S,T] at ht
  rw [Finset.sum_comm] at ht
  exact ht

end NField.Alignment.FiniteShiftAveraging

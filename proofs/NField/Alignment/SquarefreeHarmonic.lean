/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# A logarithmic lower bound from squarefree reciprocals

Every positive integer is a square times a positive squarefree integer.
Summing over those pairs and bounding the reciprocal-square sum by two
shows that the squarefree reciprocal sum dominates half the harmonic sum.
-/

noncomputable section
set_option autoImplicit false
open scoped BigOperators
open Finset

namespace NField.Alignment.SquarefreeHarmonic

/-- Positive squarefree integers up to the finite cutoff. -/
def squarefreeRange (N : ℕ) : Finset ℕ := (Icc 1 N).filter Squarefree

def reciprocalSum (N : ℕ) : ℝ := ∑ d ∈ squarefreeRange N, (d : ℝ)⁻¹

theorem harmonic_le_twice (N : ℕ) : (harmonic N : ℝ) ≤ 2 * reciprocalSum N := by
  let S := squarefreeRange N ×ˢ Icc 1 N
  let f : ℕ × ℕ → ℕ := fun ab => ab.2^2 * ab.1
  have hcover : Icc 1 N ⊆ S.image f := by
    intro n hn
    rcases mem_Icc.mp hn with ⟨hn0, hnN⟩
    rcases Nat.sq_mul_squarefree_of_pos hn0 with ⟨a, b, ha, hb, hab, hsf⟩
    have haN : a ≤ N := (Nat.le_of_dvd hn0 (show a ∣ n from
      ⟨b^2, by rw [← hab]; ring⟩)).trans hnN
    have hbN : b ≤ N := (Nat.le_of_dvd hn0 (show b ∣ n from
      ⟨b*a, by rw [← hab]; ring⟩)).trans hnN
    exact mem_image.mpr ⟨(a,b), mem_product.mpr
      ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨ha, haN⟩, hsf⟩,
        mem_Icc.mpr ⟨hb, hbN⟩⟩, hab⟩
  have hsq : (∑ b ∈ Icc 1 N, ((b : ℝ)^2)⁻¹) ≤ 2 := by
    have heq : Icc 1 N = Ioo 0 (N+1) := by ext b; simp only [mem_Icc, mem_Ioo]; omega
    rw [heq]
    simpa using (sum_Ioo_inv_sq_le (α := ℝ) 0 (N+1))
  have hnonneg : 0 ≤ reciprocalSum N := sum_nonneg (fun _ _ => by positivity)
  calc
    (harmonic N : ℝ) = ∑ n ∈ Icc 1 N, (n : ℝ)⁻¹ := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      rfl
    _ ≤ ∑ n ∈ S.image f, (n : ℝ)⁻¹ :=
      sum_le_sum_of_subset_of_nonneg hcover (fun _ _ _ => by positivity)
    _ ≤ ∑ ab ∈ S, (f ab : ℝ)⁻¹ :=
      sum_image_le_of_nonneg (fun _ _ => by positivity)
    _ = reciprocalSum N * ∑ b ∈ Icc 1 N, ((b : ℝ)^2)⁻¹ := by
      rw [show S = squarefreeRange N ×ˢ Icc 1 N from rfl, sum_product]
      simp only [f, Nat.cast_mul, Nat.cast_pow, mul_inv, reciprocalSum]
      rw [sum_mul]
      apply sum_congr rfl
      intro a ha
      rw [mul_sum]
      simp only [mul_comm]
    _ ≤ reciprocalSum N * 2 := mul_le_mul_of_nonneg_left hsq hnonneg
    _ = 2 * reciprocalSum N := by ring

theorem log_le_twice {z : ℝ} (hz : 0 ≤ z) :
    Real.log z ≤ 2 * reciprocalSum ⌊z⌋₊ :=
  (log_le_harmonic_floor z hz).trans (harmonic_le_twice _)

end NField.Alignment.SquarefreeHarmonic

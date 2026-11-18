/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib
/-! # The finite Schur estimate for the reset-grid transform

Mathlib's finite weighted Cauchy--Schwarz inequality supplies the row
estimate. Summing the actual columns gives the complete matrix bound.
-/

noncomputable section

namespace NField.ResetForests.ResetGrid

open scoped BigOperators

theorem complex_weighted_row_bound {ι : Type*} (s : Finset ι)
    (a c : ι → ℂ) :
    ‖∑ j ∈ s, a j*c j‖^2 ≤
      (∑ j ∈ s, ‖a j‖)*(∑ j ∈ s, ‖a j‖*‖c j‖^2) := by
  have ht : ‖∑ j ∈ s, a j*c j‖ ≤ ∑ j ∈ s, ‖a j‖*‖c j‖ := by
    simpa only [norm_mul] using norm_sum_le (s := s) (f := fun j => a j*c j)
  have hs : (∑ j ∈ s, ‖a j‖*‖c j‖)^2 ≤
      (∑ j ∈ s, ‖a j‖)*(∑ j ∈ s, ‖a j‖*‖c j‖^2) := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
      (fun j _ => norm_nonneg _) (fun j _ => by positivity)
    intro j _
    exact le_of_eq (by ring)
  exact (pow_le_pow_left₀ (norm_nonneg _) ht 2).trans hs

/-- All rows and columns are measured in their actual complete populations. -/
theorem finite_schur_bound {ι κ : Type*} (rows : Finset ι) (cols : Finset κ)
    (A : ι → κ → ℂ) (c : κ → ℂ) {R C : ℝ} (hR : 0 ≤ R) (_hC : 0 ≤ C)
    (hrow : ∀ i ∈ rows, (∑ j ∈ cols, ‖A i j‖) ≤ R)
    (hcol : ∀ j ∈ cols, (∑ i ∈ rows, ‖A i j‖) ≤ C) :
    (∑ i ∈ rows, ‖∑ j ∈ cols, A i j*c j‖^2) ≤
      R*C*(∑ j ∈ cols, ‖c j‖^2) := by
  calc
    _ ≤ ∑ i ∈ rows, (∑ j ∈ cols, ‖A i j‖)*
        (∑ j ∈ cols, ‖A i j‖*‖c j‖^2) :=
      Finset.sum_le_sum (fun i _ => complex_weighted_row_bound cols (A i) c)
    _ ≤ ∑ i ∈ rows, R*(∑ j ∈ cols, ‖A i j‖*‖c j‖^2) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right (hrow i hi) (by positivity)
    _ = R*(∑ j ∈ cols, (∑ i ∈ rows, ‖A i j‖)*‖c j‖^2) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ ≤ R*(∑ j ∈ cols, C*‖c j‖^2) := by
      apply mul_le_mul_of_nonneg_left _ hR
      exact Finset.sum_le_sum (fun j hj =>
        mul_le_mul_of_nonneg_right (hcol j hj) (sq_nonneg _))
    _ = _ := by rw [← Finset.mul_sum]; ring

end NField.ResetForests.ResetGrid

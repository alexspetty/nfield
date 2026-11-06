/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevActualTupleBlocks
import Mathlib.Analysis.PSeries

/-! # Summation cost of the exact canonical block decomposition -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevTupleBlockCount
open KorolevActualPrimeBlocks KorolevLogarithmicPartition
open scoped BigOperators Classical

/-- The unit filter cannot enlarge the positive reciprocal-square sum. -/
theorem square_sum_le_two (B m : ℕ) :
    (∑ l ∈ (Finset.Icc 1 B).filter (fun l => l.Coprime m), ((l : ℝ)^2)⁻¹) ≤ 2 := by
  have hsub := Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset (fun l => l.Coprime m) (Finset.Icc 1 B))
    (fun l _ _ => by positivity : ∀ l ∈ Finset.Icc 1 B,
      l ∉ (Finset.Icc 1 B).filter (fun l => l.Coprime m) → 0 ≤ ((l : ℝ)^2)⁻¹)
  have heq : Finset.Icc 1 B = Finset.Ioo 0 (B+1) := by
    ext l
    simp only [Finset.mem_Icc, Finset.mem_Ioo]
    omega
  apply hsub.trans
  rw [heq]
  simpa using (sum_Ioo_inv_sq_le (α := ℝ) 0 (B+1))

/-- Reciprocal-square decay sums all block residuals with their exact multiplicities. -/
theorem norm_nested_le (S T : Finset ℕ) (B m : ℕ) (np nq : ℕ → ℕ)
    (F : ℕ → ℕ → ℕ → ℕ → ℕ → ℂ) (D : ℝ) (hD : 0 ≤ D)
    (hF : ∀ l ∈ (Finset.Icc 1 B).filter (fun l => l.Coprime m),
      ∀ k ∈ S, ∀ s ∈ T, ∀ i ∈ Finset.range (np k), ∀ j ∈ Finset.range (nq s),
        ‖F l k s i j‖ ≤ D/(l : ℝ)^2) :
    ‖∑ l ∈ (Finset.Icc 1 B).filter (fun l => l.Coprime m),
      ∑ k ∈ S, ∑ s ∈ T, ∑ i ∈ Finset.range (np k), ∑ j ∈ Finset.range (nq s),
        F l k s i j‖ ≤
      2*D*(∑ k ∈ S, (np k : ℝ))*(∑ s ∈ T, (nq s : ℝ)) := by
  have hn : ‖∑ l ∈ (Finset.Icc 1 B).filter (fun l => l.Coprime m),
      ∑ k ∈ S, ∑ s ∈ T, ∑ i ∈ Finset.range (np k), ∑ j ∈ Finset.range (nq s), F l k s i j‖ ≤
      ∑ l ∈ (Finset.Icc 1 B).filter (fun l => l.Coprime m),
        ∑ k ∈ S, ∑ s ∈ T, ∑ i ∈ Finset.range (np k), ∑ j ∈ Finset.range (nq s),
          D/(l : ℝ)^2 := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro l hl
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro k hk
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro s hs
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i hi
    apply (norm_sum_le _ _).trans
    exact Finset.sum_le_sum (fun j hj => hF l hl k hk s hs i hi j hj)
  have hc (l : ℕ) :
      (∑ k ∈ S, ∑ s ∈ T, ∑ i ∈ Finset.range (np k), ∑ j ∈ Finset.range (nq s),
        D/(l : ℝ)^2) =
      D*(∑ k ∈ S, (np k : ℝ))*(∑ s ∈ T, (nq s : ℝ))*((l : ℝ)^2)⁻¹ := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm (s := T) (t := S)]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro s hs
    ring
  simp_rw [hc] at hn
  rw [← Finset.mul_sum] at hn
  have hcost : 0 ≤ D*(∑ k ∈ S, (np k : ℝ))*(∑ s ∈ T, (nq s : ℝ)) := by positivity
  calc
    _ ≤ D*(∑ k ∈ S, (np k : ℝ))*(∑ s ∈ T, (nq s : ℝ))*
        ∑ l ∈ (Finset.Icc 1 B).filter (fun l => l.Coprime m), ((l : ℝ)^2)⁻¹ := hn
    _ ≤ D*(∑ k ∈ S, (np k : ℝ))*(∑ s ∈ T, (nq s : ℝ))*2 :=
      mul_le_mul_of_nonneg_left (square_sum_le_two B m) hcost
    _ = _ := by ring

end NField.Alignment.KorolevTupleBlockCount

/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KaratsubaBilinearReduction

/-! # Cauchy-Schwarz on actual finite coordinate populations -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KaratsubaPopulationCauchy
open scoped BigOperators
open KaratsubaFiberEnergy

theorem sum_comp_eq_population_sum {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] (f : α → β) (h : β → ℝ) :
    (∑ x, h (f x)) = ∑ y, (fiberCount f y : ℝ) * h y := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ f (fun x => h (f x))]
  apply Finset.sum_congr rfl
  intro y _
  calc
    (∑ x ∈ Finset.univ with f x = y, h (f x)) =
        ∑ _x ∈ Finset.univ with f _x = y, h y := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    _ = _ := by simp [fiberCount, nsmul_eq_mul]

/-- The first factor is the exact collision energy of the coordinate map. -/
theorem population_cauchy {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] (f : α → β) (h : β → ℝ) :
    (∑ x, h (f x)) ^ 2 ≤
      (∑ y, (fiberCount f y : ℝ) ^ 2) * ∑ y, h y ^ 2 := by
  rw [sum_comp_eq_population_sum]
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun y => (fiberCount f y : ℝ)) h

end NField.Alignment.KaratsubaPopulationCauchy

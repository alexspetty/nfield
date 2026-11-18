/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.Readout
import Mathlib
/-! # Complete orthogonal source work and its signed covector

The complement is a source vector with its own work. It is not discarded.
The readout kills it only when that is an explicit property of the actual
observed span. These lemmas do not assert an arithmetic bound on the cost.
-/

noncomputable section

namespace NField.ResetForests.Core

open scoped BigOperators InnerProductSpace

variable {ι E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem orthogonal_work_sum (s : Finset ι) (v : ι → E)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪v i, v j⟫_ℝ = 0) :
    ‖∑ i ∈ s, v i‖^2 = ∑ i ∈ s, ‖v i‖^2 := by
  classical
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  apply Finset.sum_congr rfl
  intro i hi
  rw [inner_sum, Finset.sum_eq_single i]
  · exact real_inner_self_eq_norm_sq _
  · intro j hj hji
    exact ho i hi j hj (Ne.symm hji)
  · exact fun h => (h hi).elim

theorem complete_source_work (s : Finset ι) (v : ι → E) (c z : E)
    (hc : c = (∑ i ∈ s, v i)+z)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪v i, v j⟫_ℝ = 0)
    (hz : ∀ i ∈ s, ⟪v i, z⟫_ℝ = 0) :
    ‖c‖^2 = (∑ i ∈ s, ‖v i‖^2)+‖z‖^2 := by
  rw [hc, norm_add_sq_real, orthogonal_work_sum s v ho, sum_inner]
  have hzero : (∑ i ∈ s, ⟪v i, z⟫_ℝ) = 0 := Finset.sum_eq_zero hz
  rw [hzero]
  ring

/-- The full source pays for the observed signed readout and its complement. -/
theorem coherent_signed_bound (s : Finset ι) (v : ι → E) (c z : E)
    (f : E →ₗ[ℝ] ℝ)
    (hc : c = (∑ i ∈ s, v i)+z)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪v i, v j⟫_ℝ = 0)
    (hz : ∀ i ∈ s, ⟪v i, z⟫_ℝ = 0) (hfz : f z = 0) :
    |f c|^2 ≤ (∑ i ∈ s, ‖v i‖^2) *
        readoutCost s (fun i => ‖v i‖^2) (fun i => f (v i)) ∧
      (∑ i ∈ s, ‖v i‖^2) *
        readoutCost s (fun i => ‖v i‖^2) (fun i => f (v i)) ≤
      ‖c‖^2 * readoutCost s (fun i => ‖v i‖^2) (fun i => f (v i)) := by
  have hD : f c = ∑ i ∈ s, f (v i) := by
    rw [hc, map_add, map_sum, hfz, add_zero]
  have he : ∀ i ∈ s, 0 ≤ ‖v i‖^2 := fun i _ => sq_nonneg _
  have hd : ∀ i ∈ s, ‖v i‖^2 = 0 → f (v i) = 0 := by
    intro i _ hi
    have hv : v i = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (v i)])
    simp [hv]
  constructor
  · rw [sq_abs, hD]
    exact signed_readout_bound s _ _ he hd
  · apply mul_le_mul_of_nonneg_right _ (readout_cost_nonneg s _ _ he)
    rw [complete_source_work s v c z hc ho hz]
    exact le_add_of_nonneg_right (sq_nonneg _)

def sourceReadoutProjection (s : Finset ι) (v : ι → E) (f : E →ₗ[ℝ] ℝ) : E :=
  ∑ i ∈ s, (f (v i)/‖v i‖^2) • v i

/-- The cost is exactly the work of the covector's projection onto the
source-generated directions, with zero-work directions retained as zero. -/
theorem readout_projection_work (s : Finset ι) (v : ι → E) (f : E →ₗ[ℝ] ℝ)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪v i, v j⟫_ℝ = 0) :
    ‖sourceReadoutProjection s v f‖^2 =
      readoutCost s (fun i => ‖v i‖^2) (fun i => f (v i)) := by
  unfold sourceReadoutProjection
  rw [orthogonal_work_sum s _ (by
    intro i hi j hj hij
    simp [real_inner_smul_left, real_inner_smul_right, ho i hi j hj hij])]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hv : v i = 0
  · simp [hv]
  · have hn : ‖v i‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    field_simp

end NField.ResetForests.Core

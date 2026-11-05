/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperPathGrid
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Probability transfer through the partial-sum grid

Only subadditivity is used for the original law. Half-open cells are
disjoint for the comparison law. A closed-rectangle to half-open-rectangle
bound therefore transfers a path event to its two-unit enlargement.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperPathTransfer
open scoped BigOperators ENNReal
open MeasureTheory Set HarperPathGrid

theorem partialSum_measurable {n : ℕ} (j : Fin n) :
    Measurable (fun z : Fin n → ℝ => partialSum z j) :=
  (Finset.Iic j).measurable_sum (fun i _ => measurable_pi_apply i)

theorem pathEvent_measurable {n : ℕ} (u v : Fin n → ℝ) :
    MeasurableSet (pathEvent u v) := by
  have he : pathEvent u v = ⋂ j, {z | u j ≤ partialSum z j ∧ partialSum z j ≤ v j} := by
    ext z
    simp [pathEvent]
  rw [he]
  exact MeasurableSet.iInter (fun j =>
    (measurableSet_le measurable_const (partialSum_measurable j)).inter
    (measurableSet_le (partialSum_measurable j) measurable_const))

theorem gridCell_measurable {n : ℕ} (k : Fin n → ℤ) : MeasurableSet (gridCell k) :=
  (measurableSet_pi Set.countable_univ).mpr (Or.inl (fun _ _ => measurableSet_Ico))

theorem closedGridCell_measurable {n : ℕ} (k : Fin n → ℤ) :
    MeasurableSet (closedGridCell k) :=
  (measurableSet_pi Set.countable_univ).mpr (Or.inl (fun _ _ => measurableSet_Icc))

theorem path_probability_transfer {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ν : Measure (Fin n → ℝ)) (f : Ω → Fin n → ℝ)
    (u v : Fin n → ℝ) (C : ℝ≥0∞)
    (hrect : ∀ k ∈ selectedCells u v,
      μ (f ⁻¹' closedGridCell k) ≤ C*ν (gridCell k)) :
    μ (f ⁻¹' pathEvent u v) ≤ C*ν (pathEvent (fun j => u j-2) (fun j => v j+2)) := by
  have hd : Pairwise (fun k l : selectedCells u v =>
      Disjoint (gridCell k.val) (gridCell l.val)) := fun k l hkl =>
    gridCell_pairwise_disjoint n (show k.val ≠ l.val from
      fun h => hkl (Subtype.ext h))
  have hcover : (⋃ k : selectedCells u v, gridCell k.val) ⊆
      pathEvent (fun j => u j-2) (fun j => v j+2) := by
    intro z hz
    rcases Set.mem_iUnion.mp hz with ⟨k,hk⟩
    exact selected_cell_subset_expanded_path k.property
      (gridCell_subset_closedGridCell k.val hk)
  calc
    _ ≤ μ (f ⁻¹' ⋃ k : selectedCells u v, gridCell k.val) :=
      measure_mono (Set.preimage_mono (path_subset_selected_union u v))
    _ = μ (⋃ k : selectedCells u v, f ⁻¹' gridCell k.val) := by rw [Set.preimage_iUnion]
    _ ≤ ∑' k : selectedCells u v, μ (f ⁻¹' gridCell k.val) := measure_iUnion_le _
    _ ≤ ∑' k : selectedCells u v, C*ν (gridCell k.val) := ENNReal.tsum_le_tsum
      (fun k => (measure_mono (Set.preimage_mono
        (gridCell_subset_closedGridCell k.val))).trans (hrect k.val k.property))
    _ = C*∑' k : selectedCells u v, ν (gridCell k.val) := ENNReal.tsum_mul_left
    _ = C*ν (⋃ k : selectedCells u v, gridCell k.val) := by
      rw [measure_iUnion hd (fun k => gridCell_measurable k.val)]
    _ ≤ _ := mul_le_mul_right (measure_mono hcover) C

end NField.Alignment.HarperPathTransfer

/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CarryFiniteExampleDetails

/-! # The complete primitive odd packet in the nine-state example -/

noncomputable section
namespace NField.Alignment.CarryNineChannels
open scoped BigOperators Classical
open CollisionCharacterStructure CarryBoundarySpectra CarryNineCharacter
  CarryFiniteExamples CarryFiniteExampleDetails PrimitiveOddBoundaryMean

local instance : Fact (1 < 9) := ⟨by decide⟩

theorem chiNine_inverse_odd : (chiNine⁻¹).Odd := by
  change chiNine⁻¹ (-1 : ZMod 9) = -1
  rw [MulChar.inv_apply_eq_inv', show chiNine (-1 : ZMod 9) = -1 from chiNine_odd]
  norm_num

theorem chiNine_ne_inverse : chiNine ≠ chiNine⁻¹ := by
  intro he
  have hv := congrArg (fun χ : Character 9 => χ (2 : ZMod 9)) he
  rw [← MulChar.star_apply'] at hv
  have hr : sixthRoot = star sixthRoot := by
    change sixthRoot = star sixthRoot at hv
    exact hv
  have hi := congrArg Complex.im hr
  norm_num [sixthRoot] at hi
  have hpos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  linarith

/-- Title: `The two printed characters are the complete primitive odd packet modulo nine`. -/
theorem nine_primitive_odd_packet :
    ((Finset.univ : Finset (Character 9)).filter fun χ => χ.IsPrimitive ∧ χ.Odd) =
      {chiNine, chiNine⁻¹} := by
  let s := (Finset.univ : Finset (Character 9)).filter fun χ => χ.IsPrimitive ∧ χ.Odd
  have hc := primitiveOddCharacterCount_primePower (p := 3) (N := 2)
    (by decide) (by decide) (by decide)
  norm_num [show (9 : ℕ).totient = 6 by decide,
    show (3 : ℕ).totient = 2 by decide] at hc
  have hs : s.card = 2 := by exact_mod_cast hc
  have hsub : ({chiNine, chiNine⁻¹} : Finset (Character 9)) ⊆ s := by
    intro χ hχ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hχ
    rcases hχ with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, chiNine_primitive, chiNine_odd⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, inverse_isPrimitive chiNine_primitive, chiNine_inverse_odd⟩
  exact (Finset.eq_of_subset_of_card_le hsub (by simp [hs, chiNine_ne_inverse])).symm

/-- Title: `Each primitive odd coefficient in the modulus nine example has squared norm sixteen`. -/
theorem nine_all_primitive_coefficient_norms (χ : Character 9)
    (hχ : χ.IsPrimitive ∧ χ.Odd) : ‖carryTransform nineWeight χ‖ ^ 2 = 16 := by
  have hm : χ ∈ ((Finset.univ : Finset (Character 9)).filter fun ψ => ψ.IsPrimitive ∧ ψ.Odd) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hχ⟩
  rw [nine_primitive_odd_packet] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl
  · exact nine_primitive_coefficient_norms.1
  · exact nine_primitive_coefficient_norms.2

end NField.Alignment.CarryNineChannels

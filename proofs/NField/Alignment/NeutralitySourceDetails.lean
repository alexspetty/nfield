/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CenteredCollisionClosure

/-! # Empty-slice and fixed-label details of the residue-three argument -/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.NeutralityTheorem

open scoped BigOperators
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.CollisionTransformStrip

/-- Title: `The reflection fixed residue three label exists and is unique`. -/
theorem existsUnique_fixed_internal_label (m : ℕ) :
    ∃! j : ZMod 3, 2 * j = (m : ZMod 3) := by
  have htwo : (2 : ZMod 3) * 2 = 1 := by decide +kernel
  have hsol : (2 : ZMod 3) * (2 * m) = m := by
    rw [← mul_assoc, htwo, one_mul]
  refine ⟨2 * m, hsol, fun j hj => ?_⟩
  exact mul_left_cancel₀ (by decide : (2 : ZMod 3) ≠ 0) (hj.trans hsol.symm)

theorem coordinateSlice_raw_twice
    {α γ K : Type*} [Fintype α] [DecidableEq γ] [Field K] [CharZero K]
    (label : α → γ) (j : γ) (T : α → K) (r : α → α)
    (hr : Function.Involutive r)
    (hpreserve : ∀ a, label a = j → label (r a) = j)
    (hreflect : ∀ a, T a + T (r a) = -1) :
    2 * (∑ a : CoordinateSlice label j, T a) =
      -(Fintype.card (CoordinateSlice label j) : K) := by
  simpa only [two_mul] using
    (coordinateSlices_raw_pair label j j T r hr hpreserve hpreserve hreflect).2

/-- Title: `The fixed internal raw identity also includes the empty slice`. -/
theorem internal_fixed_slice_raw_twice
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb : 2 ≤ b) (hell : 1 ≤ ell) (j : ZMod 3)
    (hfixed : 2 * j = (allLagModulus b ell : ZMod 3)) :
    (2 : ℂ) * (∑ a : CoordinateSlice
      (internalResidueThree (m := allLagModulus b ell)) j, allLagUnitTable b ell a) =
      -(Fintype.card (CoordinateSlice
        (internalResidueThree (m := allLagModulus b ell)) j) : ℂ) := by
  have hm : 2 ≤ allLagModulus b ell := hb.trans (Nat.le_pow (by omega))
  apply coordinateSlice_raw_twice _ j (allLagUnitTable b ell) (fun a => -a)
  · intro a
    simp
  · exact internalResidueThree_fixed_preserved hm j hfixed
  · exact allLagUnitTable_reflection hb hell

end NField.Alignment.NeutralityTheorem

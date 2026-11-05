/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimitiveFloorTransform
import NField.Alignment.CenteredCollisionSum

/-! # Primitive character cancellation on actual reduction fibers -/

noncomputable section
namespace NField.Alignment.PrimitiveReductionFiber
open scoped BigOperators
open CollisionCharacterStructure

theorem primitive_nontrivial_kernel {N d : ℕ} [NeZero N]
    (hd : d ∣ N) (hdlt : d < N) (χ : Character N) (hχ : χ.IsPrimitive) :
    ∃ u : UnitClass N, ZMod.unitsMap hd u = 1 ∧ χ u.val ≠ 1 := by
  by_contra! hn
  have hfac : χ.FactorsThrough d := by
    apply (DirichletCharacter.factorsThrough_iff_ker_unitsMap hd).mpr
    intro u hu
    change χ.toUnitHom u = 1
    apply Units.ext
    exact hn u hu
  have hle : χ.conductor ≤ d := Nat.sInf_le hfac
  rw [hχ] at hle
  omega

/-- Multiplication by a kernel unit with nontrivial character value preserves
the fiber and forces its complete character sum to vanish. -/
theorem primitive_fiber_sum_zero {N d : ℕ} [NeZero N] [NeZero d]
    (hd : d ∣ N) (hdlt : d < N) (χ : Character N) (hχ : χ.IsPrimitive)
    (s : UnitClass d) :
    (∑ a : {a : UnitClass N // ZMod.unitsMap hd a = s}, χ a.val.val) = 0 := by
  classical
  obtain ⟨u, hu, hvalue⟩ := primitive_nontrivial_kernel hd hdlt χ hχ
  let F := {a : UnitClass N // ZMod.unitsMap hd a = s}
  let e : F ≃ F :=
    { toFun := fun a => ⟨u * a.val, by simp [map_mul, hu, a.property]⟩
      invFun := fun a => ⟨u⁻¹ * a.val, by simp [map_mul, hu, a.property]⟩
      left_inv := fun a => by apply Subtype.ext; simp
      right_inv := fun a => by apply Subtype.ext; simp }
  have hs : (∑ a : F, χ a.val.val) = χ u.val * ∑ a : F, χ a.val.val := by
    calc
      (∑ a : F, χ a.val.val) = ∑ a : F, χ (e a).val.val :=
        (Equiv.sum_comp e (fun a => χ a.val.val)).symm
      _ = χ u.val * ∑ a : F, χ a.val.val := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        change χ (u.val * a.val.val) = χ u.val * χ a.val.val
        exact map_mul χ _ _
  have hz : (χ u.val - 1) * ∑ a : F, χ a.val.val = 0 := by
    linear_combination -hs
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hvalue)

/-- Every weight constant on reduction fibers pairs to zero with a primitive
character at the larger modulus. -/
theorem primitive_reduction_weight_sum_zero {N d : ℕ} [NeZero N] [NeZero d]
    (hd : d ∣ N) (hdlt : d < N) (χ : Character N) (hχ : χ.IsPrimitive)
    (w : UnitClass d → ℂ) :
    (∑ a : UnitClass N, w (ZMod.unitsMap hd a) * χ a.val) = 0 := by
  classical
  rw [← Fintype.sum_fiberwise (ZMod.unitsMap hd)]
  apply Finset.sum_eq_zero
  intro s _
  have heq (a : {a : UnitClass N // ZMod.unitsMap hd a = s}) :
      w (ZMod.unitsMap hd a.val) * χ a.val.val = w s * χ a.val.val := by
    rw [a.property]
  simp_rw [heq]
  rw [← Finset.mul_sum, primitive_fiber_sum_zero hd hdlt χ hχ, mul_zero]

end NField.Alignment.PrimitiveReductionFiber

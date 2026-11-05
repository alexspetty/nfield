/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimitiveFloorTransform
import NField.Alignment.CollisionFluctuationSum

/-! # Primitive transforms for every natural multiplier, including nonunits -/

noncomputable section
namespace NField.Alignment.PrimitiveNaturalFloorTransform
open scoped BigOperators
open CollisionCharacterStructure CarryBoundarySpectra CollisionFluctuationSum

theorem primitive_fractional_transform {q : ℕ} [NeZero q]
    (χ : Character q) (hprim : χ.IsPrimitive) (n : ℕ) :
    (∑ a : UnitClass q, (((n * a.val.val) % q : ℕ) : ℂ) / q * χ⁻¹ a.val) =
      χ (n : ZMod q) * bernoulliOne χ⁻¹ := by
  let f : ZMod q → ℂ := fun x => (x.val : ℂ) / q
  have hbase : twistedTransform f χ⁻¹ 1 = bernoulliOne χ⁻¹ := by
    unfold twistedTransform bernoulliOne f
    simp only [one_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  have h := twistedTransform_eq_inv_mul f (inverse_isPrimitive hprim) (n : ZMod q)
  rw [inv_inv, hbase] at h
  unfold twistedTransform at h
  rw [sum_character_pairing_eq_units] at h
  simpa only [f, ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod] using h

theorem primitive_natural_floor_transform {q : ℕ} [NeZero q]
    (χ : Character q) (hprim : χ.IsPrimitive) (n : ℕ) :
    (∑ a : UnitClass q, (((n * a.val.val) / q : ℕ) : ℂ) * χ⁻¹ a.val) =
      ((n : ℂ) - χ (n : ZMod q)) * bernoulliOne χ⁻¹ := by
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hlinear : (∑ a : UnitClass q, (a.val.val : ℂ) * χ⁻¹ a.val) =
      (q : ℂ) * bernoulliOne χ⁻¹ := by
    unfold bernoulliOne
    rw [sum_character_pairing_eq_units]
    field_simp [hq]
  have hfloor (a : UnitClass q) :
      (((n * a.val.val) / q : ℕ) : ℂ) =
        (n : ℂ) / q * (a.val.val : ℂ) - (((n * a.val.val) % q : ℕ) : ℂ) / q := by
    have h := congrArg (fun k : ℕ => (k : ℂ)) (Nat.mod_add_div (n * a.val.val) q)
    push_cast at h
    field_simp [hq]
    linear_combination h
  simp_rw [hfloor, sub_mul, mul_assoc]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hlinear,
    primitive_fractional_transform χ hprim]
  field_simp [hq]

theorem primitive_floor_jump_transform {q : ℕ} [NeZero q]
    (χ : Character q) (hprim : χ.IsPrimitive) (n : ℕ) :
    (∑ a : UnitClass q, (floorJump q a.val.val n : ℂ) * χ⁻¹ a.val) =
      (1 + χ (n : ZMod q) - χ ((n + 1 : ℕ) : ZMod q)) * bernoulliOne χ⁻¹ := by
  unfold floorJump
  simp only [Int.cast_sub, Int.cast_natCast]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, primitive_natural_floor_transform χ hprim,
    primitive_natural_floor_transform χ hprim]
  push_cast
  ring

end NField.Alignment.PrimitiveNaturalFloorTransform

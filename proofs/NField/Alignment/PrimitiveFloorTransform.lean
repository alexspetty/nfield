/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CarryBoundarySpectra

/-!
# Primitive floor transform

The floor transform is proved directly from quotient-remainder arithmetic and
the primitive centered-sawtooth transform.  The multiplier is represented by
its intrinsic unit class, so all coprimality hypotheses are carried by the
type.
-/

namespace NField.Alignment.PrimitiveFloorTransform

open scoped BigOperators ComplexConjugate ZMod
open NField.Alignment.CarryBoundarySpectra
open NField.Alignment.CollisionCharacterStructure

/-- Exact primitive floor transform.  This is slightly stronger than the
odd-character specialization because parity is not needed. -/
theorem primitiveFloorTransform
    {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : Character q} (hχ : χ.IsPrimitive) (k : UnitClass q) :
    (∑ a : UnitClass q,
        (((k.val.val * a.val.val) / q : ℕ) : ℂ) * χ⁻¹ a.val) =
      ((k.val.val : ℂ) - χ k.val) * bernoulliOne χ⁻¹ := by
  classical
  letI : Fact (1 < q) := ⟨by omega⟩
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hχne : χ ≠ 1 := primitive_ne_one hq hχ
  have hinvne : χ⁻¹ ≠ 1 := inv_ne_one.mpr hχne
  have hfloor (a : UnitClass q) :
      (((k.val.val * a.val.val) / q : ℕ) : ℂ) =
        (k.val.val : ℂ) * (a.val.val : ℂ) / (q : ℂ) -
          centeredSawtooth (k.val * a.val) - 1 / 2 := by
    have hunit : IsUnit (k.val * a.val) :=
      IsUnit.mul k.isUnit a.isUnit
    have hne : k.val * a.val ≠ 0 := IsUnit.ne_zero hunit
    have hval : (k.val * a.val).val =
        (k.val.val * a.val.val) % q := by
      rw [ZMod.val_mul]
    unfold centeredSawtooth
    rw [if_neg hne, hval]
    have hdecomp := Nat.mod_add_div (k.val.val * a.val.val) q
    have hdecompC := congrArg (fun n : ℕ => (n : ℂ)) hdecomp
    push_cast at hdecompC ⊢
    rw [← hdecompC]
    field_simp [hqC]
    ring
  have hsumZero :
      (∑ a : UnitClass q, χ⁻¹ a.val) = 0 := by
    have hall : ∑ x : ZMod q, χ⁻¹ x = 0 :=
      (χ⁻¹).sum_eq_zero_of_ne_one hinvne
    have hpair := sum_character_pairing_eq_units
      (fun _ : ZMod q => (1 : ℂ)) χ⁻¹
    simp only [one_mul] at hpair
    exact hpair ▸ hall
  have hlinear :
      (∑ a : UnitClass q, (a.val.val : ℂ) * χ⁻¹ a.val) =
        (q : ℂ) * bernoulliOne χ⁻¹ := by
    have hpair := sum_character_pairing_eq_units
      (fun x : ZMod q => (x.val : ℂ)) χ⁻¹
    unfold bernoulliOne
    rw [← hpair]
    field_simp [hqC]
  have hsaw :
      (∑ a : UnitClass q,
          centeredSawtooth (k.val * a.val) * χ⁻¹ a.val) =
        χ k.val * bernoulliOne χ⁻¹ := by
    have hfull := twistedSawtooth_evaluation hq hχ k.val
    unfold twistedTransform at hfull
    have hpair := sum_character_pairing_eq_units
      (fun x : ZMod q => centeredSawtooth (k.val * x)) χ⁻¹
    exact hpair.symm.trans hfull
  simp_rw [hfloor]
  calc
    (∑ a : UnitClass q,
        ((k.val.val : ℂ) * (a.val.val : ℂ) / (q : ℂ) -
            centeredSawtooth (k.val * a.val) - 1 / 2) * χ⁻¹ a.val) =
      (k.val.val : ℂ) / (q : ℂ) *
          ∑ a : UnitClass q, (a.val.val : ℂ) * χ⁻¹ a.val -
        ∑ a : UnitClass q,
          centeredSawtooth (k.val * a.val) * χ⁻¹ a.val -
        (1 / 2 : ℂ) * ∑ a : UnitClass q, χ⁻¹ a.val := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
            ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro a _
          ring
    _ = (k.val.val : ℂ) / (q : ℂ) *
          ((q : ℂ) * bernoulliOne χ⁻¹) -
        χ k.val * bernoulliOne χ⁻¹ := by
          rw [hlinear, hsaw, hsumZero, mul_zero, sub_zero]
    _ = ((k.val.val : ℂ) - χ k.val) * bernoulliOne χ⁻¹ := by
      field_simp [hqC]

end NField.Alignment.PrimitiveFloorTransform

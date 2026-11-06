/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ConductorFourFloors
import NField.Alignment.IntegerConductorLedger
import Mathlib.NumberTheory.LegendreSymbol.ZModChar

/-! # The literal Mathlib character and the decimal collision coefficient -/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.ConductorFourCoefficient

open scoped BigOperators ComplexConjugate
open NField.Alignment.CollisionFluctuationSum
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionTransformStrip
open NField.Alignment.NeutralityTheorem
open NField.Alignment.GeneralNeutrality
open NField.Alignment.ConductorFourLifts
open NField.Alignment.IntegerConductorLedger

def complexChiFour : Character 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

def decimalChiFour : Character 100 :=
  DirichletCharacter.changeLevel (by decide : 4 ∣ 100) complexChiFour

def literalDecimalCenteredTable (a : UnitClass 100) : ℂ :=
  rationalCenteredTable 10 1 a.val.val

theorem mathlib_chiFour_eq_sign (n : ℕ) : ZMod.χ₄ (n : ZMod 4) = chiFourSign n := by
  rw [ZMod.χ₄_nat_eq_if_mod_four]
  have hmod := Nat.mod_lt n (by decide : 0 < 4)
  have hpar : n % 2 = (n % 4) % 2 := (Nat.mod_mod_of_dvd n (by decide : 2 ∣ 4)).symm
  interval_cases h : n % 4 <;> norm_num [chiFourSign, h, hpar]

theorem decimalChiFour_unit (a : UnitClass 100) :
    decimalChiFour a.val = (chiFourSign a.val.val : ℂ) := by
  unfold decimalChiFour
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd]
  unfold complexChiFour
  rw [MulChar.ringHomComp_apply, ZMod.cast_eq_val, mathlib_chiFour_eq_sign]
  rfl

/-- Title: `The lifted Mathlib conductor four character has zero collision coefficient`. -/
theorem literal_decimal_conductor_four_coefficient :
    collisionCoefficient literalDecimalCenteredTable decimalChiFour = 0 := by
  have hunit : reducedResidues 100 = (Finset.range 100).filter (fun a => a.Coprime 100) := by
    decide
  have hsum : (∑ a : UnitClass 100,
      literalDecimalCenteredTable a * conj (decimalChiFour a.val)) =
      (conductorFourCenteredNumerator : ℂ) := by
    simp_rw [literalDecimalCenteredTable, decimalChiFour_unit, map_intCast]
    rw [sum_units_val 100 (fun a : ℕ =>
      (rationalCenteredTable 10 1 a : ℂ) * (chiFourSign a : ℂ)),
      ← Finset.sum_filter, ← hunit]
    unfold conductorFourCenteredNumerator
    push_cast
    rfl
  unfold collisionCoefficient CenteredCollisionSum.finiteCoefficient
  change (Fintype.card (UnitClass 100) : ℂ)⁻¹ *
    (∑ a : UnitClass 100, literalDecimalCenteredTable a * conj (decimalChiFour a.val)) = 0
  rw [hsum, conductorFourCenteredNumerator_eq_zero]
  simp

end NField.Alignment.ConductorFourCoefficient

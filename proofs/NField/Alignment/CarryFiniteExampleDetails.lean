/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CarryFiniteExamples
import NField.Alignment.TerminalSupportSource

/-! # Complete finite source tables and conductor channels -/

noncomputable section
namespace NField.Alignment.CarryFiniteExampleDetails
open scoped BigOperators Classical ZMod
open CollisionCharacterStructure CarryBoundarySpectra CarryNineCharacter CarryFiniteExamples
  CollisionSmallConductorCharacters PrimitiveOddBoundaryMean TerminalSupportSource
  LiftedBoundaryInvisibility EndpointNormalization

local instance : Fact (1 < 9) := ⟨by decide⟩

/-- Title: `Every canonical carry step is zero or one`. -/
theorem carryStep_zero_or_one {m a n : ℕ} (hm : 0 < m) (ha : a < m) :
    carryStep m a n = 0 ∨ carryStep m a n = 1 := by
  have hdecomp : (n + 1) * a = m * (n * a / m) + (n * a % m + a) := by
    have h := Nat.div_add_mod (n * a) m
    nlinarith
  have hlt : (n * a % m + a) / m < 2 := by
    rw [Nat.div_lt_iff_lt_mul hm]
    have h := Nat.mod_lt (n * a) hm
    omega
  unfold carryStep
  simp only [hdecomp, Nat.mul_add_div hm, Nat.add_sub_cancel_left]
  have hnonneg : 0 ≤ (n * a % m + a) / m := Nat.zero_le _
  omega

/-- Title: `The base three digit diagonal is exactly the three printed cells`. -/
theorem nine_digit_support : terminalDigitSupport 3 2 = {0, 4, 8} := by decide

/-- Title: `Exact raw carry counts on the six units modulo nine`. -/
theorem nine_raw_carry_table :
    ([1, 2, 4, 5, 7, 8] : List ℕ).map
      (fun a => ∑ n ∈ ({0, 4, 8} : Finset ℕ), carryStep 9 a n) = [1, 2, 2, 1, 1, 2] := by
  decide

/-- Title: `The printed sixth-root character table modulo nine`. -/
theorem nine_character_table :
    ([1, 2, 4, 5, 7, 8] : List ℕ).map (fun a => chiNine (a : ZMod 9)) =
      [1, sixthRoot, sixthRoot ^ 2, sixthRoot ^ 5, sixthRoot ^ 4, -1] := by
  have h2 : sixthRoot ^ 2 = sixthRoot - 1 := by linear_combination sixthRoot_quadratic
  have h3 : sixthRoot ^ 3 = -1 := by
    calc
      sixthRoot ^ 3 = sixthRoot * sixthRoot ^ 2 := by ring
      _ = -1 := by rw [h2]; linear_combination sixthRoot_quadratic
  have h4 : sixthRoot ^ 4 = -sixthRoot := by
    rw [show (4 : ℕ) = 3 + 1 by decide, pow_add, h3]
    ring
  have h5 : sixthRoot ^ 5 = 1 - sixthRoot := by
    rw [show (5 : ℕ) = 3 + 2 by decide, pow_add, h3, h2]
    ring
  norm_num [chiNine, character, characterValues, ZMod.val_natCast, ZMod.val_one,
    ZMod.val_ofNat, h2, h4, h5]

/-- Title: `The conjugate primitive channel in the modulus nine example`. -/
theorem nine_inverse_carry_transform :
    carryTransform nineWeight chiNine⁻¹ = 2 + 2 * (Real.sqrt 3 : ℂ) * Complex.I := by
  unfold carryTransform
  rw [sum_residues]
  norm_num [nine_carry_value, chiNine, character, characterValues,
    Fin.sum_univ_succ, ZMod.val_natCast, sixthRoot]
  ring

/-- Title: `Both primitive carry coefficients have squared norm sixteen`. -/
theorem nine_primitive_coefficient_norms :
    ‖carryTransform nineWeight chiNine‖ ^ 2 = 16 ∧
      ‖carryTransform nineWeight chiNine⁻¹‖ ^ 2 = 16 := by
  rw [nine_carry_transform, nine_inverse_carry_transform]
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  constructor <;> simp only [Complex.sq_norm, Complex.normSq_apply] <;>
    norm_num <;> nlinarith

def chiInducedNine : Character 9 := DirichletCharacter.changeLevel (by decide : 3 ∣ 9) chiMinusThree

theorem chiInducedNine_nat (n : ℕ) : chiInducedNine (n : ZMod 9) =
    if n.Coprime 9 then chiMinusThree (n : ZMod 3) else 0 := by
  by_cases hn : n.Coprime 9
  · rw [if_pos hn]
    have h := DirichletCharacter.changeLevel_eq_cast_of_dvd chiMinusThree
      (by decide : 3 ∣ 9) (ZMod.unitOfCoprime n hn)
    simpa only [chiInducedNine, ZMod.coe_unitOfCoprime,
      ZMod.cast_natCast (by decide : 3 ∣ 9)] using h
  · rw [if_neg hn]
    exact MulChar.map_nonunit _ (by simpa only [ZMod.isUnit_iff_coprime] using hn)

/-- Title: `The induced odd channel modulo nine has zero carry transform`. -/
theorem nine_induced_transform_zero : carryTransform nineWeight chiInducedNine = 0 := by
  unfold carryTransform
  rw [sum_residues]
  simp only [nine_carry_value, MulChar.inv_apply_eq_inv', chiInducedNine_nat]
  norm_num [Fin.sum_univ_succ, ZMod.val_natCast,
    chiMinusThree, MulChar.ringHomComp_apply, chiMinusThreeInt]

/-- Title: `The lifted nine-state support has the nine printed cells modulo twenty seven`. -/
theorem twenty_seven_lifted_support :
    ((Finset.range 27).filter fun n => n / 3 ∈ ({0, 4, 8} : Finset ℕ)) =
      {0, 1, 2, 12, 13, 14, 24, 25, 26} := by decide

/-- Title: `Primitive characters modulo twenty seven cannot see the lifted carry`. -/
theorem twenty_seven_primitive_invisibility {χ : Character 27} (hχ : χ.IsPrimitive) :
    carryTransform (blockLiftWeight (q := 9) (L := 3) nineWeight) χ = 0 :=
  primitiveTransform_blockLift_zero (p := 3) (by decide) (by decide)
    (by decide) (by decide) nineWeight hχ

end NField.Alignment.CarryFiniteExampleDetails

/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CarryNineCharacter
import NField.Alignment.CarryQuadraticLayer
import NField.Alignment.CollisionSmallConductorCharacters
import NField.Alignment.FinitePrefixCarryReduction
import NField.Alignment.EndpointNormalization

/-! # Exact finite examples in the carry-boundary paper -/

noncomputable section
namespace NField.Alignment.CarryFiniteExamples
open scoped BigOperators ZMod
open CollisionCharacterStructure CarryBoundarySpectra CarryQuadraticLayer
  CarryNineCharacter CollisionSmallConductorCharacters FinitePrefixCarryReduction

local instance : Fact (1 < 9) := ⟨by decide⟩
local instance : Fact (1 < 6) := ⟨by decide⟩

theorem sum_residues {m : ℕ} [NeZero m] (f : ZMod m → ℂ) :
    (∑ x : ZMod m, f x) = ∑ n : Fin m, f (n.val : ZMod m) := by
  have h := ((ZMod.finEquiv m).toEquiv.sum_comp f).symm
  change (∑ x : ZMod m, f x) = ∑ n : Fin m, f (ZMod.finEquiv m n) at h
  simpa only [ConductorDepthSawtooth.finEquiv_eq_natCast] using h

def nineWeight (x : ZMod 9) : ℂ := if x = 0 ∨ x = 4 ∨ x = 8 then 1 else 0

def sixWeight (x : ZMod 6) : ℂ := if x = 0 ∨ x = 1 then 1 else 0

/-- Title: `Nine state prefix numerators`. -/
theorem nine_prefix_numerators :
    ((Finset.Ico 1 11).filter fun r => (9 * r / 11) ∈ ({0, 4, 8} : Finset ℕ)) =
      {1, 5, 6, 10} := by decide

/-- Title: `Intrinsic nine state digit count`. -/
theorem nine_intrinsic_digit_count :
    ((Finset.Ico 1 11).filter fun r => digitReadout 3 11 r 0 = digitReadout 3 11 r 1).card = 4 := by
  decide

/-- Title: `Nine state slice decomposition`. -/
theorem nine_slice_counts :
    (∑ n ∈ ({0, 4, 8} : Finset ℕ), ((n + 1) * 2 / 9 - n * 2 / 9)) = 2 ∧
      (4 : ℤ) = 1 * 3 + 2 - 1 := by decide

/-- Title: `Visible signed boundary modulo nine`. -/
theorem nine_signed_boundary (x : ZMod 9) :
    signedBoundary nineWeight x =
      (if x = 1 ∨ x = 5 then 1 else 0) - (if x = 4 ∨ x = 8 then 1 else 0) := by
  simp only [signedBoundary, nineWeight, sub_eq_add_neg,
    show (-1 : ZMod 9) = 8 by decide, ← (ZMod.val_injective 9).eq_iff, ZMod.val_add]
  norm_num only [ZMod.val_zero, ZMod.val_one, ZMod.val_ofNat]
  fin_cases x <;> norm_num [ZMod.val_natCast, ZMod.val_ofNat, ZMod.val_zero, ZMod.val_one, ZMod.val, Fin.val_ofNat, Fin.val_natCast]

/-- Title: `Nonunit signed boundary modulo six`. -/
theorem six_signed_boundary (x : ZMod 6) :
    signedBoundary sixWeight x = (if x = 2 then 1 else 0) - (if x = 0 then 1 else 0) := by
  simp only [signedBoundary, sixWeight, sub_eq_add_neg,
    show (-1 : ZMod 6) = 5 by decide, ← (ZMod.val_injective 6).eq_iff, ZMod.val_add]
  norm_num only [ZMod.val_zero, ZMod.val_one, ZMod.val_ofNat]
  fin_cases x <;> norm_num [ZMod.val_natCast, ZMod.val_ofNat, ZMod.val_zero, ZMod.val_one, ZMod.val, Fin.val_ofNat, Fin.val_natCast]

theorem nine_carry_value (a : ZMod 9) :
    carryObservable nineWeight a = match a.val with
      | 1 => 2/3 | 2 => 4/3 | 4 => 2/3 | 5 => -2/3 | 7 => -4/3 | 8 => -2/3 | _ => 0 := by
  unfold carryObservable
  rw [sum_residues]
  simp only [Fin.sum_univ_succ, nineWeight, centeredSawtooth,
    ← (ZMod.val_injective 9).eq_iff, ZMod.val_mul, ZMod.val_add,
    ZMod.val_natCast, ZMod.val_ofNat]
  norm_num only [ZMod.val_zero, ZMod.val_one, ZMod.val_ofNat]
  fin_cases a <;> norm_num [ZMod.val_zero, ZMod.val_one, ZMod.val, Fin.val_ofNat, Fin.val_natCast]

theorem six_carry_value (a : ZMod 6) :
    carryObservable sixWeight a = match a.val with
      | 1 => 1/6 | 2 => -1/6 | 4 => 1/6 | 5 => -1/6 | _ => 0 := by
  unfold carryObservable
  rw [sum_residues]
  simp only [Fin.sum_univ_succ, sixWeight, centeredSawtooth,
    ← (ZMod.val_injective 6).eq_iff, ZMod.val_mul, ZMod.val_add,
    ZMod.val_natCast, ZMod.val_ofNat]
  norm_num only [ZMod.val_zero, ZMod.val_one, ZMod.val_ofNat]
  fin_cases a <;> norm_num [ZMod.val_zero, ZMod.val_one, ZMod.val, Fin.val_ofNat, Fin.val_natCast]

/-- Title: `Actual centered carry table modulo nine`. -/
theorem nine_carry_table :
    (List.ofFn fun a : Fin 9 => carryObservable nineWeight (a.val : ZMod 9)) =
      [0, 2/3, 4/3, 0, 2/3, -2/3, 0, -4/3, -2/3] := by
  norm_num [nine_carry_value, List.ofFn_succ, ZMod.val_natCast, ZMod.val_ofNat]

/-- Title: `Actual centered carry table modulo six`. -/
theorem six_carry_table :
    (List.ofFn fun a : Fin 6 => carryObservable sixWeight (a.val : ZMod 6)) =
      [0, 1/6, -1/6, 0, 1/6, -1/6] := by
  norm_num [six_carry_value, List.ofFn_succ, ZMod.val_natCast, ZMod.val_ofNat]

/-- Title: `Every ordinary flux in the modulus six example is zero`. -/
theorem six_ordinary_flux_zero (χ : Character 6) : cellBoundaryFlux sixWeight χ = 0 := by
  rw [cellBoundaryFlux_eq_boundary_pairing]
  simp_rw [six_signed_boundary]
  have h0 : χ (0 : ZMod 6) = 0 := χ.map_zero' (by decide)
  have h2 : χ (2 : ZMod 6) = 0 := MulChar.map_nonunit χ (by decide)
  simp only [sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib]
  simp [h0, h2]

/-- Title: `The induced modulus six transform equals one third`. -/
theorem six_induced_transform : carryTransform sixWeight chiInducedSix = 1/3 := by
  unfold carryTransform
  rw [sum_residues]
  simp only [six_carry_value, MulChar.inv_apply_eq_inv', chiInducedSix_nat]
  norm_num [Fin.sum_univ_succ, ZMod.val_natCast, ZMod.val_ofNat,
    chiMinusThree, MulChar.ringHomComp_apply, chiMinusThreeInt]

/-- Title: `Exact modulo nine boundary flux`. -/
theorem nine_boundary_flux :
    cellBoundaryFlux nineWeight chiNine = 3 - (Real.sqrt 3 : ℂ) * Complex.I := by
  rw [cellBoundaryFlux_eq_boundary_pairing]
  simp_rw [nine_signed_boundary]
  simp only [sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib]
  rw [sum_residues, sum_residues]
  norm_num [Fin.sum_univ_succ, chiNine, character, characterValues,
    ← (ZMod.val_injective 9).eq_iff, ZMod.val_natCast, ZMod.val_ofNat, ZMod.val_zero, ZMod.val_one]
  unfold sixthRoot
  ring

/-- Title: `Exact modulo nine Bernoulli value`. -/
theorem nine_bernoulli_value :
    bernoulliOne chiNine⁻¹ = -1 + (Real.sqrt 3 : ℂ) * Complex.I / 3 := by
  have hi (a : ZMod 9) : chiNine⁻¹ a = star (chiNine a) := by
    rw [MulChar.star_apply']
  unfold bernoulliOne
  simp_rw [hi]
  rw [sum_residues]
  norm_num [chiNine, character, characterValues, Fin.sum_univ_succ, sixthRoot,
    ZMod.val_natCast, ZMod.val_ofNat, ZMod.val_zero, ZMod.val_one, map_div₀, map_add, map_mul, map_ofNat, Complex.conj_I]
  ring

/-- Title: `Exact modulo nine carry transform`. -/
theorem nine_carry_transform :
    carryTransform nineWeight chiNine = 2 - 2 * (Real.sqrt 3 : ℂ) * Complex.I := by
  rw [carryBoundary_factorization (by decide) nineWeight chiNine_primitive,
    nine_bernoulli_value, nine_boundary_flux]
  have hsq : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  ring_nf
  norm_num [hsq, Complex.I_sq]
  ring

/-- Title: `Exact modulo nine carry energy`. -/
theorem nine_carry_energy :
    (∑ a : UnitClass 9, ‖carryObservable nineWeight a.val‖ ^ 2) = 16/3 := by
  have hs := unit_sum_eq_coprime_range (m := 9)
    (fun n => ((‖carryObservable nineWeight (n : ZMod 9)‖ ^ 2 : ℝ) : ℂ))
  simp only [ZMod.natCast_zmod_val] at hs
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum, hs]
  norm_num [Finset.sum_filter, Finset.sum_range_succ, nine_carry_value,
    ZMod.val_natCast, ZMod.val_ofNat, Complex.sq_norm, Complex.normSq_apply]

end NField.Alignment.CarryFiniteExamples

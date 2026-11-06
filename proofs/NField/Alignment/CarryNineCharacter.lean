/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimitiveOddBoundaryMean

/-! # The actual primitive odd character in the nine-state example -/

noncomputable section
namespace NField.Alignment.CarryNineCharacter
open scoped BigOperators ZMod
open CollisionCharacterStructure PrimitiveOddBoundaryMean

/-- The six unit values, with zero on the three nonunits. -/
def characterValues (z : ℂ) (a : ZMod 9) : ℂ :=
  match a.val with
  | 1 => 1
  | 2 => z
  | 4 => z - 1
  | 5 => 1 - z
  | 7 => -z
  | 8 => -1
  | _ => 0

/-- An actual Dirichlet character for either primitive sixth root. -/
def character (z : ℂ) (hz : z ^ 2 - z + 1 = 0) : Character 9 where
  toFun := characterValues z
  map_one' := by rfl
  map_mul' := by
    intro a b
    simp only [characterValues, ZMod.val_mul]
    fin_cases a <;> fin_cases b <;> norm_num [ZMod.val]
    all_goals first | (solve | ring) | (solve | linear_combination hz) |
      (solve | linear_combination -hz)
  map_nonunit' := by
    intro a ha
    have ha' : a = 0 ∨ a = 3 ∨ a = 6 :=
      (by decide : ∀ a : ZMod 9, ¬ IsUnit a → a = 0 ∨ a = 3 ∨ a = 6) a ha
    rcases ha' with rfl | rfl | rfl <;> rfl

/-- The manuscript's root `exp(2πi/6)`, in exact rectangular coordinates. -/
def sixthRoot : ℂ := (1 + (Real.sqrt 3 : ℂ) * Complex.I) / 2

theorem sixthRoot_quadratic : sixthRoot ^ 2 - sixthRoot + 1 = 0 := by
  have hsq : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  unfold sixthRoot
  ring_nf
  norm_num [hsq, Complex.I_sq]

def chiNine : Character 9 := character sixthRoot sixthRoot_quadratic

/-- Title: `The printed character modulo nine is odd`. -/
theorem chiNine_odd : chiNine.Odd := by
  change characterValues sixthRoot (-1 : ZMod 9) = -1
  norm_num [characterValues]

/-- Title: `The printed character modulo nine is primitive`. -/
theorem chiNine_primitive : chiNine.IsPrimitive := by
  by_contra hn
  have hf := (nonprimitive_iff_factorsThrough_previous
    (p := 3) (N := 2) (by decide) (by decide) chiNine).mp hn
  have hk := (DirichletCharacter.factorsThrough_iff_ker_unitsMap
    (χ := chiNine) (by decide : 3 ∣ 9)).mp hf
  let u : UnitClass 9 := ZMod.unitOfCoprime 4 (by decide)
  have hu : ZMod.unitsMap (by decide : 3 ∣ 9) u = 1 := by decide
  have hv := hk hu
  have he : characterValues sixthRoot 4 = 1 := by
    exact congrArg Units.val hv
  change sixthRoot - 1 = 1 at he
  have hz := sixthRoot_quadratic
  rw [show sixthRoot = 2 by linear_combination he] at hz
  norm_num at hz

/-- Title: `Exact sixth root and the exponential convention`. -/
theorem sixthRoot_eq_exp : sixthRoot = Complex.exp (2 * Real.pi * Complex.I / 6) := by
  rw [show (2 * (Real.pi : ℂ) * Complex.I / 6) = ((Real.pi / 3 : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.exp_mul_I]
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_three,
    Real.sin_pi_div_three]
  unfold sixthRoot
  push_cast
  ring

end NField.Alignment.CarryNineCharacter

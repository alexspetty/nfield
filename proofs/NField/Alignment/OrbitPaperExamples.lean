/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.BaseFifteenExamples
import NField.Alignment.OrbitIndicatorCorrespondence

/-! # Literal finite examples in the orbit paper -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.OrbitPaperExamples
open CarryBoundarySpectra ExactConductorEnergy OrbitIndicatorCorrespondence IndexTwoOrbitEnergy
open scoped BigOperators

theorem full_orbit_nine_cycle :
    ((List.range 6).map fun n => (2 : ZMod 9) ^ n) = [1, 2, 4, 8, 7, 5] ∧
      (2 : ZMod 9) ^ 6 = 1 ∧
      ∀ x : ZMod 9, IsUnit x ↔ x ∈ ([1, 2, 4, 8, 7, 5] : List (ZMod 9)) := by
  decide

theorem full_orbit_nine_boundary (x : ZMod 9) :
    signedBoundary (fullUnitWeight 9) x =
      (if x = 0 ∨ x = 3 ∨ x = 6 then 1 else 0) -
        (if x = 1 ∨ x = 4 ∨ x = 7 then 1 else 0) := by
  have h := fullUnitBoundary_formula (p := 3) (e := 2) (by decide) (by decide) x
  calc
    signedBoundary (fullUnitWeight 9) x =
        (if primeReduction (p := 3) (e := 2) (by decide) x = 0 then 1 else 0) -
          (if primeReduction (p := 3) (e := 2) (by decide) x = 1 then 1 else 0) := h
    _ = _ := by
      have h0 : ∀ y : ZMod 9, primeReduction (p := 3) (e := 2) (by decide) y = 0 ↔
          y = 0 ∨ y = 3 ∨ y = 6 := by decide
      have h1 : ∀ y : ZMod 9, primeReduction (p := 3) (e := 2) (by decide) y = 1 ↔
          y = 1 ∨ y = 4 ∨ y = 7 := by decide
      simp only [h0, h1]

theorem full_orbit_nine_energy :
    fullOddBoundaryEnergy (unitBoundarySignal (fullUnitWeight 9)) = 9 ∧
    exactConductorEnergy 3 (unitBoundarySignal (fullUnitWeight 9)) = 9 ∧
    exactConductorEnergy 9 (unitBoundarySignal (fullUnitWeight 9)) = 0 := by
  constructor
  · have h := actual_full_orbit_total_energy (p := 3) (e := 2)
      (by decide) (by decide) (by decide)
    norm_num at h ⊢
    exact h
  constructor
  · have h := actual_full_orbit_conductor_energy (p := 3) (e := 2) (d := 3)
      (by decide) (by decide) (by decide) (by decide)
    norm_num at h ⊢
    exact h
  · have h := actual_full_orbit_conductor_energy (p := 3) (e := 2) (d := 9)
      (by decide) (by decide) (by decide) (by decide)
    norm_num at h ⊢
    exact h

theorem prime_seven_card_moment :
    letI : Fact (Nat.Prime 7) := ⟨by decide⟩
    (offResonanceOddCharacters 7).card = 2 ∧ offResonanceJacobiMoment 7 = 4 := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hodd : (complexQuadraticCharacter 7).Odd :=
    (complexQuadraticCharacter_odd_iff (by decide : Nat.Prime 7) (by decide)).mpr (by decide)
  have hc := offResonanceOddCharacters_card_cast (by decide : Nat.Prime 7) (by decide)
  have hm := offResonanceJacobiMoment_eq (by decide : Nat.Prime 7) (by decide)
  rw [if_pos hodd] at hc hm
  constructor
  · norm_num at hc
    exact_mod_cast hc
  · have hn : complexQuadraticCharacter 7 (-2) = -1 := by
      apply Complex.ext
      · simpa using complexQuadraticCharacter_negTwo_re (by decide : Nat.Prime 7) (by decide)
      · simp [complexQuadraticCharacter]
    norm_num [hn] at hm
    exact hm

end NField.Alignment.OrbitPaperExamples

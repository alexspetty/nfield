/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetCarry
import NField.Alignment.CollisionRampEnergy
import NField.Alignment.DedekindReciprocity
import NField.Alignment.ConductorDepthSawtooth

/-! # Literal real clock readings on the carry grid -/

noncomputable section

namespace NField.Alignment.CommonResetGrid

open scoped BigOperators
open CollisionRampEnergy DedekindReciprocity CarryBoundarySpectra
open CollisionBernoulliStraightening PrimeCarryTableColumnLaw

/-- Title: `A real clock reading equals the exact rational sawtooth`. -/
theorem midpointRow_rational {m : ℕ} (hm : 0 < m) (r a : ℕ) :
    midpointRow r ((a : ℝ)/(m : ℝ)) = (rationalSawtooth (r*a) m : ℝ) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  unfold midpointRow affineRow rationalSawtooth
  rw [← mul_div_assoc, ← Nat.cast_mul, Int.fract_div_natCast_eq_div_natCast_mod]
  by_cases hz : (r*a)%m = 0
  · simp [hz]
  · have hnz : (((r*a)%m : ℕ) : ℝ)/(m : ℝ) ≠ 0 :=
      div_ne_zero (by exact_mod_cast hz) hmR
    simp [hz, hnz]

/-- Title: `Real grid readings agree with the intrinsic residue sawtooth`. -/
theorem midpointRow_grid {m : ℕ} [NeZero m] (r a : ℕ) :
    (midpointRow r ((a : ℝ)/(m : ℝ)) : ℂ) =
      centeredSawtooth ((r*a : ℕ) : ZMod m) := by
  rw [midpointRow_rational (NeZero.pos m)]
  have h := rationalSawtooth_val_eq_centeredSawtooth ((r*a : ℕ) : ZMod m)
  have he : rationalSawtooth (((r*a : ℕ) : ZMod m).val) m =
      rationalSawtooth (r*a) m := by
    simp only [ZMod.val_natCast, rationalSawtooth, Nat.mod_mod]
  rw [he] at h
  simpa only [Complex.ofReal_ratCast] using h

/-- Title: `The complete real profile equals the straightened carry profile`. -/
theorem boundaryResponse_grid {b : ℕ} (hb : 2 ≤ b) (A : ZMod (b^2)) :
    (boundaryResponse (b-1) ((A.val : ℝ)/(b : ℝ)^2) : ℂ) =
      CommonResetCarry.bernoulliBoundary hb A := by
  letI : NeZero (b^2) := ⟨pow_ne_zero 2 (by omega : b ≠ 0)⟩
  have hsets : Finset.Icc 1 (b-1) = Finset.Ico 1 b := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  unfold boundaryResponse CommonResetCarry.bernoulliBoundary
  push_cast
  rw [hsets]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  have h := midpointRow_grid (m := b^2) r A.val
  simpa only [Nat.cast_pow, Nat.cast_mul, ZMod.natCast_zmod_val] using h

def carryReading (b a : ℕ) : ℝ := (carryThresholdCount b a : ℝ) - (a : ℝ)/(b : ℝ)

def carryEnergy (b : ℕ) : ℝ := ∑ a ∈ Finset.range (b^2), carryReading b a ^ 2

theorem carryReading_cast {b : ℕ} (hb : 2 ≤ b) (a : ZMod (b^2)) :
    (carryReading b a.val : ℂ) = collisionResponse b a := by
  have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
  unfold carryReading collisionResponse
  push_cast
  field_simp

/-- The least residue of the manuscript's multiplier `(1-b)A`. -/
def straightenedAddress (b A : ℕ) : ℕ :=
  ((straighteningUnit b).val * (A : ZMod (b^2))).val

/-- Title: `The straightened address is the printed least residue`. -/
theorem straightenedAddress_int_mod {b : ℕ} (hb : 2 ≤ b) (A : ℕ) :
    (straightenedAddress b A : ℤ) = ((1-(b : ℤ))*(A : ℤ)) % (b^2 : ℕ) := by
  letI : NeZero (b^2) := ⟨pow_ne_zero 2 (by omega : b ≠ 0)⟩
  have h := ZMod.val_intCast (n := b^2) ((1-(b : ℤ))*(A : ℤ))
  simpa [straightenedAddress, straighteningUnit] using h

/-- Title: `Every carry reading is the literal real clock reading`. -/
theorem carry_representation {b A : ℕ} (hb : 2 ≤ b) (hA : A < b^2) :
    carryReading b (straightenedAddress b A) =
      boundaryResponse (b-1) ((A : ℝ)/(b : ℝ)^2) := by
  letI : NeZero (b^2) := ⟨pow_ne_zero 2 (by omega : b ≠ 0)⟩
  apply Complex.ofReal_injective
  rw [show (carryReading b (straightenedAddress b A) : ℂ) =
    collisionResponse b ((straighteningUnit b).val * (A : ZMod (b^2))) from
      carryReading_cast hb _]
  rw [CommonResetCarry.collision_to_bernoulli_straightening hb,
    ← boundaryResponse_grid hb]
  simp only [ZMod.val_natCast, Nat.mod_eq_of_lt hA]

theorem sum_residue_values {m : ℕ} [NeZero m] (f : ℕ → ℝ) :
    (∑ a : ZMod m, f a.val) = ∑ a ∈ Finset.range m, f a := by
  rw [← (ZMod.finEquiv m).toEquiv.sum_comp (fun a : ZMod m => f a.val)]
  change (∑ i : Fin m, f (ZMod.finEquiv m i).val) = _
  simp only [ConductorDepthSawtooth.finEquiv_eq_natCast, ZMod.val_natCast,
    Nat.mod_eq_of_lt (Fin.isLt _)]
  exact Fin.sum_univ_eq_sum_range f m

theorem carryEnergy_eq_complex {b : ℕ} (hb : 2 ≤ b) :
    carryEnergy b = CommonResetCarry.collisionEnergy hb := by
  letI : NeZero (b^2) := ⟨pow_ne_zero 2 (by omega : b ≠ 0)⟩
  unfold carryEnergy CommonResetCarry.collisionEnergy
  rw [← sum_residue_values]
  apply Finset.sum_congr rfl
  intro a _
  rw [← carryReading_cast hb]
  simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- Title: `The carry energy is the full real grid square sum`. -/
theorem carry_energy_representation {b : ℕ} (hb : 2 ≤ b) :
    carryEnergy b = ∑ A ∈ Finset.range (b^2),
      boundaryResponse (b-1) ((A : ℝ)/(b : ℝ)^2)^2 := by
  letI : NeZero (b^2) := ⟨pow_ne_zero 2 (by omega : b ≠ 0)⟩
  rw [carryEnergy_eq_complex hb, CommonResetCarry.collision_energy_eq_bernoulli_energy hb]
  unfold CommonResetCarry.bernoulliEnergy
  rw [← sum_residue_values]
  apply Finset.sum_congr rfl
  intro A _
  rw [← boundaryResponse_grid hb]
  simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]

end NField.Alignment.CommonResetGrid

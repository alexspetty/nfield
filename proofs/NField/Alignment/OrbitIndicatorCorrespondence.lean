/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimePowerFullOrbitBoundary
import NField.Alignment.IndexTwoOrbitEnergy
import NField.Alignment.CarryBoundarySpectra

/-! # The spectral boundary models are the actual orbit indicators -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.OrbitIndicatorCorrespondence
open CollisionCharacterStructure CarryBoundarySpectra PrimePowerFullOrbitBoundary IndexTwoOrbitEnergy
open ExactConductorEnergy

def fullUnitWeight (m : ℕ) (x : ZMod m) : ℂ := by
  classical
  exact if IsUnit x then 1 else 0

def primeReduction {p e : ℕ} (he : 1 ≤ e) : ZMod (p ^ e) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (by omega : e ≠ 0)) (ZMod p)

theorem primePower_unit_iff_reduction_ne_zero {p e : ℕ}
    (hp : p.Prime) (he : 1 ≤ e) (x : ZMod (p ^ e)) :
    IsUnit x ↔ primeReduction he x ≠ 0 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
  calc
    IsUnit x ↔ IsUnit (x.val : ZMod (p ^ e)) := by rw [ZMod.natCast_zmod_val]
    _ ↔ ¬p ∣ x.val := ZMod.isUnit_natCast_iff_not_dvd_pow hp (by omega)
    _ ↔ primeReduction he x ≠ 0 := by
      have hcast : primeReduction he x = (x.val : ZMod p) := by
        exact ZMod.cast_eq_val x
      rw [hcast]
      exact not_congr (ZMod.natCast_eq_zero_iff x.val p).symm

theorem fullUnitBoundary_formula {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e)
    (x : ZMod (p ^ e)) :
    signedBoundary (fullUnitWeight (p ^ e)) x =
      (if primeReduction he x = 0 then 1 else 0) -
        (if primeReduction he x = 1 then 1 else 0) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  simp only [signedBoundary, fullUnitWeight, primePower_unit_iff_reduction_ne_zero hp he,
    map_sub, map_one, sub_ne_zero]
  by_cases h0 : primeReduction he x = 0 <;>
    by_cases h1 : primeReduction he x = 1 <;> simp [h0, h1]

theorem fullUnitBoundary_visible {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) :
    unitBoundarySignal (fullUnitWeight (p ^ e)) = fullOrbitVisibleBoundary he := by
  classical
  funext u
  rw [unitBoundarySignal, fullUnitBoundary_formula hp he]
  have hzero := (primePower_unit_iff_reduction_ne_zero hp he u.val).mp u.isUnit
  have hred : primeReduction he u.val =
      (ZMod.unitsMap (dvd_pow_self p (by omega : e ≠ 0)) u).val := rfl
  rw [if_neg hzero]
  simp only [hred, Units.val_eq_one, fullOrbitVisibleBoundary]
  split_ifs <;> norm_num

theorem actual_full_orbit_conductor_energy {p e d : ℕ}
    [NeZero (p ^ e)] [NeZero p] (hp : p.Prime) (hpodd : p ≠ 2)
    (he : 1 ≤ e) (hd : d ∣ p ^ e) :
    exactConductorEnergy d (unitBoundarySignal (fullUnitWeight (p ^ e))) =
      if d = p then ((p - 1 : ℝ) / 2) * (p : ℝ) ^ (2 * e - 2) else 0 := by
  rw [fullUnitBoundary_visible hp he]
  obtain ⟨f, hfe, rfl⟩ := (Nat.dvd_prime_pow hp).mp hd
  rw [fullOrbit_exactConductorEnergy_pow hp hpodd he hfe]
  have heq : p ^ f = p ↔ f = 1 := by
    simpa only [pow_one] using
      (show p ^ f = p ^ 1 ↔ f = 1 from (Nat.pow_right_injective hp.two_le).eq_iff)
  simp only [heq]

theorem actual_full_orbit_total_energy {p e : ℕ}
    [NeZero (p ^ e)] [NeZero p] (hp : p.Prime) (hpodd : p ≠ 2)
    (he : 1 ≤ e) :
    fullOddBoundaryEnergy (unitBoundarySignal (fullUnitWeight (p ^ e))) =
      ((p - 1 : ℝ) / 2) * (p : ℝ) ^ (2 * e - 2) := by
  rw [fullUnitBoundary_visible hp he]
  exact fullOrbit_fullOddBoundaryEnergy hp hpodd he

theorem indexTwoIndicator_eq_square_indicator {q : ℕ} [Fact q.Prime] (x : ZMod q) :
    indexTwoIndicator x = if x ≠ 0 ∧ IsSquare x then 1 else 0 := by
  classical
  by_cases hx : x = 0
  · subst x
    have h0 : (1 : Character q) (0 : ZMod q) = 0 :=
      MulChar.map_nonunit _ (by simp)
    have hχ0 : complexQuadraticCharacter q (0 : ZMod q) = 0 :=
      MulChar.map_nonunit _ (by simp)
    simp [indexTwoIndicator, h0, hχ0]
  · have hone : (1 : Character q) x = 1 := MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)
    by_cases hs : IsSquare x
    · have hχ : complexQuadraticCharacter q x = 1 := by
        change ((quadraticChar (ZMod q) x : ℤ) : ℂ) = 1
        rw [(quadraticChar_one_iff_isSquare hx).mpr hs]
        norm_num
      norm_num [indexTwoIndicator, hone, hχ, hx, hs]
    · have hχ : complexQuadraticCharacter q x = -1 := by
        change ((quadraticChar (ZMod q) x : ℤ) : ℂ) = -1
        rw [quadraticChar_neg_one_iff_not_isSquare.mpr hs]
        norm_num
      simp [indexTwoIndicator, hone, hχ, hx, hs]

theorem indexTwoIndicator_eq_kernel_indicator {q : ℕ} [Fact q.Prime] (x : ZMod q) :
    indexTwoIndicator x = if IsUnit x ∧ complexQuadraticCharacter q x = 1 then 1 else 0 := by
  classical
  simp only [indexTwoIndicator_eq_square_indicator, isUnit_iff_ne_zero]
  by_cases hx : x = 0
  · simp [hx]
  · have hχ : complexQuadraticCharacter q x = 1 ↔ IsSquare x := by
      change ((quadraticChar (ZMod q) x : ℤ) : ℂ) = 1 ↔ IsSquare x
      norm_cast
      exact quadraticChar_one_iff_isSquare hx
    simp only [hχ]

end NField.Alignment.OrbitIndicatorCorrespondence

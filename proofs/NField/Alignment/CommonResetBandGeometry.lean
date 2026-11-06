/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetBandParameters

/-! # Exact interval geometry for the quotient bands -/

noncomputable section

namespace NField.Alignment.CommonResetBandGeometry

open Set CommonResetBandParameters

def bandRight (p m : ℕ) : ℝ := ((p-1 : ℕ) : ℝ)/(m : ℝ)

/-- Title: `The entire quotient band lies between its left endpoint and twice that endpoint`. -/
theorem band_right_le_twice {p m : ℕ} (hm : 1 ≤ m) :
    bandRight p m ≤ 2*bandLeft p m := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  unfold bandRight bandLeft
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (show (0 : ℝ) < m by linarith) (by positivity)).mpr
  nlinarith [mul_nonneg (Nat.cast_nonneg (p-1)) (sub_nonneg.mpr hmR)]

theorem band_width {p m : ℕ} (hm : 1 ≤ m) :
    bandRight p m-bandLeft p m = ((p-1 : ℕ) : ℝ)/((m : ℝ)*((m : ℝ)+1)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  unfold bandRight bandLeft
  field_simp
  ring

theorem band_width_le {p m : ℕ} (hm : 1 ≤ m) :
    bandRight p m-bandLeft p m ≤ (p : ℝ)/(m : ℝ)^2 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [band_width hm]
  calc
    _ ≤ (p : ℝ)/((m : ℝ)*((m : ℝ)+1)) :=
      div_le_div_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le p 1)) (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (Nat.cast_nonneg p) (by positivity) (by nlinarith)

/-- Title: `Every retained interval has at most twice p divided by the squared quotient in integer samples`. -/
theorem band_interval_length {p m : ℕ} (hm : 1 ≤ m) (hmsq : m^2 ≤ p)
    (a : ℤ) (N : ℕ) (hsub : Icc (a : ℝ) (a+N) ⊆ Icc (bandLeft p m) (bandRight p m)) :
    (N : ℝ)+1 ≤ 2*(p : ℝ)/(m : ℝ)^2 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hab : (a : ℝ) ≤ a+N := le_add_of_nonneg_right (Nat.cast_nonneg N)
  have hlo := (hsub ⟨le_rfl, hab⟩).1
  have hhi := (hsub ⟨hab, le_rfl⟩).2
  have hlen : (N : ℝ) ≤ (p : ℝ)/(m : ℝ)^2 := by linarith [band_width_le (p := p) hm]
  have hone : (1 : ℝ) ≤ (p : ℝ)/(m : ℝ)^2 := by
    apply (le_div_iff₀ (by positivity)).mpr
    simpa only [one_mul] using (show (m : ℝ)^2 ≤ p by exact_mod_cast hmsq)
  calc
    _ ≤ (p : ℝ)/(m : ℝ)^2+(p : ℝ)/(m : ℝ)^2 := add_le_add hlen hone
    _ = _ := by ring

theorem band_interval_dyadic {p m : ℕ} (hm : 1 ≤ m) (a : ℤ) (N : ℕ)
    (hsub : Icc (a : ℝ) (a+N) ⊆ Icc (bandLeft p m) (bandRight p m)) :
    Icc (a : ℝ) (a+N) ⊆ Icc (bandLeft p m) (2*bandLeft p m) := by
  intro x hx
  exact ⟨(hsub hx).1, (hsub hx).2.trans (band_right_le_twice hm)⟩

end NField.Alignment.CommonResetBandGeometry

/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib
/-! # The literal nearest-integer Euclidean remainder, with lower ties -/

set_option autoImplicit false

namespace NField.ResetForests.EuclideanFold

def nearestQuotient (d a : ℕ) : ℕ :=
  d / a + if 2 * (d % a) ≤ a then 0 else 1

def signedRemainder (d a : ℕ) : ℤ :=
  (d : ℤ) - (nearestQuotient d a : ℤ) * (a : ℤ)

def remainderHeight (d a : ℕ) : ℕ := (signedRemainder d a).natAbs

theorem quotient_lower_branch (d a : ℕ) (h : 2 * (d % a) ≤ a) :
    nearestQuotient d a = d / a := by
  simp [nearestQuotient, h]

theorem quotient_upper_branch (d a : ℕ) (h : a < 2 * (d % a)) :
    nearestQuotient d a = d / a + 1 := by
  simp [nearestQuotient, Nat.not_le.mpr h]

theorem remainder_lower_branch (d a : ℕ) (h : 2 * (d % a) ≤ a) :
    signedRemainder d a = (d % a : ℕ) := by
  have hd : (d : ℤ) = (a : ℤ) * (d / a : ℕ) + (d % a : ℕ) := by
    exact_mod_cast (Nat.div_add_mod d a).symm
  rw [signedRemainder, quotient_lower_branch d a h]
  nlinarith

theorem remainder_upper_branch (d a : ℕ) (h : a < 2 * (d % a)) :
    signedRemainder d a = (d % a : ℕ) - (a : ℤ) := by
  have hd : (d : ℤ) = (a : ℤ) * (d / a : ℕ) + (d % a : ℕ) := by
    exact_mod_cast (Nat.div_add_mod d a).symm
  rw [signedRemainder, quotient_upper_branch d a h]
  rw [Nat.cast_add, Nat.cast_one]
  nlinarith

theorem remainder_half_interval (d a : ℕ) (ha : 0 < a) :
    -(a : ℤ) < 2 * signedRemainder d a ∧
      2 * signedRemainder d a ≤ (a : ℤ) := by
  have hr := Nat.mod_lt d ha
  by_cases h : 2 * (d % a) ≤ a
  · rw [remainder_lower_branch d a h]
    constructor <;> omega
  · rw [remainder_upper_branch d a (by omega)]
    constructor <;> omega

theorem remainder_height_half (d a : ℕ) (ha : 0 < a) :
    2 * remainderHeight d a ≤ a := by
  obtain ⟨hlo, hhi⟩ := remainder_half_interval d a ha
  have h : 2 * |signedRemainder d a| ≤ (a : ℤ) := by
    rcases le_total 0 (signedRemainder d a) with hr | hr
    · rw [abs_of_nonneg hr]; omega
    · rw [abs_of_nonpos hr]; omega
  have h' : (2 : ℤ) * (remainderHeight d a : ℤ) ≤ (a : ℤ) := by
    simpa only [remainderHeight, Int.natCast_natAbs] using h
  exact_mod_cast h'

theorem quotient_nearest (d a : ℕ) (ha : 0 < a) (k : ℤ) :
    |signedRemainder d a| ≤ |(d : ℤ) - k * (a : ℤ)| := by
  obtain ⟨hlo, hhi⟩ := remainder_half_interval d a ha
  have heq : (d : ℤ) = signedRemainder d a + (nearestQuotient d a : ℤ) * a := by
    simp [signedRemainder]
  have ha' : (0 : ℤ) < a := by exact_mod_cast ha
  by_cases hk : k = (nearestQuotient d a : ℤ)
  · subst k; rfl
  rcases lt_or_gt_of_ne hk with hk | hk
  · have hb := le_abs_self ((d : ℤ) - k * a)
    rcases le_total 0 (signedRemainder d a) with hr | hr
    · rw [abs_of_nonneg hr]; nlinarith
    · rw [abs_of_nonpos hr]; nlinarith
  · have hb := neg_le_abs ((d : ℤ) - k * a)
    rcases le_total 0 (signedRemainder d a) with hr | hr
    · rw [abs_of_nonneg hr]; nlinarith
    · rw [abs_of_nonpos hr]; nlinarith

theorem quotient_tie_is_smaller (d a : ℕ) (ha : 0 < a) (k : ℤ)
    (hk : |(d : ℤ) - k * (a : ℤ)| = |signedRemainder d a|) :
    (nearestQuotient d a : ℤ) ≤ k := by
  obtain ⟨hlo, hhi⟩ := remainder_half_interval d a ha
  have heq : (d : ℤ) = signedRemainder d a + (nearestQuotient d a : ℤ) * a := by
    simp [signedRemainder]
  have ha' : (0 : ℤ) < a := by exact_mod_cast ha
  by_contra h
  have hk' : k + 1 ≤ (nearestQuotient d a : ℤ) := by omega
  have hb := le_abs_self ((d : ℤ) - k * a)
  rw [hk] at hb
  rcases le_total 0 (signedRemainder d a) with hr | hr
  · rw [abs_of_nonneg hr] at hb; nlinarith
  · rw [abs_of_nonpos hr] at hb; nlinarith

theorem exact_half_tie (d a : ℕ) (h : 2 * (d % a) = a) :
    nearestQuotient d a = d / a ∧
      signedRemainder d a = (d % a : ℕ) :=
  ⟨quotient_lower_branch d a (by omega), remainder_lower_branch d a (by omega)⟩

end NField.ResetForests.EuclideanFold

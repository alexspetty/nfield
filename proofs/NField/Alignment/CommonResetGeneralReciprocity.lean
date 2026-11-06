/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetBernoulliLifts

/-! # General three-modulus reciprocity, retaining all common factors -/

noncomputable section

namespace NField.Alignment.CommonResetGeneralReciprocity

open scoped BigOperators
open RademacherThreeTerm CommonResetBernoulliLifts

def reciprocityDefect (a b c : ℕ) : ℚ :=
  arithmeticCoefficientDedekindTerm b c a +
    arithmeticCoefficientDedekindTerm c a b +
    arithmeticCoefficientDedekindTerm a b c + (a.gcd b |>.gcd c : ℚ)/4 -
    ((a : ℚ)^2*(b.gcd c : ℚ)^2 + (b : ℚ)^2*(c.gcd a : ℚ)^2 +
      (c : ℚ)^2*(a.gcd b : ℚ)^2)/(12*a*b*c)

theorem reciprocityDefect_cycle (a b c : ℕ) :
    reciprocityDefect b c a = reciprocityDefect a b c := by
  have ht : (b.gcd c).gcd a = (a.gcd b).gcd c := by ac_rfl
  unfold reciprocityDefect
  rw [ht]
  ring

theorem reciprocityDefect_common_scale {d a b c : ℕ}
    (hd : 0 < d) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    reciprocityDefect (d*a) (d*b) (d*c) = d*reciprocityDefect a b c := by
  unfold reciprocityDefect
  rw [coefficient_common_scale hd ha, coefficient_common_scale hd hb,
    coefficient_common_scale hd hc]
  simp only [Nat.gcd_mul_left, Nat.cast_mul]
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
  have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have hcQ : (c : ℚ) ≠ 0 := by exact_mod_cast hc.ne'
  field_simp [hdQ, haQ, hbQ, hcQ]

theorem reciprocityDefect_pair_scale {d a b c : ℕ}
    (hd : 0 < d) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hdc : d.Coprime c) :
    reciprocityDefect (d*a) (d*b) c = reciprocityDefect a b c := by
  unfold reciprocityDefect
  rw [coefficient_swap (d*b) c, coefficient_strip hd ha hdc.symm,
    coefficient_strip hd hb hdc.symm, coefficient_unit_scale hc hdc,
    coefficient_swap c b]
  rw [Nat.gcd_mul_left]
  rw [Nat.Coprime.gcd_mul_left_cancel _ hdc,
    Nat.Coprime.gcd_mul_left_cancel _ hdc,
    Nat.Coprime.gcd_mul_left_cancel_right _ hdc]
  simp only [Nat.cast_mul]
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
  have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have hcQ : (c : ℚ) ≠ 0 := by exact_mod_cast hc.ne'
  field_simp [hdQ, haQ, hbQ, hcQ]

theorem reciprocityDefect_coprime {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a.Coprime b) (hac : a.Coprime c) (hbc : b.Coprime c) :
    reciprocityDefect a b c = 0 := by
  unfold reciprocityDefect
  rw [arithmeticCoefficientDedekindTerm_threeTerm ha hb hc hab hac hbc,
    hab.gcd_eq_one, hbc.gcd_eq_one, hac.symm.gcd_eq_one]
  simp only [Nat.gcd_one_left, Nat.cast_one, one_pow]
  have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
  have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have hcQ : (c : ℚ) ≠ 0 := by exact_mod_cast hc.ne'
  field_simp [haQ, hbQ, hcQ]
  ring

theorem reciprocityDefect_zero {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    reciprocityDefect a b c = 0 := by
  have main : ∀ s a b c : ℕ, a+b+c=s → 0<a → 0<b → 0<c → reciprocityDefect a b c=0 := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih =>
      intro a b c hs ha hb hc
      have step : ∀ x y z : ℕ, x+y+z=s → 0<x → 0<y → 0<z →
          ¬x.Coprime y → reciprocityDefect x y z=0 := by
        intro x y z hsum hx hy hz hxy
        obtain ⟨d, hd, hdx, hdy⟩ := Nat.Prime.not_coprime_iff_dvd.mp hxy
        obtain ⟨x, rfl⟩ := hdx
        obtain ⟨y, rfl⟩ := hdy
        have hx' := Nat.pos_of_mul_pos_left hx
        have hy' := Nat.pos_of_mul_pos_left hy
        by_cases hdz : d ∣ z
        · obtain ⟨z, rfl⟩ := hdz
          have hz' := Nat.pos_of_mul_pos_left hz
          have hlt : x+y+z < s := by nlinarith [hd.two_le]
          rw [reciprocityDefect_common_scale hd.pos hx' hy' hz',
            ih (x+y+z) hlt x y z rfl hx' hy' hz', mul_zero]
        · have hlt : x+y+z < s := by nlinarith [hd.two_le]
          rw [reciprocityDefect_pair_scale hd.pos hx' hy' hz
            (hd.coprime_iff_not_dvd.mpr hdz)]
          exact ih (x+y+z) hlt x y z rfl hx' hy' hz
      by_cases hab : a.Coprime b
      · by_cases hbc : b.Coprime c
        · by_cases hca : c.Coprime a
          · exact reciprocityDefect_coprime ha hb hc hab hca.symm hbc
          · rw [← reciprocityDefect_cycle, ← reciprocityDefect_cycle]
            exact step c a b (by omega) hc ha hb hca
        · rw [← reciprocityDefect_cycle]
          exact step b c a (by omega) hb hc ha hbc
      · exact step a b c hs ha hb hc hab
  exact main (a+b+c) a b c rfl ha hb hc

/-- Title: `Three-modulus reciprocity retains every common-factor correction`. -/
theorem three_modulus_reciprocity {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    arithmeticCoefficientDedekindTerm b c a +
      arithmeticCoefficientDedekindTerm c a b +
      arithmeticCoefficientDedekindTerm a b c =
    -(a.gcd b |>.gcd c : ℚ)/4 +
      ((a : ℚ)^2*(b.gcd c : ℚ)^2 + (b : ℚ)^2*(c.gcd a : ℚ)^2 +
        (c : ℚ)^2*(a.gcd b : ℚ)^2)/(12*a*b*c) := by
  have h := reciprocityDefect_zero ha hb hc
  unfold reciprocityDefect at h
  linarith

end NField.Alignment.CommonResetGeneralReciprocity

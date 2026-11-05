/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.IndexTwoOrbitEnergy

/-! # The printed power forms of the quadratic supplementary laws -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.QuadraticSupplementaryPowers
open scoped ZMod
open IndexTwoOrbitEnergy

theorem chi_eight_power {n : ℕ} (hn : n % 2 = 1) :
    ZMod.χ₈ n = (-1 : ℤ) ^ ((n ^ 2 - 1) / 8) := by
  rw [ZMod.χ₈_nat_eq_if_mod_eight, neg_one_pow_eq_pow_mod_two]
  have h16 : n % 16 < 16 := Nat.mod_lt _ (by decide)
  have hs : n ^ 2 % 16 = (n % 16) ^ 2 % 16 := Nat.pow_mod _ _ _
  have h82 : n % 8 % 2 = n % 2 := Nat.mod_mod_of_dvd n (by decide : 2 ∣ 8)
  have h168 : n % 16 % 8 = n % 8 := Nat.mod_mod_of_dvd n (by decide : 8 ∣ 16)
  interval_cases h : n % 16 <;> norm_num [h] at hs h168 <;>
    first
    | omega
    | have hd : (n ^ 2 - 1) / 8 % 2 = 0 := by omega
      simp [hn, hd, ← h168]
    | have hd : (n ^ 2 - 1) / 8 % 2 = 1 := by omega
      simp [hn, hd, ← h168]

theorem quadratic_supplementary_powers {q : ℕ} [Fact q.Prime]
    (hqodd : q ≠ 2) :
    complexQuadraticCharacter q (-1) = (-1 : ℂ) ^ ((q - 1) / 2) ∧
    complexQuadraticCharacter q 2 = (-1 : ℂ) ^ ((q ^ 2 - 1) / 8) := by
  have hp : q.Prime := Fact.out
  have hn : q % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hqodd)
  have hchar : ringChar (ZMod q) ≠ 2 := (ZMod.ringChar_zmod_n q).substr hqodd
  have hdiv : q / 2 = (q - 1) / 2 := by omega
  constructor
  · simp only [complexQuadraticCharacter, MulChar.ringHomComp_apply,
      quadraticChar_neg_one hchar, ZMod.card, ZMod.χ₄_eq_neg_one_pow hn, hdiv,
      map_pow, map_neg, map_one]
  · simp only [complexQuadraticCharacter, MulChar.ringHomComp_apply,
      quadraticChar_two hchar, ZMod.card, chi_eight_power hn,
      map_pow, map_neg, map_one]

end NField.Alignment.QuadraticSupplementaryPowers

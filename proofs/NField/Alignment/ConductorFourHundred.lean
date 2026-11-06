/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ConductorFourLifts

/-! # The exact conductor-four support on the units modulo one hundred -/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.ConductorFourHundred

open scoped BigOperators
open NField.Alignment.CollisionFluctuationSum
open NField.Alignment.DedekindReciprocity
open NField.Alignment.DedekindInverseResidueTransform
open NField.Alignment.GeneralNeutrality
open NField.Alignment.ConductorFourLifts

def unitSawtoothSum (k : ℕ) : ℚ :=
  ∑ a ∈ reducedResidues 100, (chiFourSign a : ℚ) * rationalSawtooth (k * a) 100

def signedUnitSawtoothSum (k : ℤ) : ℚ :=
  ∑ a ∈ reducedResidues 100, (chiFourSign a : ℚ) * signedSawtooth (k * a) 100

theorem chiFourSign_five_mul (a : ℕ) : chiFourSign (5 * a) = chiFourSign a := by
  simp [chiFourSign, Nat.mul_mod]

theorem unitSawtoothSum_sub_lifts (k : ℕ) :
    unitSawtoothSum k = conductorFourLift 25 k - conductorFourLift 5 k := by
  have hunit : reducedResidues 100 = (Finset.range 100).filter (fun a => a.Coprime 100) := by
    decide
  have hclass : ∀ a : Fin 100,
      a.val.Coprime 100 ↔ ¬5 ∣ a.val ∧ chiFourSign a.val ≠ 0 := by decide
  have hpoint (a : ℕ) (ha : a ∈ Finset.range 100) :
      (if a.Coprime 100 then (chiFourSign a : ℚ) * rationalSawtooth (k * a) 100 else 0) =
      (chiFourSign a : ℚ) * rationalSawtooth (k * a) 100 -
        if 5 ∣ a then (chiFourSign a : ℚ) * rationalSawtooth (k * a) 100 else 0 := by
    have hc := hclass ⟨a, Finset.mem_range.mp ha⟩
    by_cases h5 : 5 ∣ a
    · have hn : ¬a.Coprime 100 := by simpa [h5] using hc
      simp [h5, hn]
    · by_cases hcop : a.Coprime 100
      · simp [h5, hcop]
      · have hz : chiFourSign a = 0 := by simpa [h5, hcop] using hc
        simp [h5, hcop, hz]
  unfold unitSawtoothSum
  rw [hunit, Finset.sum_filter]
  calc
    _ = (∑ a ∈ Finset.range 100,
        (chiFourSign a : ℚ) * rationalSawtooth (k * a) 100) -
        ∑ a ∈ Finset.range 100,
          if 5 ∣ a then (chiFourSign a : ℚ) * rationalSawtooth (k * a) 100 else 0 := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl hpoint
    _ = conductorFourLift 25 k - conductorFourLift 5 k := by
      rw [sum_range_divisible_reindex (by decide : 0 < 5) (by decide : 5 ∣ 100)]
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      rw [chiFourSign_five_mul,
        show k * (5 * a) = 5 * (k * a) by ring,
        show 100 = 5 * 20 by decide,
        rationalSawtooth_scale (by decide : 0 < 5) (by decide : 0 < 20)]

theorem unitSawtoothSum_mod (k : ℕ) : unitSawtoothSum (k % 100) = unitSawtoothSum k := by
  unfold unitSawtoothSum
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  apply rationalSawtooth_eq_of_mod_eq
  simp [Nat.mul_mod]

theorem finite_support_formula : ∀ k : Fin 100,
    -(k.val.gcd 25 : ℚ) / 2 * (chiFourSign (k.val / k.val.gcd 25) : ℚ) -
      (-(k.val.gcd 5 : ℚ) / 2 * (chiFourSign (k.val / k.val.gcd 5) : ℚ)) =
      if 25 ∣ k.val then -10 * (chiFourSign (k.val / 25) : ℚ) else 0 := by
  decide +kernel

/-- Title: `The unit Bernoulli sum is supported exactly at multiples of twenty five`. -/
theorem unitSawtoothSum_support (k : ℕ) :
    unitSawtoothSum k = if 25 ∣ k then -10 * (chiFourSign (k / 25) : ℚ) else 0 := by
  rw [← unitSawtoothSum_mod k, unitSawtoothSum_sub_lifts,
    conductorFourLift_gcd (by decide : 0 < 25), conductorFourLift_gcd (by decide : 0 < 5)]
  rw [finite_support_formula ⟨k % 100, Nat.mod_lt _ (by decide : 0 < 100)⟩]
  have hd : 25 ∣ k % 100 ↔ 25 ∣ k := Nat.dvd_mod_iff (by decide : 25 ∣ 100)
  have hq : k % 100 / 25 = (k / 25) % 4 := Nat.mod_mul_right_div_self k 25 4
  simp only [hd, hq, chiFourSign, Nat.mod_mod]

theorem signedUnitSawtoothSum_natCast (k : ℕ) :
    signedUnitSawtoothSum k = unitSawtoothSum k := by
  simp only [signedUnitSawtoothSum, unitSawtoothSum, ← Nat.cast_mul, signedSawtooth_natCast]

theorem signedUnitSawtoothSum_neg_natCast (k : ℕ) :
    signedUnitSawtoothSum (-(k : ℤ)) = -unitSawtoothSum k := by
  simp only [signedUnitSawtoothSum, unitSawtoothSum, neg_mul, ← Nat.cast_mul,
    signedSawtooth_neg_natCast, mul_neg, Finset.sum_neg_distrib]

/-- Title: `The odd residues with multiples of five removed give the unit sum`. -/
theorem signedUnitSawtoothSum_sub_lifts (k : ℤ) :
    signedUnitSawtoothSum k = signedConductorFourLift 25 k - signedConductorFourLift 5 k := by
  obtain ⟨n, rfl | rfl⟩ := k.eq_nat_or_neg
  · simpa only [signedUnitSawtoothSum_natCast, signedConductorFourLift_natCast] using
      unitSawtoothSum_sub_lifts n
  · simp only [signedUnitSawtoothSum_neg_natCast, signedConductorFourLift_neg_natCast,
      unitSawtoothSum_sub_lifts]
    ring

/-- Title: `The conductor four support formula holds for every integer frequency`. -/
theorem signedUnitSawtoothSum_support (k : ℤ) :
    signedUnitSawtoothSum k =
      if (25 : ℤ) ∣ k then -10 * (signedChiFour (k / 25) : ℚ) else 0 := by
  obtain ⟨n, rfl | rfl⟩ := k.eq_nat_or_neg
  · have hd : (25 : ℤ) ∣ (n : ℤ) ↔ 25 ∣ n := by exact_mod_cast Iff.rfl
    have hdiv : (n : ℤ) / 25 = ((n / 25 : ℕ) : ℤ) := (Int.natCast_ediv n 25).symm
    simpa only [signedUnitSawtoothSum_natCast, hd, hdiv,
      signedChiFour_natCast] using unitSawtoothSum_support n
  · rw [signedUnitSawtoothSum_neg_natCast, unitSawtoothSum_support]
    by_cases hn : 25 ∣ n
    · have hd : (25 : ℤ) ∣ (n : ℤ) := by exact_mod_cast hn
      have hdiv : (n : ℤ) / 25 = ((n / 25 : ℕ) : ℤ) := (Int.natCast_ediv n 25).symm
      simp only [hn, if_true, dvd_neg, hd, Int.neg_ediv_of_dvd hd,
        hdiv, signedChiFour_neg_natCast, Int.cast_neg]
      ring
    · have hd : ¬(25 : ℤ) ∣ (n : ℤ) := by exact_mod_cast hn
      simp [hn, hd]

end NField.Alignment.ConductorFourHundred

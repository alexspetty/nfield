/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ConductorFourHundred

/-! # The literal integer floor transform in the conductor-four calculation -/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.ConductorFourFloors

open scoped BigOperators
open NField.Alignment.CollisionFluctuationSum
open NField.Alignment.DedekindReciprocity
open NField.Alignment.GeneralNeutrality
open NField.Alignment.ConductorFourLifts
open NField.Alignment.ConductorFourHundred

theorem rationalSawtooth_linear_floor {q : ℕ} (hq : 0 < q) (n : ℕ) :
    rationalSawtooth n q = (n : ℚ) / q - (n / q : ℕ) -
      if q ∣ n then 0 else (1 / 2 : ℚ) := by
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have heq : (n : ℚ) = (n % q : ℕ) + (q : ℚ) * (n / q : ℕ) := by
    exact_mod_cast (Nat.mod_add_div n q).symm
  by_cases hd : q ∣ n
  · have hm : n % q = 0 := Nat.dvd_iff_mod_eq_zero.mp hd
    simp only [rationalSawtooth, hm, if_true, hd, sub_zero, Nat.cast_zero] at *
    field_simp
    nlinarith
  · have hm : n % q ≠ 0 := by simpa only [Nat.dvd_iff_mod_eq_zero] using hd
    simp only [rationalSawtooth, hm, if_false, hd]
    field_simp
    nlinarith

theorem signedSawtooth_linear_floor {q : ℕ} (hq : 0 < q) (k : ℤ) :
    signedSawtooth k q = (k : ℚ) / q - (k / (q : ℤ) : ℤ) -
      if (q : ℤ) ∣ k then 0 else (1 / 2 : ℚ) := by
  obtain ⟨n, rfl | rfl⟩ := k.eq_nat_or_neg
  · simpa only [signedSawtooth_natCast, ← Int.natCast_ediv, Int.cast_natCast,
      Int.natCast_dvd_natCast] using rationalSawtooth_linear_floor hq n
  · have hsign : (q : ℤ).sign = 1 := Int.sign_eq_one_of_pos (by exact_mod_cast hq)
    rw [signedSawtooth_neg_natCast, rationalSawtooth_linear_floor hq, Int.neg_ediv]
    simp only [Int.cast_neg, dvd_neg, Int.natCast_dvd_natCast, hsign,
      ← Int.natCast_ediv, Int.cast_sub, Int.cast_natCast, Int.cast_ite,
      Int.cast_zero, Int.cast_one]
    split_ifs <;> ring

theorem signedSawtooth_floor_bridge {q : ℕ} (hq : 0 < q) (k : ℤ) :
    signedSawtooth k q = (k : ℚ) / q - (⌊(k : ℚ) / q⌋ : ℤ) -
      if (q : ℤ) ∣ k then 0 else (1 / 2 : ℚ) := by
  rw [Int.floor_div_natCast, Int.floor_intCast]
  exact signedSawtooth_linear_floor hq k

def unitFloorSum (k : ℤ) : ℚ :=
  ∑ a ∈ reducedResidues 100, (chiFourSign a : ℚ) * (⌊(k : ℚ) * a / 100⌋ : ℤ)

theorem chiFour_unit_sum : (∑ a ∈ reducedResidues 100, chiFourSign a) = 0 := by decide

theorem chiFour_unit_linear_sum :
    (∑ a ∈ reducedResidues 100, (chiFourSign a : ℚ) * a) = 0 := by decide +kernel

theorem hundred_dvd_unit_mul_iff (k : ℤ) {a : ℕ} (ha : a ∈ reducedResidues 100) :
    (100 : ℤ) ∣ k * a ↔ (100 : ℤ) ∣ k := by
  have hcop := (Finset.mem_filter.mp ha).2
  norm_num only [← Int.natAbs_dvd_natAbs, Int.natAbs_mul, Int.natAbs_natCast]
  exact hcop.symm.dvd_mul_right

/-- Title: `The character weighted integer floor transform equals its Bernoulli form`. -/
theorem unitFloorSum_eq_linear_sub_sawtooth (k : ℤ) :
    unitFloorSum k = (k : ℚ) / 100 *
      (∑ a ∈ reducedResidues 100, (chiFourSign a : ℚ) * a) - signedUnitSawtoothSum k := by
  have hzero : (∑ a ∈ reducedResidues 100, (chiFourSign a : ℚ)) = 0 := by
    exact_mod_cast chiFour_unit_sum
  have hpoint (a : ℕ) (ha : a ∈ reducedResidues 100) :
      (chiFourSign a : ℚ) * (⌊(k : ℚ) * a / 100⌋ : ℤ) =
      (k : ℚ) / 100 * ((chiFourSign a : ℚ) * a) -
        (chiFourSign a : ℚ) * signedSawtooth (k * a) 100 -
        (chiFourSign a : ℚ) * (if (100 : ℤ) ∣ k then 0 else (1 / 2 : ℚ)) := by
    have h := signedSawtooth_floor_bridge (by decide : 0 < 100) (k * a)
    norm_num only [Int.cast_mul, Int.cast_natCast, Nat.cast_ofNat] at h
    simp only [hundred_dvd_unit_mul_iff k ha] at h
    rw [h]
    ring
  unfold unitFloorSum
  calc
    _ = (k : ℚ) / 100 * (∑ a ∈ reducedResidues 100, (chiFourSign a : ℚ) * a) -
        signedUnitSawtoothSum k -
        (∑ a ∈ reducedResidues 100, (chiFourSign a : ℚ)) *
          (if (100 : ℤ) ∣ k then 0 else (1 / 2 : ℚ)) := by
      simp only [signedUnitSawtoothSum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl hpoint
    _ = _ := by rw [hzero]; ring

/-- Title: `The decimal conductor four floor transform has the exact sparse support`. -/
theorem unitFloorSum_support (k : ℤ) :
    unitFloorSum k = if (25 : ℤ) ∣ k then 10 * (signedChiFour (k / 25) : ℚ) else 0 := by
  rw [unitFloorSum_eq_linear_sub_sawtooth, chiFour_unit_linear_sum,
    signedUnitSawtoothSum_support]
  split_ifs <;> ring

theorem decimal_diagonal_explicit :
    CenteredCollisionSum.allLagDiagonal 10 1 =
      {0, 11, 22, 33, 44, 55, 66, 77, 88, 99} := by decide

theorem decimal_diagonal_linear_cancellation (c : ℚ) :
    -(10 : ℚ) * c + ∑ n ∈ CenteredCollisionSum.allLagDiagonal 10 1,
      (((n : ℚ) + 1) * c - (n : ℚ) * c) = 0 := by
  have hpoint (n : ℕ) : ((n : ℚ) + 1) * c - (n : ℚ) * c = c := by ring
  simp only [hpoint, Finset.sum_const,
    CenteredCollisionSum.allLagDiagonal_card (by decide : 2 ≤ 10) (by decide : 1 ≤ 1),
    pow_one, nsmul_eq_mul]
  ring

/-- Title: `Every floor term in the decimal conductor four packet cancels`. -/
theorem decimal_diagonal_floor_cancellation :
    -unitFloorSum 10 + ∑ n ∈ CenteredCollisionSum.allLagDiagonal 10 1,
      (unitFloorSum ((n : ℤ) + 1) - unitFloorSum n) = 0 := by
  rw [decimal_diagonal_explicit]
  norm_num [unitFloorSum_support, signedChiFour, chiFourSign]

end NField.Alignment.ConductorFourFloors

/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.SquareLockRemainingStrip
import NField.Alignment.CarrierPrefixPeriod

/-! # The exact six-level example at prime 101 and carrier 14 -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.SecondaryCarrierExample
open SquareLockCarrierMass CarrierStateSwitching

/-- Title: `The displacement at prime 101 and carrier 14`. -/
theorem displacement : centeredNaturalResidue (101^2) 14 = -5 := by decide

/-- Title: `The coefficient cutoff at prime 101 is four`. -/
theorem coefficient_cutoff : coefficientSquareLockCutoff 101 = 4 := by
  have h96 : Real.log (96 : ℝ) = 5*Real.log 2+Real.log 3 := by
    rw [show (96 : ℝ)=2^5*3 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  have h128 : Real.log (128 : ℝ) = 7*Real.log 2 := by
    rw [show (128 : ℝ)=2^7 by norm_num,Real.log_pow]
    norm_num
  have hlo := Real.log_le_log (by norm_num : (0 : ℝ) < 96) (by norm_num : (96 : ℝ) ≤ 101)
  have hhi := Real.log_le_log (by norm_num : (0 : ℝ) < 101) (by norm_num : (101 : ℝ) ≤ 128)
  have hl : (9/2 : ℝ) < Real.log 101 := by
    rw [h96] at hlo
    linarith [Real.log_two_gt_d9,Real.log_three_gt_d9]
  have hu : Real.log (101 : ℝ) < 5 := by
    rw [h128] at hhi
    linarith [Real.log_two_lt_d9]
  unfold coefficientSquareLockCutoff
  norm_num only [Nat.cast_ofNat]
  apply (Nat.floor_eq_iff (by positivity)).mpr
  constructor
  · rw [le_div_iff₀ (sq_pos_of_pos (by linarith : 0 < Real.log (101 : ℝ)))]
    norm_num
    nlinarith
  · rw [div_lt_iff₀ (sq_pos_of_pos (by linarith : 0 < Real.log (101 : ℝ)))]
    norm_num
    nlinarith

/-- Title: `The six floor-level residues`. -/
theorem floor_residues :
    ((100/1)%14, (100/2)%14, (100/3)%14, (100/4)%14, (100/5)%14, (100/6)%14) =
      (2,8,5,11,6,2) := by decide

/-- Title: `The six exact collar values`. -/
theorem collar_values :
    (carrierPrefix 101 14 (100/1), carrierPrefix 101 14 (100/2),
      carrierPrefix 101 14 (100/3), carrierPrefix 101 14 (100/4),
      carrierPrefix 101 14 (100/5), carrierPrefix 101 14 (100/6)) =
      ((-3/14 : ℚ),-13/14,-13/14,-3/14,-13/14,-3/14) := by
  have h := CarrierPrefixPeriod.carrierPrefix_eq_mod (by norm_num : 2 ≤ 14)
    (by decide : (101^2).Coprime 14)
  rw [h (100/1),h (100/2),h (100/3),h (100/4),h (100/5),h (100/6)]
  norm_num [carrierPrefix, RademacherThreeTerm.arithmeticCoefficientDedekindTerm,
    DedekindReciprocity.rationalSawtooth, Nat.Coprime, Finset.sum_Icc_succ_top,
    Finset.sum_range_succ]

/-- Title: `The six collars are negative and sum to minus twenty-four sevenths`. -/
theorem collar_sign_and_sum :
    (∀ h ∈ Finset.Icc 1 6, carrierPrefix 101 14 (100/h) < 0) ∧
      (∑ h ∈ Finset.Icc 1 6, carrierPrefix 101 14 (100/h)) = -24/7 := by
  have h := collar_values
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨h1,h2,h3,h4,h5,h6⟩
  constructor
  · intro h hh
    obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hh
    interval_cases h <;> simp_all <;> norm_num
  · norm_num [Finset.sum_Icc_succ_top,h1,h2,h3,h4,h5,h6]

end NField.Alignment.SecondaryCarrierExample

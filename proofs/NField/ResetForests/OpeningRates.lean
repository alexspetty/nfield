/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.NormalizedRate
import NField.Alignment.CommonResetCorrectedRate
/-! # The cited rate and the finite-contact correction on the original source -/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.RefinedBounds

open scoped Topology
open Filter
open NField.Alignment CommonResetSampling CommonResetCorrectedRate
open CostCriteria

def contact (p : OddPrime) : ℝ := ((p.val - 1 : ℕ) : ℝ) ^ 2 / (p.val : ℝ) ^ 2

def correctedSampleError (p : OddPrime) : ℝ := correctedDefect p.val

theorem corrected_error_literal (p : OddPrime) :
    correctedSampleError p = continuousEnergy (p.val - 1) -
      (sourceEnergy p.val / (p.val : ℝ) ^ 2 + contact p) := by
  have hp : (p.val : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr p.property.1.ne_zero
  rw [source_energy_sampled_energy]
  simp only [correctedSampleError, correctedDefect, contact]
  congr 2
  field_simp

theorem corrected_error_shift (p : OddPrime) :
    correctedSampleError p = sampleError p + (2 / (p.val : ℝ) - 1 / (p.val : ℝ) ^ 2) :=
  correctedDefect_centered p.property.1.one_le

theorem contact_complement (p : OddPrime) :
    1 - contact p = 2 / (p.val : ℝ) - 1 / (p.val : ℝ) ^ 2 := by
  have hp : (p.val : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr p.property.1.ne_zero
  unfold contact
  rw [Nat.cast_sub p.property.1.one_le, Nat.cast_one]
  field_simp
  ring

theorem contact_error_bound (p : OddPrime) :
    |contact p - 1| ≤ 2 / (p.val : ℝ) := by
  rw [abs_sub_comm, contact_complement]
  exact common_reset_residual p.property.1.one_le

theorem contact_factor (p : OddPrime) :
    contact p = (1 - 1 / (p.val : ℝ)) ^ 2 := by
  have hp : (p.val : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr p.property.1.ne_zero
  unfold contact
  rw [Nat.cast_sub p.property.1.one_le, Nat.cast_one]
  field_simp

theorem contact_limit : Tendsto contact primeAtTop (𝓝 1) := by
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub
    MagnitudeCubicLimits.reciprocal_base_limit).pow 2
  simpa only [← contact_factor, sub_zero, one_pow] using h

theorem contact_error_isBigO :
    Asymptotics.IsBigO primeAtTop (fun p => contact p - 1) (primePower (-1)) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨2, Eventually.of_forall ?_⟩
  intro p
  rw [Real.norm_eq_abs, Real.norm_of_nonneg
    (show 0 ≤ primePower (-1) p from Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  simpa only [primePower, Real.rpow_neg_one, div_eq_mul_inv, one_mul] using contact_error_bound p

theorem correction_isBigO {a : ℝ} (ha : -1 ≤ a) :
    Asymptotics.IsBigO primeAtTop (fun p => correctedSampleError p - sampleError p)
      (primePower a) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨2, Eventually.of_forall ?_⟩
  intro p
  have hp1 : (1 : ℝ) ≤ p.val := by exact_mod_cast p.property.1.one_le
  have hpow : 1 / (p.val : ℝ) ≤ primePower a p := by
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hp1 ha
  rw [Real.norm_eq_abs, Real.norm_of_nonneg
    (show 0 ≤ primePower a p from Real.rpow_nonneg (Nat.cast_nonneg _) _),
    corrected_error_shift, add_sub_cancel_left]
  exact (common_reset_residual p.property.1.one_le).trans
    (by simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 2))

theorem corrected_rate_iff {a : ℝ} (ha : -1 ≤ a) :
    Asymptotics.IsBigO primeAtTop sampleError (primePower a) ↔
      Asymptotics.IsBigO primeAtTop correctedSampleError (primePower a) := by
  constructor
  · intro h
    simpa only [Pi.add_apply, sub_add_cancel] using (correction_isBigO ha).add h
  · intro h
    simpa only [Pi.sub_apply, sub_sub_cancel] using h.sub (correction_isBigO ha)

theorem corrected_half_power_iff :
    HalfPowerConclusion ↔ ∀ ε : ℝ, 0 < ε →
      Asymptotics.IsBigO primeAtTop correctedSampleError (primePower (-1 / 2 + ε)) := by
  constructor
  · intro h ε hε
    exact (corrected_rate_iff (by linarith : (-1 : ℝ) ≤ -1 / 2 + ε)).mp (h ε hε)
  · intro h ε hε
    exact (corrected_rate_iff (by linarith : (-1 : ℝ) ≤ -1 / 2 + ε)).mpr (h ε hε)

theorem sample_error_quarter_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : OddPrime,
      |sampleError p| ≤ C * primePower (-1 / 4 + ε) p := by
  obtain ⟨C, hC, h⟩ := CommonResetQuarterPower.unit_sampling_defect_quarter_power ε hε
  exact ⟨C, hC, fun p => h p.val p.property.1 p.property.2⟩

theorem sample_error_quarter_isBigO (ε : ℝ) (hε : 0 < ε) :
    Asymptotics.IsBigO primeAtTop sampleError (primePower (-1 / 4 + ε)) := by
  obtain ⟨C, _, h⟩ := sample_error_quarter_power ε hε
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨C, Eventually.of_forall ?_⟩
  intro p
  simpa only [Real.norm_eq_abs, abs_of_nonneg
    (show 0 ≤ primePower (-1 / 4 + ε) p from Real.rpow_nonneg (Nat.cast_nonneg _) _)] using h p

theorem corrected_quarter_isBigO (ε : ℝ) (hε : 0 < ε) :
    Asymptotics.IsBigO primeAtTop correctedSampleError (primePower (-1 / 4 + ε)) :=
  (corrected_rate_iff (by linarith : (-1 : ℝ) ≤ -1 / 4 + ε)).mp
    (sample_error_quarter_isBigO ε hε)

theorem corrected_carry_quarter_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : OddPrime,
      |continuousEnergy (p.val - 1) -
        (CollisionBernoulliStraightening.collisionEnergy p.property.1 / (p.val : ℝ) ^ 2 +
          contact p)| ≤ C * primePower (-1 / 4 + ε) p := by
  obtain ⟨C, hC, h⟩ := corrected_sampling_quarter_power ε hε
  exact ⟨C, hC, fun p => h p.val p.property.1 p.property.2⟩

end NField.ResetForests.RefinedBounds

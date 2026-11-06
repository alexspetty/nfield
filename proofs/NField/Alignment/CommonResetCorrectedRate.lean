/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetQuarterPower

/-! # The published corrected finite energy at the common reset -/

noncomputable section

namespace NField.Alignment.CommonResetCorrectedRate

open CommonResetQuarterPower CommonResetSampling

def correctedDefect (p : ℕ) : ℝ := continuousEnergy (p-1)-
  (sampledEnergy (p-1) (p^2)+((p-1 : ℕ) : ℝ)^2/(p : ℝ)^2)

theorem correctedDefect_centered {p : ℕ} (hp : 1 ≤ p) :
    correctedDefect p = (defect (p-1) (p^2)-1)+(2/(p : ℝ)-1/(p : ℝ)^2) := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  unfold correctedDefect defect
  rw [Nat.cast_sub hp, Nat.cast_one]
  field_simp
  ring

theorem common_reset_residual {p : ℕ} (hp : 1 ≤ p) :
    |2/(p : ℝ)-1/(p : ℝ)^2| ≤ 2/(p : ℝ) := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hinv : 1/(p : ℝ)^2 ≤ 1/(p : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by linarith) (by nlinarith)
  have hpos : 0 ≤ 2/(p : ℝ)-1/(p : ℝ)^2 := by
    apply sub_nonneg.mpr
    exact hinv.trans (div_le_div_of_nonneg_right (by norm_num) (by linarith))
  rw [abs_of_nonneg hpos]
  have hnn : 0 ≤ 1/(p : ℝ)^2 := by positivity
  linarith

/-- Title: `Correcting the common reset removes the unit defect with the published quarter-power error`. -/
theorem corrected_sampling_quarter_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) (hp : p.Prime), p ≠ 2 →
      |continuousEnergy (p-1)-
        (CollisionBernoulliStraightening.collisionEnergy hp/(p : ℝ)^2+
          ((p-1 : ℕ) : ℝ)^2/(p : ℝ)^2)| ≤ C*(p : ℝ)^(-1/4+ε) := by
  obtain ⟨C, hC, hc⟩ := unit_sampling_defect_quarter_power ε hε
  refine ⟨C+2, by positivity, ?_⟩
  intro p hp hodd
  have he : continuousEnergy (p-1)-
      (CollisionBernoulliStraightening.collisionEnergy hp/(p : ℝ)^2+
        ((p-1 : ℕ) : ℝ)^2/(p : ℝ)^2) = correctedDefect p := by
    unfold correctedDefect
    rw [sampledEnergy_prime hp]
  rw [he, correctedDefect_centered hp.one_le]
  calc
    _ ≤ |defect (p-1) (p^2)-1|+|2/(p : ℝ)-1/(p : ℝ)^2| := abs_add_le _ _
    _ ≤ C*(p : ℝ)^(-1/4+ε)+2/(p : ℝ) := add_le_add (hc p hp hodd) (common_reset_residual hp.one_le)
    _ ≤ C*(p : ℝ)^(-1/4+ε)+2*(p : ℝ)^(-1/4+ε) := by
      apply add_le_add (le_refl _)
      convert mul_le_mul_of_nonneg_left (inverse_le_quarter_scale hp.one_le hε) (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring
    _ = _ := by ring

end NField.Alignment.CommonResetCorrectedRate

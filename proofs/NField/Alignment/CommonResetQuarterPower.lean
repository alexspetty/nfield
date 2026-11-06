/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetSourceRate

/-! # The published unit sampling defect and original carry-energy rate -/

noncomputable section

namespace NField.Alignment.CommonResetQuarterPower

open scoped BigOperators
open CommonResetSampling CommonResetSourceRate CommonResetBudget CommonResetSmallConductors

theorem harmonic_le_nat (n : ℕ) : (harmonic n : ℝ) ≤ n := by
  by_cases hn : n=0
  · subst n
    simp
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hh := harmonic_le_one_add_log n
  have hl := Real.log_le_sub_one_of_pos hnR
  linarith

def residualCorrection (p : ℕ) : ℝ :=
  ((p-1 : ℕ) : ℝ)*(harmonic (p-1) : ℝ)/(3*(p : ℝ)^3)

theorem residualCorrection_nonneg (p : ℕ) : 0 ≤ residualCorrection p := by
  have hh := harmonic_nonneg (p-1)
  unfold residualCorrection
  positivity

theorem residualCorrection_le {p : ℕ} (hp : 1 ≤ p) : residualCorrection p ≤ 1/(p : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hN : ((p-1 : ℕ) : ℝ) ≤ p := Nat.cast_le.mpr (Nat.sub_le p 1)
  have hH : (harmonic (p-1) : ℝ) ≤ p := (harmonic_le_nat _).trans hN
  calc
    residualCorrection p ≤ ((p : ℝ)*(p : ℝ))/(3*(p : ℝ)^3) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul hN hH (harmonic_nonneg _) (Nat.cast_nonneg _)
    _ = (1/3)/(p : ℝ) := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_right (by norm_num) hpR.le

theorem correction_total_le {p : ℕ} (hp : 1 ≤ p) :
    2/(p : ℝ)+1/(p : ℝ)^2+residualCorrection p ≤ 4/(p : ℝ) := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hinv : 1/(p : ℝ)^2 ≤ 1/(p : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by linarith) (by nlinarith)
  have hr := residualCorrection_le hp
  calc
    _ ≤ 2/(p : ℝ)+1/(p : ℝ)+1/(p : ℝ) := add_le_add (add_le_add (le_refl _) hinv) hr
    _ = _ := by ring

theorem inverse_le_quarter_scale {p : ℕ} (hp : 1 ≤ p) {ε : ℝ} (hε : 0 < ε) :
    1/(p : ℝ) ≤ (p : ℝ)^(-1/4+ε) := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  calc
    _ = (p : ℝ)^(-1 : ℝ) := by rw [Real.rpow_neg_one, one_div]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hpR (by linarith)

theorem source_scale_div_square {p : ℕ} (hp : 0 < p) (C ε : ℝ) :
    4*(C*(p : ℝ)^(7/4+ε))/(p : ℝ)^2 = (4*C)*(p : ℝ)^(-1/4+ε) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  calc
    _ = (4*C)*((p : ℝ)^(7/4+ε)/(p : ℝ)^2) := by ring
    _ = _ := by rw [← Real.rpow_two, ← Real.rpow_sub hpR]; congr 2; ring

/-- Title: `The actual unit sampling defect has the published quarter-power rate along every odd prime`. -/
theorem unit_sampling_defect_quarter_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime → p ≠ 2 →
      |defect (p-1) (p^2)-1| ≤ C*(p : ℝ)^(-1/4+ε) := by
  obtain ⟨C, hC, hc⟩ := complete_source_quarter_power ε hε
  refine ⟨4*C+4, by positivity, ?_⟩
  intro p hp hodd
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hsource := hc p hp
  have hcorr := residualCorrection_nonneg p
  have hidentity : defect (p-1) (p^2)-1 =
      4*interiorSource (p-1) (p^2)/(p : ℝ)^2+(-(2/(p : ℝ)))+
        1/(p : ℝ)^2+(-residualCorrection p) := by
    rw [prime_square_centered_identity hp hodd]
    unfold residualCorrection
    ring
  calc
    _ ≤ 4*|interiorSource (p-1) (p^2)|/(p : ℝ)^2+
        2/(p : ℝ)+1/(p : ℝ)^2+residualCorrection p := by
      rw [hidentity]
      have hh := abs_four_sum (4*interiorSource (p-1) (p^2)/(p : ℝ)^2)
        (-(2/(p : ℝ))) (1/(p : ℝ)^2) (-residualCorrection p)
      simpa only [abs_neg, abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
        abs_of_nonneg hpR.le, abs_of_nonneg (sq_nonneg (p : ℝ)), abs_of_nonneg hcorr,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_one] using hh
    _ ≤ 4*(C*(p : ℝ)^(7/4+ε))/(p : ℝ)^2+4/(p : ℝ) := by
      have hmain := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsource (by norm_num : (0 : ℝ) ≤ 4)) (sq_nonneg (p : ℝ))
      linarith [correction_total_le hp.one_le]
    _ = (4*C)*(p : ℝ)^(-1/4+ε)+4/(p : ℝ) := by rw [source_scale_div_square hp.pos]
    _ ≤ (4*C)*(p : ℝ)^(-1/4+ε)+4*(p : ℝ)^(-1/4+ε) := by
      apply add_le_add (le_refl _)
      convert mul_le_mul_of_nonneg_left (inverse_le_quarter_scale hp.one_le hε) (by norm_num : (0 : ℝ) ≤ 4) using 1 <;> ring
    _ = _ := by ring

theorem energy_sampling_remainder {p : ℕ} (hp : p.Prime) :
    CollisionBernoulliStraightening.collisionEnergy hp-(p : ℝ)^2*(continuousEnergy (p-1)-1) =
      -(p : ℝ)^2*(defect (p-1) (p^2)-1) := by
  unfold defect
  rw [sampledEnergy_prime hp]
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  field_simp
  ring

theorem multiply_quarter_scale {p : ℕ} (hp : 0 < p) (C ε : ℝ) :
    (p : ℝ)^2*(C*(p : ℝ)^(-1/4+ε)) = C*(p : ℝ)^(7/4+ε) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  calc
    _ = C*((p : ℝ)^2*(p : ℝ)^(-1/4+ε)) := by ring
    _ = _ := by rw [← Real.rpow_two, ← Real.rpow_add hpR]; congr 2; ring

/-- Title: `The original finite carry energy has the equivalent seven-quarter-plus-epsilon remainder`. -/
theorem original_carry_energy_quarter_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) (hp : p.Prime), p ≠ 2 →
      |CollisionBernoulliStraightening.collisionEnergy hp-(p : ℝ)^2*(continuousEnergy (p-1)-1)| ≤
        C*(p : ℝ)^(7/4+ε) := by
  obtain ⟨C, hC, hc⟩ := unit_sampling_defect_quarter_power ε hε
  refine ⟨C, hC, ?_⟩
  intro p hp hodd
  rw [energy_sampling_remainder hp, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg (p : ℝ))]
  calc
    _ ≤ (p : ℝ)^2*(C*(p : ℝ)^(-1/4+ε)) := mul_le_mul_of_nonneg_left (hc p hp hodd) (sq_nonneg _)
    _ = _ := multiply_quarter_scale hp.pos C ε

end NField.Alignment.CommonResetQuarterPower

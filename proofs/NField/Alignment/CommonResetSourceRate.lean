/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetBudget

/-! # The published quarter-power cutoff choice for the complete source -/

noncomputable section

namespace NField.Alignment.CommonResetSourceRate

open scoped BigOperators
open CommonResetBudget CommonResetSampling

def quarterFrequency (p : ℕ) : ℕ := Nat.ceil ((p : ℝ)^(1/4 : ℝ))

theorem quarterFrequency_pos {p : ℕ} (hp : 1 ≤ p) : 0 < quarterFrequency p := by
  apply Nat.ceil_pos.mpr
  exact Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < p by omega)) _

theorem quarterFrequency_le {p : ℕ} (hp : 1 ≤ p) : quarterFrequency p ≤ p := by
  apply Nat.ceil_le.mpr
  calc
    _ ≤ (p : ℝ)^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp) (by norm_num)
    _ = _ := Real.rpow_one _

theorem quarterFrequency_upper {p : ℕ} (hp : 1 ≤ p) :
    (quarterFrequency p : ℝ) ≤ 2*(p : ℝ)^(1/4 : ℝ) := by
  have hone := Real.one_le_rpow (show (1 : ℝ) ≤ p by exact_mod_cast hp) (by norm_num : (0 : ℝ) ≤ 1/4)
  have hh := Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg p) (1/4 : ℝ))
  change (quarterFrequency p : ℝ) < (p : ℝ)^(1/4 : ℝ)+1 at hh
  linarith

theorem quarterFrequency_tail {p : ℕ} (hp : 1 ≤ p) :
    (p : ℝ)^2/(quarterFrequency p : ℝ) ≤ (p : ℝ)^(7/4 : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  calc
    _ ≤ (p : ℝ)^2/((p : ℝ)^(1/4 : ℝ)) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (Real.rpow_pos_of_pos hpR _)
        (Nat.le_ceil ((p : ℝ)^(1/4 : ℝ)))
    _ = _ := by rw [← Real.rpow_two, ← Real.rpow_sub hpR]; norm_num

/-- Title: `The two published ceiling cutoffs give the seven-quarter complete-source scale`. -/
theorem quarter_frequency_budget {p : ℕ} (hp : 1 ≤ p) :
    budgetScale p (quarterFrequency p) (quarterFrequency p) ≤ 5*(p : ℝ)^(7/4 : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hone := Real.one_le_rpow (show (1 : ℝ) ≤ p by exact_mod_cast hp) (by norm_num : (0 : ℝ) ≤ 1/4)
  have hq := quarterFrequency_upper hp
  have hfirst : (p : ℝ)^(3/2 : ℝ)*((quarterFrequency p : ℝ)+1) ≤ 3*(p : ℝ)^(7/4 : ℝ) := by
    calc
      _ ≤ (p : ℝ)^(3/2 : ℝ)*(3*(p : ℝ)^(1/4 : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hpR.le _)
      _ = _ := by
        rw [show (p : ℝ)^(3/2 : ℝ)*(3*(p : ℝ)^(1/4 : ℝ)) =
          3*((p : ℝ)^(3/2 : ℝ)*(p : ℝ)^(1/4 : ℝ)) by ring]
        rw [← Real.rpow_add hpR]
        norm_num
  unfold budgetScale
  rw [Real.sqrt_mul_self (Nat.cast_nonneg _)]
  linarith [quarterFrequency_tail hp]

/-- Title: `The complete original signed interior source has the seven-quarter-plus-epsilon bound`. -/
theorem complete_source_quarter_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime →
      |interiorSource (p-1) (p^2)| ≤ C*(p : ℝ)^(7/4+ε) := by
  obtain ⟨C, hC, hc⟩ := complete_frequency_budget ε hε
  refine ⟨5*C, by positivity, ?_⟩
  intro p hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hb := hc p (quarterFrequency p) (quarterFrequency p) hp
    (quarterFrequency_pos hp.one_le) (quarterFrequency_le hp.one_le)
    (quarterFrequency_pos hp.one_le) (quarterFrequency_le hp.one_le)
  calc
    _ ≤ C*(p : ℝ)^ε*budgetScale p (quarterFrequency p) (quarterFrequency p) := hb
    _ ≤ C*(p : ℝ)^ε*(5*(p : ℝ)^(7/4 : ℝ)) :=
      mul_le_mul_of_nonneg_left (quarter_frequency_budget hp.one_le) (by positivity)
    _ = _ := by
      rw [show C*(p : ℝ)^ε*(5*(p : ℝ)^(7/4 : ℝ)) =
        (5*C)*((p : ℝ)^(7/4 : ℝ)*(p : ℝ)^ε) by ring, ← Real.rpow_add hpR]

end NField.Alignment.CommonResetSourceRate

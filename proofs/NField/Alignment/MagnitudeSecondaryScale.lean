/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.MagnitudeSecondaryTransfer
import NField.Alignment.PrimeSecondaryCoefficient

/-! # The exact logarithmic remainder scale under rational normalization -/

noncomputable section
namespace NField.Alignment.MagnitudeSecondaryTransfer

open PrimeSecondaryCoefficient

theorem printed_scale_bounds (p : ℕ) (hp : 3 ≤ p) :
    1 ≤ primePrintedSamplingScale p ∧
      (Real.log (p : ℝ))^2 ≤ (p : ℝ)*primePrintedSamplingScale p := by
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hlogp : 1 ≤ Real.log (p : ℝ) :=
    (Real.le_log_iff_exp_le hp0).mpr (Real.exp_one_lt_three.le.trans hp3)
  have hmono : Real.log (p : ℝ) ≤ Real.log (2*(p : ℝ)) :=
    Real.log_le_log hp0 (by linarith)
  have hlog2p : 1 ≤ Real.log (2*(p : ℝ)) := hlogp.trans hmono
  have hlog3p : Real.log (3*(p : ℝ)) ≤ 2*Real.log (p : ℝ) := by
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hp0.ne']
    have hthree := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hp3
    linarith
  have hlog3pos : 0 < Real.log (3*(p : ℝ)) := Real.log_pos (by nlinarith)
  have hden : 0 < Real.log (Real.log (3*(p : ℝ))) := by
    apply Real.log_pos
    exact (Real.lt_log_iff_exp_lt (by positivity)).mpr (by
      have h := Real.exp_one_lt_three
      nlinarith)
  have hlogple : Real.log (p : ℝ) ≤ (p : ℝ)-1 := Real.log_le_sub_one_of_pos hp0
  have hdenle : Real.log (Real.log (3*(p : ℝ))) ≤ Real.log (2*(p : ℝ)) :=
    Real.log_le_log hlog3pos (by linarith)
  have htlep : Real.log (2*(p : ℝ)) ≤ (p : ℝ) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hp0.ne']
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hL : (Real.log (p : ℝ))^2 ≤ (Real.log (2*(p : ℝ)))^2 := by nlinarith
  unfold primePrintedSamplingScale
  constructor
  · apply (le_div_iff₀ hden).mpr
    nlinarith
  · rw [← mul_div_assoc]
    apply (le_div_iff₀ hden).mpr
    calc
      _ ≤ (Real.log (p : ℝ))^2*(p : ℝ) :=
        mul_le_mul_of_nonneg_left (hdenle.trans htlep) (sq_nonneg _)
      _ ≤ (Real.log (2*(p : ℝ)))^2*(p : ℝ) :=
        mul_le_mul_of_nonneg_right hL hp0.le
      _ = _ := by ring

end NField.Alignment.MagnitudeSecondaryTransfer

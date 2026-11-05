/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperSuffixLogTail

/-!
# Summing the actual single-scale failure bounds

The one-scale code count cancels one logarithmic block factor. Reversed
block growth leaves a summable inverse cube; no product of code counts
over earlier scales is introduced.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperExceptionalScaleSum
open scoped BigOperators
open HarperFrequencyMesh HarperGoodAllowance HarperReversedGoodPath

def scaleTailConstant : ℝ := 1+∑' n : ℕ, 1/((n : ℝ)+1)^3

theorem scaleTailConstant_pos : 0 < scaleTailConstant := by
  have h : 0 ≤ ∑' n : ℕ, 1/((n : ℝ)+1)^3 := tsum_nonneg (fun n => by positivity)
  unfold scaleTailConstant
  linarith

theorem shifted_inverse_cube_summable : Summable (fun n : ℕ => 1/((n : ℝ)+1)^3) := by
  have h := (summable_nat_add_iff 1).mpr
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (3 : ℕ)))
  simpa only [Nat.cast_add,Nat.cast_one] using h

theorem inverse_cube_scale_sum {x : ℝ} (hx : 1 < x) (M : ℕ)
    (hc : 1 ≤ terminalLogScale x M) :
    (∑ j : Fin (M+1), 1/(Real.log (logScale x j.val))^3) ≤ scaleTailConstant := by
  have he : (∑ j : Fin (M+1), 1/(Real.log (logScale x j.val))^3) =
      ∑ i : Fin (M+1), 1/(terminalLogScale x M+(i.val : ℝ))^3 := by
    calc
      _ = ∑ i : Fin (M+1), 1/(Real.log (logScale x (Fin.revPerm i).val))^3 :=
        (Equiv.sum_comp Fin.revPerm (fun i : Fin (M+1) => 1/(Real.log (logScale x i.val))^3)).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        have hi : (Fin.revPerm i).val = reverseIndex M i := by simp [reverseIndex,Fin.revPerm]
        rw [hi,reversed_log_logScale hx]
  rw [he]
  calc
    _ ≤ ∑ i : Fin (M+1), 1/((i.val : ℝ)+1)^3 := by
      apply Finset.sum_le_sum
      intro i _
      apply one_div_le_one_div_of_le (by positivity : 0 < ((i.val : ℝ)+1)^3)
      exact pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (i.val : ℝ)+1)
        (by linarith : (i.val : ℝ)+1 ≤ terminalLogScale x M+(i.val : ℝ)) 3
    _ ≤ ∑' n : ℕ, 1/((n : ℝ)+1)^3 := by
      rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => 1/((n : ℝ)+1)^3)]
      exact shifted_inverse_cube_summable.sum_le_tsum _ (fun n _ => by positivity)
    _ ≤ _ := by unfold scaleTailConstant; linarith

theorem code_weight_tail_bound {L E : ℝ} (hL : Real.exp 2 ≤ L) (hE : 0 ≤ E) :
    (2/(1/(L*Real.log L))+3)*(E/(L*(Real.log L)^4)) ≤ 5*E/(Real.log L)^3 := by
  have hL1 : 1 < L := lt_of_lt_of_le
    (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 2)) hL
  have hl : 2 ≤ Real.log L := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 2) hL
  have hL0 : L ≠ 0 := by linarith
  have hl0 : Real.log L ≠ 0 := by linarith
  have hcode : 2/(1/(L*Real.log L))+3 ≤ 5*(L*Real.log L) := by
    simp only [one_div,div_inv_eq_mul]
    nlinarith
  calc
    _ ≤ 5*(L*Real.log L)*(E/(L*(Real.log L)^4)) :=
      mul_le_mul_of_nonneg_right hcode (by positivity)
    _ = _ := by field_simp

end NField.Alignment.HarperExceptionalScaleSum

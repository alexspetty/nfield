/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperReversedGoodPath

/-!
# The exact source allowance fits the proved barrier

Writing c=log(log(blockUpper(x,M))), reverse time gives log(L_j)=c+r-1.
The critical good-event allowance is bounded by r+A+10*log(r), with
A=a+c+2*log(c+1). Its negative lies above -A-11*r. The lower slope is
the fixed number eleven, independent of the source-size offset.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperGoodAllowance
open HarperPrimeBlocks HarperFrequencyMesh HarperCriticalGoodEvent HarperReversedGoodPath

def terminalLogScale (x : ℝ) (M : ℕ) : ℝ := Real.log (logScale x M)
def pathAmplitude (x : ℝ) (M : ℕ) (a : ℝ) : ℝ :=
  a+terminalLogScale x M+2*Real.log (terminalLogScale x M+1)

theorem log_logScale_eq {x : ℝ} (hx : 1 < x) (j : ℕ) :
    Real.log (logScale x j) = Real.log (Real.log x)-((j : ℝ)+1) := by
  rw [logScale_eq (by linarith : 0 < x),
    Real.log_mul (ne_of_gt (Real.exp_pos _)) (ne_of_gt (Real.log_pos hx)),Real.log_exp]
  ring

theorem reversed_log_logScale {x : ℝ} (hx : 1 < x) (M : ℕ) (i : Fin (M+1)) :
    Real.log (logScale x (reverseIndex M i)) = terminalLogScale x M+(i.val : ℝ) := by
  unfold terminalLogScale
  rw [log_logScale_eq hx,log_logScale_eq hx]
  dsimp [reverseIndex]
  rw [Nat.cast_sub (show i.val ≤ M by omega)]
  ring

theorem pathAmplitude_ge_one {x a : ℝ} (M : ℕ) (ha : 0 ≤ a)
    (hc : 1 ≤ terminalLogScale x M) : 1 ≤ pathAmplitude x M a := by
  have hlog : 0 ≤ Real.log (terminalLogScale x M+1) := Real.log_nonneg (by linarith)
  unfold pathAmplitude
  linarith

theorem allowance_upper_arithmetic {c a r : ℝ} (hc : 1 ≤ c) (hr : 1 ≤ r) :
    c+r-1+a+2*Real.log (c+r-1) ≤ r+(a+c+2*Real.log (c+1))+10*Real.log r := by
  have hp : 0 < c+r-1 := by linarith
  have hlog : Real.log (c+r-1) ≤ Real.log (c+1)+Real.log r := by
    calc
      _ ≤ Real.log ((c+1)*r) := Real.log_le_log hp (by nlinarith)
      _ = _ := Real.log_mul (by linarith : c+1 ≠ 0) (by linarith : r ≠ 0)
  have hn : 0 ≤ Real.log r := Real.log_nonneg hr
  linarith

theorem sourceAllowance_upper {x : ℝ} (hx : 1 < x) (M : ℕ)
    (hc : 1 ≤ terminalLogScale x M) (a : ℝ) (i : Fin (M+1)) :
    sourceAllowance x a (reverseIndex M i) ≤
      ((i.val : ℝ)+1)+pathAmplitude x M a+10*Real.log ((i.val : ℝ)+1) := by
  unfold sourceAllowance
  rw [reversed_log_logScale hx]
  have h := allowance_upper_arithmetic (a := a) hc
    (show (1 : ℝ) ≤ (i.val : ℝ)+1 from le_add_of_nonneg_left (Nat.cast_nonneg _))
  simpa only [← add_assoc,add_sub_cancel_right,pathAmplitude] using h

theorem sourceAllowance_lower {x : ℝ} (hx : 1 < x) (M : ℕ)
    (hc : 1 ≤ terminalLogScale x M) (a : ℝ) (i : Fin (M+1)) :
    -pathAmplitude x M a-11*((i.val : ℝ)+1) ≤ -sourceAllowance x a (reverseIndex M i) := by
  have h := sourceAllowance_upper hx M hc a i
  have hl : Real.log ((i.val : ℝ)+1) ≤ (i.val : ℝ)+1 :=
    (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
  linarith

end NField.Alignment.HarperGoodAllowance

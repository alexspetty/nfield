/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ReciprocalArcBlock
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # The literal two-thirds power scale in square-lock counting -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.SquareLockCountScales

def countScale (X C : ℝ) : ℝ := C+X^(2/3:ℝ)

theorem countScale_bounds (X C : ℝ) (hX : 1 ≤ X) (hC : 0 ≤ C) :
    0 < countScale X C ∧ C ≤ countScale X C ∧ X^2 ≤ (countScale X C)^3 := by
  have hX0 : 0 < X := by linarith
  have hp : 0 < X^(2/3:ℝ) := Real.rpow_pos_of_pos hX0 _
  have he : (X^(2/3:ℝ))^3 = X^2 := by
    rw [← Real.rpow_mul_natCast hX0.le]
    norm_num
  refine ⟨by dsimp [countScale]; linarith,by dsimp [countScale]; linarith,?_⟩
  rw [← he]
  apply pow_le_pow_left₀ hp.le
  dsimp [countScale]
  linarith

theorem block_log_scale (p : ℕ) (X C : ℝ) (hp : 1 ≤ p)
    (hpX : (p:ℝ) ≤ X) (hC : 0 ≤ C) :
    (p:ℝ)*(1+Real.log (p:ℝ)) ≤ 4*(countScale X C)^2 := by
  have hp1 : (1:ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0:ℝ) < p := by linarith
  have hX1 : 1 ≤ X := hp1.trans hpX
  have hX0 : 0 < X := by linarith
  let y := X^(1/3:ℝ)
  have hy : 1 ≤ y := Real.one_le_rpow hX1 (by norm_num)
  have hy0 : 0 ≤ y := by linarith
  have hy3 : y^3 = X := by
    dsimp [y]
    rw [← Real.rpow_mul_natCast hX0.le]
    norm_num
  have hy2 : y^2 = X^(2/3:ℝ) := by
    dsimp [y]
    rw [← Real.rpow_mul_natCast hX0.le]
    norm_num
  have hlog : Real.log (p:ℝ) ≤ 3*y := by
    have hl := (Real.log_le_log hp0 hpX).trans
      (Real.log_le_rpow_div hX0.le (by norm_num : (0:ℝ)<1/3))
    simpa [y,div_eq_mul_inv,mul_comm] using hl
  have hT : y^2 ≤ countScale X C := by
    rw [hy2]
    dsimp [countScale]
    linarith
  have hb : (p:ℝ)*(1+Real.log (p:ℝ)) ≤ 4*y^4 := by
    calc
      _ ≤ X*(4*y) := mul_le_mul hpX (by linarith)
        (by linarith [Real.log_nonneg hp1]) hX0.le
      _ = _ := by rw [← hy3]; ring
  apply hb.trans
  have hh := pow_le_pow_left₀ (sq_nonneg y) hT 2
  nlinarith

theorem dyadic_count_log_bound (Y : ℕ) (X : ℝ) (hY : 1 ≤ Y)
    (hYX : (Y:ℝ) ≤ X) :
    (Nat.log 2 Y:ℝ) ≤ 2*Real.log (2*X) := by
  have hY0 : (0:ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
  have hX0 : 0 < X := hY0.trans_le hYX
  have hlog2 : (1/2:ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hlogY : 0 ≤ Real.log (Y:ℝ) := Real.log_nonneg (by exact_mod_cast hY)
  calc
    _ ≤ Real.logb 2 Y := Real.natLog_le_logb Y 2
    _ = Real.log (Y:ℝ)/Real.log 2 := rfl
    _ ≤ 2*Real.log (Y:ℝ) := by
      apply (div_le_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr
      nlinarith
    _ ≤ 2*Real.log (2*X) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Real.log_le_log hY0 (by linarith)

end NField.Alignment.SquareLockCountScales

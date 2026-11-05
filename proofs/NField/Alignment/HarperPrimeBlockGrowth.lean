/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperPrimeBlocks

/-!
# Growth and interval widths along a reversed finite block sequence

Strictly decreasing natural block indices force exponentially separated
upper endpoints. This controls the one-based widths 1/(i+1)^2 uniformly
in the number of blocks. Nonempty families use Fin (n+1), so no zero-width
index or impossible infinite decreasing sequence is assumed.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperPrimeBlockGrowth
open HarperPrimeBlocks

theorem strictAnti_index_gap {n : ℕ} {l : Fin (n+1) → ℕ} (hl : StrictAnti l)
    (i : Fin (n+1)) : l i+i.val ≤ l 0 := by
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
    have h : l i.succ < l i.castSucc := hl Fin.castSucc_lt_succ
    change l i.castSucc+i.val ≤ l 0 at ih
    change l i.succ+(i.val+1) ≤ l 0
    omega

theorem blockUpper_growth {x : ℝ} (hx : 1 ≤ x) {i j k : ℕ} (hgap : j+k ≤ i) :
    (blockUpper x i)^(Real.exp (k : ℝ)) ≤ blockUpper x j := by
  unfold blockUpper
  rw [← Real.rpow_mul (by linarith : 0 ≤ x)]
  apply Real.rpow_le_rpow_of_exponent_le hx
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h : (j : ℝ)+k ≤ i := by exact_mod_cast hgap
  linarith

theorem reversed_block_growth {x : ℝ} (hx : 1 ≤ x) {n : ℕ}
    {l : Fin (n+1) → ℕ} (hl : StrictAnti l) (i : Fin (n+1)) :
    (blockUpper x (l 0))^(Real.exp (i.val : ℝ)) ≤ blockUpper x (l i) :=
  blockUpper_growth hx (strictAnti_index_gap hl i)

theorem reversed_block_log_growth {x : ℝ} (hx : 1 < x) {n : ℕ}
    {l : Fin (n+1) → ℕ} (hl : StrictAnti l) (i : Fin (n+1)) :
    Real.exp (i.val : ℝ)*Real.log (blockUpper x (l 0)) ≤
      Real.log (blockUpper x (l i)) := by
  have h := Real.log_le_log
    (Real.rpow_pos_of_pos (by linarith [blockUpper_gt_one hx (l 0)]) _)
    (reversed_block_growth hx.le hl i)
  rwa [Real.log_rpow (by linarith [blockUpper_gt_one hx (l 0)] : 0 < blockUpper x (l 0))] at h

theorem reversed_block_log_ge {x : ℝ} (hx : 1 < x) {n : ℕ}
    {l : Fin (n+1) → ℕ} (hl : StrictAnti l) (i : Fin (n+1)) :
    Real.log (blockUpper x (l 0)) ≤ Real.log (blockUpper x (l i)) := by
  apply Real.log_le_log (by linarith [blockUpper_gt_one hx (l 0)])
  exact blockUpper_antitone hx.le (hl.antitone (Fin.zero_le i))

theorem reciprocal_square_width_le_one {j : ℝ} (hj : 1 ≤ j) :
    1/j^2 ≤ 1 := by
  have hj0 : 0 < j := by linarith
  rw [div_le_one (sq_pos_of_pos hj0)]
  nlinarith

theorem reciprocal_square_width_lower {X j : ℝ} (hX : 0 < X) (hj : 1 ≤ j)
    (hlog : 600*j ≤ Real.log X) : X^(-(1/300 : ℝ)) ≤ 1/j^2 := by
  have hj0 : 0 < j := by linarith
  have hjlog : Real.log j ≤ j := (Real.log_le_sub_one_of_pos hj0).trans (by linarith)
  have hp : j^2 ≤ X^(1/300 : ℝ) := by
    calc
      _ = Real.exp (2*Real.log j) := by
        rw [show 2*Real.log j = Real.log j+Real.log j by ring, Real.exp_add, Real.exp_log hj0]
        ring
      _ ≤ Real.exp (Real.log X*(1/300)) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := (Real.rpow_def_of_pos hX _).symm
  simpa only [Real.rpow_neg hX.le, one_div] using
    one_div_le_one_div_of_le (sq_pos_of_pos hj0) hp

theorem reversed_block_width_lower {x : ℝ} (hx : 1 < x) {n : ℕ}
    {l : Fin (n+1) → ℕ} (hl : StrictAnti l)
    (hfirst : 600 ≤ Real.log (blockUpper x (l 0))) (i : Fin (n+1)) :
    (blockUpper x (l i))^(-(1/300 : ℝ)) ≤ 1/((i.val : ℝ)+1)^2 := by
  apply reciprocal_square_width_lower (by linarith [blockUpper_gt_one hx (l i)])
    (by exact le_add_of_nonneg_left (Nat.cast_nonneg _) : 1 ≤ (i.val : ℝ)+1)
  have he : (i.val : ℝ)+1 ≤ Real.exp (i.val : ℝ) := Real.add_one_le_exp _
  have h := mul_le_mul he hfirst (by norm_num : (0 : ℝ) ≤ 600) (Real.exp_nonneg _)
  have hg := reversed_block_log_growth hx hl i
  nlinarith

end NField.Alignment.HarperPrimeBlockGrowth

/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.DivisorBudget
/-! # A uniform logarithmic divisor bound

The exponent in the existing integer-power divisor estimate is chosen
from the integer itself. Its explicit constant is bounded before that
choice, so no fixed-exponent constant is used uniformly in a growing one.
-/

noncomputable section

namespace NField.ResetForests.ReturnWindows

open NField.Alignment.DivisorSmallPowerBound

theorem log_divisor_constant_le {m : ℕ} (hm : 0 < m) :
    Real.log (divisorConstant m : ℝ) ≤ 2*(8 : ℝ)^m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hfR : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have hfact : Real.log (m.factorial : ℝ) ≤ (m : ℝ)^2 := by
    calc
      _ ≤ Real.log ((m : ℝ)^m) := Real.log_le_log hfR (by exact_mod_cast Nat.factorial_le_pow m)
      _ = (m : ℝ)*Real.log (m : ℝ) := Real.log_pow _ _
      _ ≤ (m : ℝ)*(m : ℝ) := mul_le_mul_of_nonneg_left
        (by linarith [Real.log_le_sub_one_of_pos hmR]) hmR.le
      _ = _ := by ring
  have hm2 : (m : ℝ) ≤ (2 : ℝ)^m := by exact_mod_cast (show m < 2^m from Nat.lt_two_pow_self).le
  have htwo : (1 : ℝ) ≤ (2 : ℝ)^m := one_le_pow₀ (by norm_num)
  have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hc : Real.log (localConstant m : ℝ) ≤ (m : ℝ)^2+m := by
    unfold localConstant
    rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul hfR.ne' (by positivity), Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith [mul_le_mul_of_nonneg_left hlog2 hmR.le]
  calc
    _ = (2 : ℝ)^m*Real.log (localConstant m : ℝ) := by
      rw [divisorConstant, Nat.cast_pow, Real.log_pow, Nat.cast_pow]
      norm_num only [Nat.cast_ofNat]
    _ ≤ (2 : ℝ)^m*((m : ℝ)^2+m) := mul_le_mul_of_nonneg_left hc (by positivity)
    _ ≤ (2 : ℝ)^m*(2*((2 : ℝ)^m)^2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [sq_nonneg ((2 : ℝ)^m-m)]
    _ = 2*(((2 : ℝ)^m)^3) := by ring
    _ = 2*(((2 : ℝ)^3)^m) := by
      congr 1
      rw [← pow_mul, ← pow_mul, Nat.mul_comm m 3]
    _ = _ := by norm_num

theorem triple_divisor_log_parameter {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (m : ℝ)*Real.log (Core.tripleDivisorCount n : ℝ) ≤
      2*(2*(8 : ℝ)^m+Real.log (n : ℝ)) := by
  have hd : (0 : ℝ) < n.divisors.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hn.ne'⟩
  have ht : (Core.tripleDivisorCount n : ℝ) ≤ (n.divisors.card : ℝ)^2 := by
    exact_mod_cast Core.triple_divisor_le_square n
  have ht0 : 0 < Core.tripleDivisorCount n := by
    unfold Core.tripleDivisorCount
    apply Finset.sum_pos'
    · intro d _; omega
    · refine ⟨1, Nat.one_mem_divisors.mpr hn.ne', ?_⟩
      norm_num
  have hb : (n.divisors.card : ℝ)^m ≤ (divisorConstant m : ℝ)*(n : ℝ) := by
    exact_mod_cast divisor_count_pow_le m n hn.ne'
  have hl := Real.log_le_log (pow_pos hd m) hb
  rw [Real.log_pow, Real.log_mul (by exact_mod_cast (divisorConstant_pos m).ne')
    (by exact_mod_cast hn.ne')] at hl
  have htl : Real.log (Core.tripleDivisorCount n : ℝ) ≤ 2*Real.log (n.divisors.card : ℝ) := by
    simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log (by exact_mod_cast ht0) ht
  have hc := log_divisor_constant_le hm
  nlinarith [mul_le_mul_of_nonneg_left htl (show (0 : ℝ) ≤ m by positivity)]

theorem triple_divisor_log_bound {n : ℕ} (hn : 0 < n)
    (hX : 4 ≤ Real.log (n : ℝ))
    (hY : 4*Real.log 8 ≤ Real.log (Real.log (n : ℝ))) :
    Real.log (Core.tripleDivisorCount n : ℝ) ≤
      (16*Real.log 8)*Real.log (n : ℝ)/Real.log (Real.log (n : ℝ)) := by
  let X := Real.log (n : ℝ)
  let Y := Real.log X
  let a := Y/(2*Real.log 8)
  let m := ⌊a⌋₊
  have hlog8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have hYpos : 0 < Y := by dsimp [Y, X]; linarith
  have ha2 : 2 ≤ a := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2*Real.log 8)).mpr
    dsimp [Y, X]
    linarith
  have hmpos : 0 < m := by
    have : 1 ≤ m := (Nat.one_le_floor_iff a).mpr (by linarith)
    omega
  have hmle : (m : ℝ) ≤ a := Nat.floor_le (by linarith : 0 ≤ a)
  have hmge : a/2 ≤ (m : ℝ) := by
    have := Nat.lt_floor_add_one a
    change a < (m : ℝ)+1 at this
    linarith
  have hexp : (8 : ℝ)^m ≤ Real.sqrt X := by
    apply (Real.le_sqrt (by positivity) (by linarith : 0 ≤ X)).mpr
    have hlog : Real.log (((8 : ℝ)^m)^2) ≤ Real.log X := by
      rw [Real.log_pow, Real.log_pow]
      change 2*((m : ℝ)*Real.log 8) ≤ Y
      have hma := (le_div_iff₀ (by positivity : (0 : ℝ) < 2*Real.log 8)).mp hmle
      nlinarith
    exact (Real.log_le_log_iff (by positivity) (by linarith : 0 < X)).mp hlog
  have hsqrt : 2*Real.sqrt X ≤ X := by
    have hsq := Real.sq_sqrt (by linarith : 0 ≤ X)
    have hr := Real.sqrt_nonneg X
    nlinarith
  have hb := triple_divisor_log_parameter hmpos hn
  have hmY : Y ≤ (4*Real.log 8)*(m : ℝ) := by
    have : Y/(2*Real.log 8)/2 ≤ (m : ℝ) := hmge
    have hclear := (div_le_iff₀ (by positivity : (0 : ℝ) < 4*Real.log 8)).mp
      (show Y/(4*Real.log 8) ≤ (m : ℝ) by
        convert this using 1
        field_simp
        ring)
    nlinarith
  have hB : (m : ℝ)*Real.log (Core.tripleDivisorCount n : ℝ) ≤ 4*X := by
    change (m : ℝ)*Real.log (Core.tripleDivisorCount n : ℝ) ≤ 2*(2*(8 : ℝ)^m+X) at hb
    linarith
  have htarget : Real.log (Core.tripleDivisorCount n : ℝ) ≤
      (16*Real.log 8)*X/Y := by
    apply (le_div_iff₀ hYpos).mpr
    have hcount : 0 ≤ Real.log (Core.tripleDivisorCount n : ℝ) := by
      apply Real.log_nonneg
      have : 1 ≤ Core.tripleDivisorCount n := by
        unfold Core.tripleDivisorCount
        exact (by norm_num : 1 ≤ (Nat.divisors 1).card).trans
          (Finset.single_le_sum (f := fun d : ℕ => d.divisors.card)
            (fun d _ => Nat.zero_le _) (Nat.one_mem_divisors.mpr hn.ne'))
      exact_mod_cast this
    nlinarith [mul_le_mul_of_nonneg_right hmY hcount,
      mul_le_mul_of_nonneg_left hB (by positivity : 0 ≤ 4*Real.log 8)]
  exact htarget

end NField.ResetForests.ReturnWindows

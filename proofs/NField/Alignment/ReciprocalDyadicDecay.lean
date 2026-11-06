/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ReciprocalOptimizedBlock
import Mathlib.Algebra.Order.Field.GeomSum

/-! # Cubic exponential decay summed at the two-thirds scale -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.ReciprocalDyadicDecay
open scoped BigOperators Classical

theorem inverse_exponential_gap (t : ℝ) (ht : 0 < t) :
    1/(1-Real.exp (-t)) ≤ 1+1/t := by
  have he : Real.exp (-t) ≤ 1/(1+t) := by
    rw [Real.exp_neg, one_div]
    apply inv_anti₀ (by linarith)
    linarith [Real.add_one_le_exp t]
  have hd : t/(1+t) ≤ 1-Real.exp (-t) := by
    calc
      _ = 1-1/(1+t) := by field_simp; ring
      _ ≤ _ := by linarith
  have hh := one_div_le_one_div_of_le (div_pos ht (by linarith)) hd
  apply hh.trans_eq
  field_simp
  ring

theorem geometric_exponential_sum (c T : ℝ) (hc : 0 < c) (hT : 0 < T) (N : ℕ) :
    (∑ j ∈ Finset.range N, Real.exp (-c*(j : ℝ)/T)) ≤ 1+T/c := by
  have hr : Real.exp (-c/T) < 1 := Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by linarith) hT)
  have hh := geom_sum_Ico_le_of_lt_one (m := 0) (n := N) (Real.exp_pos (-c/T)).le hr
  have he (j : ℕ) : Real.exp (-c*(j : ℝ)/T) = Real.exp (-c/T)^j := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simp only [he, pow_zero, ← Finset.range_eq_Ico] at *
  apply hh.trans
  have hb := inverse_exponential_gap (c/T) (div_pos hc hT)
  simpa only [neg_div, one_div_div] using hb

theorem cubic_tail_comparison (L : ℝ) (hL : 0 < L) (T j : ℕ) (hT : 0 < T)
    (hscale : L^2 ≤ (T : ℝ)^3) (hj : T ≤ j) : (j : ℝ)/T ≤ (j : ℝ)^3/L^2 := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hjr : (T : ℝ) ≤ j := by exact_mod_cast hj
  have hj2 : (T : ℝ)^2 ≤ (j : ℝ)^2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hj2 hTr.le
  have hh' : L^2 ≤ (j : ℝ)^2*T := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hh' (Nat.cast_nonneg j : (0 : ℝ) ≤ j)
  apply (div_le_div_iff₀ hTr (sq_pos_of_pos hL)).mpr
  nlinarith

/-- A finite cubic-decay sum is controlled by an integer scale with T^3>=L^2. -/
theorem cubic_exponential_sum (c L : ℝ) (hc : 0 < c) (hL : 0 < L)
    (T : ℕ) (hT : 0 < T) (hscale : L^2 ≤ (T : ℝ)^3) (N : ℕ) :
    (∑ j ∈ Finset.range N, Real.exp (-c*(j : ℝ)^3/L^2)) ≤ T+1+(T : ℝ)/c := by
  have hone (j : ℕ) : Real.exp (-c*(j : ℝ)^3/L^2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by
      apply div_nonpos_of_nonpos_of_nonneg
      · exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
      · positivity)
  have hhead : (∑ j ∈ Finset.range T, Real.exp (-c*(j : ℝ)^3/L^2)) ≤ T := by
    simpa using Finset.sum_le_sum (fun j (_ : j ∈ Finset.range T) => hone j)
  by_cases hN : N ≤ T
  · have hh : (∑ j ∈ Finset.range N, Real.exp (-c*(j : ℝ)^3/L^2)) ≤ N := by
      simpa using Finset.sum_le_sum (fun j (_ : j ∈ Finset.range N) => hone j)
    have hNr : (N : ℝ) ≤ T := by exact_mod_cast hN
    nlinarith [div_pos (show (0 : ℝ) < T by exact_mod_cast hT) hc]
  · rw [show N = T+(N-T) by omega, Finset.sum_range_add]
    have ht : (∑ j ∈ Finset.range (N-T), Real.exp (-c*((T+j : ℕ) : ℝ)^3/L^2)) ≤
        ∑ j ∈ Finset.range (N-T), Real.exp (-c*(j : ℝ)/(T : ℝ)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hh := cubic_tail_comparison L hL T (T+j) hT hscale (by omega)
      have hTr : (0 : ℝ) < T := by exact_mod_cast hT
      have hj' : (j : ℝ)/T ≤ ((T+j : ℕ) : ℝ)/T := by gcongr; exact_mod_cast (by omega : j ≤ T+j)
      apply Real.exp_le_exp.mpr
      have hm := mul_le_mul_of_nonneg_left (hj'.trans hh) hc.le
      calc
        _ = -(c*(((T+j : ℕ) : ℝ)^3/L^2)) := by ring
        _ ≤ -(c*((j : ℝ)/(T : ℝ))) := neg_le_neg hm
        _ = _ := by ring
    have hg := geometric_exponential_sum c T hc (by exact_mod_cast hT) (N-T)
    linarith

/-- Summing cubic exponential decay retains the exact two-thirds scale. -/
theorem cubic_sum_two_thirds (c L : ℝ) (hc : 0 < c) (hL : 0 < L) (N : ℕ) :
    (∑ j ∈ Finset.range N, Real.exp (-c*(j : ℝ)^3/L^2)) ≤
      (2+1/c)*(Real.rpow L (2/3 : ℝ)+1) := by
  let R := Real.rpow L (2/3 : ℝ)
  let T : ℕ := ⌈R⌉₊
  have hR : 0 < R := Real.rpow_pos_of_pos hL _
  have hRT : R ≤ (T : ℝ) := Nat.le_ceil R
  have hT : 0 < T := by
    by_contra hh
    have ht0 : T = 0 := by omega
    rw [ht0, Nat.cast_zero] at hRT
    linarith
  have hpow : R^3 = L^2 := by
    dsimp [R]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
    norm_num
  have hcube := pow_le_pow_left₀ hR.le hRT 3
  have hscale : L^2 ≤ (T : ℝ)^3 := by linarith
  have hb := cubic_exponential_sum c L hc hL T hT hscale N
  have hceil : (T : ℝ) ≤ R+1 := (Nat.ceil_lt_add_one hR.le).le
  have hinv : 0 ≤ c⁻¹ := by positivity
  have hm := mul_le_mul_of_nonneg_right hceil hinv
  apply hb.trans
  dsimp only [R] at *
  simp only [div_eq_mul_inv] at *
  nlinarith

/-- The actual exponents of dyadic blocks have a uniform two-thirds sum. -/
theorem dyadic_decay_sum (γ L : ℝ) (hγ : 0 < γ) (hL : 0 < L) (N : ℕ) :
    (∑ j ∈ Finset.range N,
      Real.exp (-γ*(Real.log (4*(2 : ℝ)^j))^3/(16*L^2))) ≤
      (2+1/(γ*(Real.log 2)^3/16))*(Real.rpow L (2/3 : ℝ)+1) := by
  let c := γ*(Real.log 2)^3/16
  have hc : 0 < c := by dsimp [c]; positivity
  apply (show (∑ j ∈ Finset.range N,
      Real.exp (-γ*(Real.log (4*(2 : ℝ)^j))^3/(16*L^2))) ≤
      ∑ j ∈ Finset.range N, Real.exp (-c*(j : ℝ)^3/L^2) from ?_).trans
    (cubic_sum_two_thirds c L hc hL N)
  apply Finset.sum_le_sum
  intro j hj
  have hl : (j : ℝ)*Real.log 2 ≤ Real.log (4*(2 : ℝ)^j) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ (j : ℝ)*Real.log 2) hl 3
  have hm := mul_le_mul_of_nonneg_left hp hγ.le
  apply Real.exp_le_exp.mpr
  dsimp [c]
  apply (div_le_div_iff₀ (by positivity : 0 < 16*L^2) (sq_pos_of_pos hL)).mpr
  nlinarith

end NField.Alignment.ReciprocalDyadicDecay

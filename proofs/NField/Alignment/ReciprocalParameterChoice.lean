/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ReciprocalPolynomialCoefficients
import Mathlib.Algebra.Order.Floor.Ring

/-! # Concrete integer parameters for the real reciprocal phase estimate -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.ReciprocalParameterChoice

def shiftLength (L : ℝ) : ℕ := ⌊Real.exp (31*L/64)⌋₊
def degreeScale (ρ : ℝ) : ℕ := ⌈ρ⌉₊
def degree (m : ℕ) : ℕ := 64*m
def momentOrder (m : ℕ) : ℕ := 24*(degree m)^2

theorem degreeScale_bounds (ρ : ℝ) (hρ : 3/2 ≤ ρ) :
    1 ≤ degreeScale ρ ∧ ρ ≤ degreeScale ρ ∧ (degreeScale ρ:ℝ) ≤ ρ+1 := by
  have h0 : 0 ≤ ρ := by linarith
  have h := Nat.le_ceil ρ
  have h' := Nat.ceil_lt_add_one h0
  refine ⟨?_,h,h'.le⟩
  have hpos : (0:ℝ) < ⌈ρ⌉₊ := by linarith
  exact Nat.succ_le_of_lt (by exact_mod_cast hpos)

theorem shiftLength_bounds (L : ℝ) (hL : 4096 ≤ L) :
    1 ≤ shiftLength L ∧
    Real.exp (123*L/256) ≤ (shiftLength L:ℝ) ∧
    (shiftLength L:ℝ) ≤ Real.exp (31*L/64) := by
  have hL0 : 0 ≤ L := by linarith
  have hlog2 := Real.log_le_self (by norm_num : (0:ℝ) ≤ 2)
  have h2 : (2:ℝ) ≤ Real.exp (L/256) := by
    rw [← Real.exp_log (by norm_num : (0:ℝ) < 2)]
    exact Real.exp_le_exp.mpr (by linarith)
  have hbase : 1 ≤ Real.exp (123*L/256) := Real.one_le_exp (by positivity)
  have he : Real.exp (31*L/64) = Real.exp (123*L/256)*Real.exp (L/256) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hdouble : 2*Real.exp (123*L/256) ≤ Real.exp (31*L/64) := by
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_left h2 (Real.exp_nonneg (123*L/256))]
  have hfloor := Nat.lt_floor_add_one (Real.exp (31*L/64))
  have hlo : Real.exp (123*L/256) ≤ (shiftLength L:ℝ) := by
    dsimp [shiftLength]
    linarith
  refine ⟨?_,hlo,Nat.floor_le (Real.exp_nonneg _)⟩
  exact_mod_cast hbase.trans hlo

theorem shiftLength_log_bounds (L : ℝ) (hL : 4096 ≤ L) :
    123*L/256 ≤ Real.log (shiftLength L:ℝ) ∧
    Real.log (shiftLength L:ℝ) ≤ 31*L/64 := by
  obtain ⟨hH,hlo,hhi⟩ := shiftLength_bounds L hL
  have hH0 : (0:ℝ) < shiftLength L := by exact_mod_cast (show 0 < shiftLength L by omega)
  constructor
  · have h := Real.log_le_log (Real.exp_pos _) hlo
    simpa only [Real.log_exp] using h
  · have h := Real.log_le_log hH0 hhi
    simpa only [Real.log_exp] using h

theorem block_log_bounds (P x L : ℝ) (hP : 0 < P) (hL : 4096 ≤ L)
    (hlogP : Real.log P = L) (hx0 : P ≤ x) (hx1 : x ≤ 3*P) :
    L ≤ Real.log x ∧ Real.log x ≤ L+L/512 ∧ Real.log 3 ≤ L/512 := by
  have hx : 0 < x := hP.trans_le hx0
  have h3 : Real.log 3 ≤ L/512 := by
    have := Real.log_le_self (by norm_num : (0:ℝ) ≤ 3)
    linarith
  refine ⟨?_,?_,h3⟩
  · simpa only [hlogP] using Real.log_le_log hP hx0
  · have h := Real.log_le_log hx hx1
    rw [Real.log_mul (by norm_num : (3:ℝ) ≠ 0) hP.ne',hlogP] at h
    linarith

theorem degree_moment_bounds (m : ℕ) (hm : 1 ≤ m) :
    2 ≤ degree m ∧ 4*m ≤ degree m ∧ (degree m)^2 ≤ momentOrder m ∧
    1 ≤ momentOrder m := by
  dsimp [degree,momentOrder]
  constructor
  · omega
  constructor
  · omega
  constructor <;> nlinarith

end NField.Alignment.ReciprocalParameterChoice

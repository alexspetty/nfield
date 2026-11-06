/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ReciprocalBlockDiscrepancy
import Mathlib.NumberTheory.Harmonic.Bounds

/-! # Rounded exponential Fourier cutoff without logarithmic loss -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.ReciprocalFourierCutoff
open scoped BigOperators Classical

def cutoff (η : ℝ) : ℕ := ⌊Real.exp (2*η)⌋₊

theorem cutoff_bounds (η : ℝ) (hη : 0 ≤ η) :
    Real.exp (2*η)/2 ≤ (cutoff η : ℝ) ∧ (cutoff η : ℝ) ≤ Real.exp (2*η) := by
  have he : 1 ≤ Real.exp (2*η) := Real.one_le_exp_iff.mpr (by linarith)
  have h1 : 1 ≤ cutoff η := (Nat.one_le_floor_iff _).mpr he
  have h1r : (1 : ℝ) ≤ cutoff η := by exact_mod_cast h1
  have hlo := Nat.lt_floor_add_one (Real.exp (2*η))
  exact ⟨by dsimp [cutoff] at *; linarith, Nat.floor_le (Real.exp_pos _).le⟩

theorem cutoff_log (η : ℝ) (hη : 0 ≤ η) : Real.log (cutoff η) ≤ 2*η := by
  have hpos : (0 : ℝ) < cutoff η := (half_pos (Real.exp_pos _)).trans_le (cutoff_bounds η hη).1
  have hh := Real.log_le_log hpos (cutoff_bounds η hη).2
  simpa only [Real.log_exp] using hh

/-- The harmonic frequency cost is absorbed by the exponential saving. -/
theorem harmonic_exponential_cost (η : ℝ) (hη : 0 ≤ η) :
    (∑ h ∈ Finset.Icc 1 (cutoff η), (h : ℝ)⁻¹)*Real.exp (-4*η) ≤ Real.exp (-η) := by
  have hh := harmonic_le_one_add_log (cutoff η)
  have heq : (harmonic (cutoff η) : ℝ) =
      ∑ h ∈ Finset.Icc 1 (cutoff η), (h : ℝ)⁻¹ := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  rw [heq] at hh
  have he := Real.add_one_le_exp (2*η)
  have hb : (∑ h ∈ Finset.Icc 1 (cutoff η), (h : ℝ)⁻¹) ≤ Real.exp (2*η) := by
    linarith [cutoff_log η hη]
  calc
    _ ≤ Real.exp (2*η)*Real.exp (-4*η) := mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
    _ = Real.exp (-2*η) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-η) := Real.exp_le_exp.mpr (by linarith)

/-- The rounded cutoff still supplies exponential smoothing decay. -/
theorem cutoff_smoothing (η : ℝ) (hη : 0 ≤ η) :
    (Real.sqrt (cutoff η : ℝ))⁻¹ ≤ 2*Real.exp (-η) := by
  have hb := (cutoff_bounds η hη).1
  have hH : (0 : ℝ) < cutoff η := (half_pos (Real.exp_pos _)).trans_le hb
  have hs := Real.sqrt_pos.mpr hH
  have he : Real.exp (2*η) = Real.exp η ^ 2 := by
    rw [pow_two, ← Real.exp_add]; congr 1; ring
  have hsq := Real.sq_sqrt hH.le
  have hroot : Real.exp η / 2 ≤ Real.sqrt (cutoff η : ℝ) := by
    nlinarith [Real.exp_pos η]
  have hinv := (one_div_le_one_div_of_le (half_pos (Real.exp_pos η)) hroot)
  have hform : 1/(Real.exp η/2) = 2*Real.exp (-η) := by rw [Real.exp_neg]; ring
  simpa only [one_div, hform] using hinv

/-- A cutoff below16 is covered by a constant multiple of the same decay. -/
theorem small_cutoff_cost (η : ℝ) (_hη : 0 ≤ η) (hH : cutoff η < 16) :
    1 ≤ 4*Real.exp (-η) := by
  have hh : Real.exp (2*η) < 16 := Nat.lt_of_floor_lt hH
  have he : Real.exp (2*η) = Real.exp η ^ 2 := by
    rw [pow_two, ← Real.exp_add]; congr 1; ring
  have h4 : Real.exp η ≤ 4 := by nlinarith [Real.exp_pos η]
  rw [Real.exp_neg]
  exact (le_mul_inv_iff₀ (Real.exp_pos η)).mpr (by simpa using h4)

/-- The source exponent dominates four times the optimized block exponent. -/
theorem frequency_exponential_saving (γ a L b : ℝ) (hγ : 0 ≤ γ) (ha : 0 ≤ a)
    (hL : 0 < L) (hb : 0 < b) (hbL : b ≤ 2*L) :
    Real.exp (-γ*a^3/b^2) ≤ Real.exp (-4*(γ*a^3/(16*L^2))) := by
  have hn : 0 ≤ γ*a^3 := by positivity
  have hh : b^2 ≤ 4*L^2 := by nlinarith
  have hd := div_le_div_of_nonneg_left hn (sq_pos_of_pos hb) hh
  apply Real.exp_le_exp.mpr
  calc
    _ = -(γ*a^3/b^2) := by ring
    _ ≤ -(γ*a^3/(4*L^2)) := neg_le_neg hd
    _ = _ := by ring

/-- The optimized exponent remains below the logarithmic ambient scale. -/
theorem optimized_exponent_upper (γ a L : ℝ) (_hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (ha0 : 0 ≤ a) (haL : a ≤ L) (hL : 0 < L) :
    γ*a^3/(16*L^2) ≤ L/16 := by
  have hp := pow_le_pow_left₀ ha0 haL 3
  have hm := mul_le_mul_of_nonneg_right hγ1 (pow_nonneg ha0 3)
  apply (div_le_iff₀ (by positivity : 0 < 16*L^2)).mpr
  nlinarith

theorem cutoff_le_ambient (η x : ℝ) (hη : 0 ≤ η) (hx : 1 < x)
    (hηx : η ≤ Real.log x/16) : (cutoff η : ℝ) ≤ x := by
  have hl := Real.log_pos hx
  calc
    _ ≤ Real.exp (2*η) := (cutoff_bounds η hη).2
    _ ≤ Real.exp (Real.log x) := Real.exp_le_exp.mpr (by linarith)
    _ = x := Real.exp_log (by linarith)

theorem frequency_log_bound (η x : ℝ) (hη : 0 ≤ η) (hx : 1 < x)
    (hηx : η ≤ Real.log x/16) (h : ℕ) (hh : 1 ≤ h) (hhH : h ≤ cutoff η) :
    Real.log ((h : ℝ)*x) ≤ 2*Real.log x := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  have hhx : (h : ℝ) ≤ x := (by exact_mod_cast hhH : (h : ℝ) ≤ cutoff η).trans
    (cutoff_le_ambient η x hη hx hηx)
  rw [Real.log_mul hh0.ne' (by linarith : x ≠ 0)]
  linarith [Real.log_le_log hh0 hhx]

end NField.Alignment.ReciprocalFourierCutoff

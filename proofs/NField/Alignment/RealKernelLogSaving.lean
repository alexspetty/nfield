/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.RealKernelSaving

/-! # Logarithmic coefficient bands give an explicit real kernel saving -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.RealKernelLogSaving
open RealKernelSaving

theorem saving_le_exp_of_bounds (β t : ℝ) (K : ℕ)
    (hβ : |β| ≤ Real.exp (-t))
    (hK : (K:ℝ)⁻¹ ≤ Real.exp (-t))
    (hprod : (|β| * (K:ℝ)^2)⁻¹ ≤ Real.exp (-t))
    (ht : Real.log 3 ≤ t/2) :
    saving β K ≤ Real.exp (-t/2) := by
  have hthree : (3:ℝ) ≤ Real.exp (t/2) := by
    rw [← Real.exp_log (by norm_num : (0:ℝ)<3)]
    exact Real.exp_le_exp.mpr ht
  calc
    _ ≤ |β|+(K:ℝ)⁻¹+(|β| * (K:ℝ)^2)⁻¹ := min_le_right _ _
    _ ≤ 3*Real.exp (-t) := by linarith
    _ ≤ Real.exp (t/2)*Real.exp (-t) :=
      mul_le_mul_of_nonneg_right hthree (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem saving_le_exp_of_log_bounds (β L d : ℝ) (K : ℕ)
    (hβ : β ≠ 0) (hK : 0 < K) (hL : 0 ≤ L) (hd : 0 ≤ d)
    (hupper : Real.log |β| ≤ -d*L/2)
    (hlength : d*L/4 ≤ Real.log (K:ℝ))
    (hlower : d*L/256 ≤ Real.log |β|+2*Real.log (K:ℝ))
    (hscale : Real.log 3 ≤ d*L/512) :
    saving β K ≤ Real.exp (-d*L/512) := by
  have hK0 : (0:ℝ) < K := by exact_mod_cast hK
  have hβ0 : 0 < |β| := abs_pos.mpr hβ
  have hdL : 0 ≤ d*L := mul_nonneg hd hL
  have hβ' : |β| ≤ Real.exp (-(d*L/256)) := by
    rw [← Real.exp_log hβ0]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hK' : (K:ℝ)⁻¹ ≤ Real.exp (-(d*L/256)) := by
    rw [← Real.exp_log (inv_pos.mpr hK0),Real.log_inv]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hprod : (|β| * (K:ℝ)^2)⁻¹ ≤ Real.exp (-(d*L/256)) := by
    rw [← Real.exp_log (by positivity : 0 < (|β| * (K:ℝ)^2)⁻¹),Real.log_inv,
      Real.log_mul hβ0.ne' (pow_ne_zero 2 hK0.ne'),Real.log_pow]
    apply Real.exp_le_exp.mpr
    norm_num only [Nat.cast_ofNat]
    linarith
  have h := saving_le_exp_of_bounds β (d*L/256) K hβ' hK' hprod (by linarith)
  convert h using 1 <;> congr 1 <;> ring

end NField.Alignment.RealKernelLogSaving

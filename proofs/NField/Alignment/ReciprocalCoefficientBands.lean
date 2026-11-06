/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ReciprocalPolynomialCoefficients
import NField.Alignment.RealKernelLogSaving

/-! # Exact logarithmic bands for the selected reciprocal coefficients -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.ReciprocalCoefficientBands
open ReciprocalPolynomialCoefficients RealKernelSaving RealKernelLogSaving

theorem selected_log_bands (L ρ m d X U V : ℝ)
    (hL : 0 ≤ L) (hρ : 3/2 ≤ ρ) (hm0 : ρ ≤ m) (hm1 : m ≤ ρ+1)
    (hd0 : 2*m ≤ d) (hd1 : d ≤ 4*m)
    (hX0 : L ≤ X) (hX1 : X ≤ L+L/512)
    (hU : 123*L/256 ≤ U) (hV : 0 ≤ V) :
    ρ*L-(d+1)*X ≤ -d*L/2 ∧
    d*L/4 ≤ V+d*U ∧
    d*L/256 ≤ ρ*L-(d+1)*X+2*(V+d*U) := by
  have hd : 1 ≤ d := by linarith
  have hXlo := mul_le_mul_of_nonneg_left hX0 (show 0 ≤ d+1 by linarith)
  have hXhi := mul_le_mul_of_nonneg_left hX1 (show 0 ≤ d+1 by linarith)
  have hUd := mul_le_mul_of_nonneg_left hU (show 0 ≤ d by linarith)
  have hdL : 0 ≤ d*L := mul_nonneg (by linarith) hL
  have hupper := mul_nonneg (show 0 ≤ d/2+1-ρ by linarith) hL
  have hcore := mul_nonneg (show 0 ≤ ρ-1-3*d/64 by linarith) hL
  have hone := mul_nonneg (show 0 ≤ d-1 by linarith) hL
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem coefficient_log (Q x : ℝ) (hQ : 0 < Q) (hx : 0 < x)
    {n : ℕ} (j : Fin n) :
    Real.log |coefficient Q x j| = Real.log Q-((j.val:ℝ)+2)*Real.log x := by
  rw [coefficient_abs Q x hQ.le hx j,
    Real.log_div hQ.ne' (pow_ne_zero _ hx.ne'),Real.log_pow]
  push_cast
  rfl

theorem radius_log (s H d : ℕ) (hs : 1 ≤ s) (hH : 1 ≤ H) :
    Real.log ((s*H^d:ℕ):ℝ) = Real.log (s:ℝ)+(d:ℝ)*Real.log (H:ℝ) := by
  have hs0 : (0:ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hH0 : (0:ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  rw [Nat.cast_mul,Nat.cast_pow,Real.log_mul hs0.ne' (pow_ne_zero _ hH0.ne'),Real.log_pow]

theorem coefficient_selected_saving (Q x L ρ m : ℝ) (hQ : 0 < Q) (hx : 0 < x)
    (hL : 0 ≤ L) (hρ : 3/2 ≤ ρ) (hm0 : ρ ≤ m) (hm1 : m ≤ ρ+1)
    (hQlog : Real.log Q = ρ*L)
    (hX0 : L ≤ Real.log x) (hX1 : Real.log x ≤ L+L/512)
    (hscale : Real.log 3 ≤ L/512)
    (s H : ℕ) (hs : 1 ≤ s) (hH : 1 ≤ H) (hHlog : 123*L/256 ≤ Real.log (H:ℝ))
    {n : ℕ} (j : Fin n) (hd0 : 2*m ≤ (j.val:ℝ)+1) (hd1 : (j.val:ℝ)+1 ≤ 4*m) :
    saving (coefficient Q x j) (s*H^(j.val+1)) ≤
      Real.exp (-((j.val:ℝ)+1)*L/512) := by
  have hsR : (1:ℝ) ≤ s := by exact_mod_cast hs
  obtain ⟨hb,hk,hbk⟩ := selected_log_bands L ρ m ((j.val:ℝ)+1)
    (Real.log x) (Real.log (H:ℝ)) (Real.log (s:ℝ)) hL hρ hm0 hm1 hd0 hd1
    hX0 hX1 hHlog (Real.log_nonneg hsR)
  have hcoeff := coefficient_log Q x hQ hx j
  rw [hQlog] at hcoeff
  have hradius := radius_log s H (j.val+1) hs hH
  simp only [Nat.cast_add,Nat.cast_one] at hradius
  apply saving_le_exp_of_log_bounds _ L ((j.val:ℝ)+1) _
    (coefficient_ne_zero Q x hQ.ne' hx.ne' j)
    (Nat.mul_pos (by omega) (pow_pos (by omega) _)) hL (by positivity)
  · rw [hcoeff]
    convert hb using 1 <;> ring
  · rw [hradius]
    exact hk
  · rw [hcoeff,hradius]
    convert hbk using 1 <;> ring
  · have h := mul_nonneg (Nat.cast_nonneg j.val : (0:ℝ) ≤ j.val) hL
    linarith

end NField.Alignment.ReciprocalCoefficientBands

/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.CollisionRootSumBounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SumIntegralComparisons

/-! # The two convergent frequency sums needed by symmetric smoothing -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.SmoothingSeriesBounds
open scoped BigOperators
open Set MeasureTheory

theorem rpow_tail_bound {H : ℕ} (hH : 1 ≤ H) {s : ℝ} (hs : 1 < s) :
    (∑' n : ℕ, ((n+H+1 : ℕ) : ℝ)^(-s)) ≤ (H : ℝ)^(1-s)/(s-1) := by
  have hH0 : (0 : ℝ)<H := by exact_mod_cast (by omega : 0<H)
  have ha : AntitoneOn (fun x : ℝ => x^(-s)) (Ici (H : ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (hH0.trans_le hx) hxy (by linarith)
  have h := ha.tsum_comp_add_le_integral H
    (integrableOn_Ioi_rpow_of_lt (by linarith : -s < -1) hH0)
    (fun x hx => Real.rpow_nonneg (hH0.trans hx).le _)
  rw [integral_Ioi_rpow_of_lt (by linarith : -s < -1) hH0] at h
  convert h using 1
  rw [show -s+1=1-s by ring]
  simp only [show 1-s= -(s-1) by ring,div_neg,neg_div,neg_neg]

theorem reciprocal_square_tail {H : ℕ} (hH : 1 ≤ H) :
    (∑' n : ℕ, 1/(((n+H+1 : ℕ) : ℝ)^2)) ≤ 1/(H : ℝ) := by
  have h := rpow_tail_bound hH (s := 2) (by norm_num)
  norm_num only [Real.rpow_neg_ofNat,show (1 : ℝ)-2= -1 by norm_num,
    show (2 : ℝ)-1=1 by norm_num,div_one,
    Real.rpow_neg_one,zpow_neg,zpow_ofNat,one_div] at h
  simpa using h

theorem inverse_three_halves (x : ℝ) (hx : 0 < x) :
    1/(x*Real.sqrt x)=x^(-(3/2 : ℝ)) := by
  have hp : x*Real.sqrt x=x^(3/2 : ℝ) := by
    calc
      _ = x^(1 : ℝ)*x^(1/2 : ℝ) := by rw [Real.rpow_one,Real.sqrt_eq_rpow]
      _ = _ := by rw [← Real.rpow_add hx]; congr 1; norm_num
  rw [hp,Real.rpow_neg hx.le,one_div]

theorem reciprocal_three_halves_tail {H : ℕ} (hH : 1 ≤ H) :
    (∑' n : ℕ, 1/(((n+H+1 : ℕ) : ℝ)*Real.sqrt ((n+H+1 : ℕ) : ℝ))) ≤
      2/Real.sqrt (H : ℝ) := by
  have hH0 : (0 : ℝ)<H := by exact_mod_cast (by omega : 0<H)
  have heq (n : ℕ) := inverse_three_halves ((n+H+1 : ℕ) : ℝ) (by positivity)
  simp_rw [heq]
  have h := rpow_tail_bound hH (s := 3/2) (by norm_num)
  have he : (H : ℝ)^(1-(3/2 : ℝ))/(3/2-1)=2/Real.sqrt (H : ℝ) := by
    rw [show (1 : ℝ)-3/2= -(1/2) by ring,Real.rpow_neg hH0.le,← Real.sqrt_eq_rpow]
    norm_num
    ring
  rwa [he] at h

end NField.Alignment.SmoothingSeriesBounds

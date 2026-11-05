/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperPrimeBlockLaw
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Quantitative cutoff scales for the proposed interval comparison

For a block with upper endpoint X and lower endpoint Y=X^(1/e), choose
T=X^(1/30) and delta=2*pi/T. The characteristic-function range contains
[-T,T], its proposed integrated error is O(X^(-1/30)), and sqrt(delta)
is exactly sqrt(2*pi)*X^(-1/60). These are scale estimates only: the
convolution sandwich and interval-probability comparison remain to prove.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperGaussianSmoothingScales
open scoped Topology
open Filter HarperPrimeBlocks HarperPrimeBlockLaw HarperPrimeRangeCharacteristic
  HarperWeightedCharacteristic

def frequencyCutoff (X : ℝ) : ℝ := X^(1/30 : ℝ)
def smoothingWidth (X : ℝ) : ℝ := 2*Real.pi/frequencyCutoff X

theorem frequencyCutoff_pos {X : ℝ} (hX : 0 < X) : 0 < frequencyCutoff X :=
  Real.rpow_pos_of_pos hX _

theorem frequencyCutoff_ge_one {X : ℝ} (hX : 1 ≤ X) : 1 ≤ frequencyCutoff X := by
  exact Real.one_le_rpow hX (by norm_num)

theorem frequencyCutoff_le_sqrt_lower {X : ℝ} (hX : 1 ≤ X) :
    frequencyCutoff X ≤ Real.sqrt (X^(1/Real.exp 1)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by linarith : 0 ≤ X)]
  apply Real.rpow_le_rpow_of_exponent_le hX
  have he := Real.exp_pos 1
  have hb := Real.exp_one_lt_three
  have hi : (1/6 : ℝ) ≤ 1/Real.exp 1/2 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ)<2), le_div_iff₀ he]
    linarith
  linarith

theorem fourth_cutoff_error_bound {X : ℝ} (hX : 1 ≤ X) :
    (frequencyCutoff X)^4/Real.sqrt (X^(1/Real.exp 1)) ≤ X^(-(1/30 : ℝ)) := by
  have hX0 : 0 < X := by linarith
  rw [frequencyCutoff, ← Real.rpow_mul_natCast hX0.le, Real.sqrt_eq_rpow,
    ← Real.rpow_mul hX0.le, ← Real.rpow_sub hX0]
  apply Real.rpow_le_rpow_of_exponent_le hX
  have he := Real.exp_pos 1
  have hb := Real.exp_one_lt_three
  have hi : (1/6 : ℝ) ≤ 1/Real.exp 1/2 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ)<2), le_div_iff₀ he]
    linarith
  norm_num at hi ⊢
  linarith

theorem integrated_cutoff_scale {X : ℝ} (hX : 1 ≤ X) :
    ((frequencyCutoff X)^2+(frequencyCutoff X)^4)/Real.sqrt (X^(1/Real.exp 1)) ≤
      2*X^(-(1/30 : ℝ)) := by
  have hT := frequencyCutoff_ge_one hX
  have hpow : (frequencyCutoff X)^2 ≤ (frequencyCutoff X)^4 := by nlinarith [sq_nonneg ((frequencyCutoff X)^2-1)]
  calc
    _ ≤ (2*(frequencyCutoff X)^4)/Real.sqrt (X^(1/Real.exp 1)) :=
      div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
    _ = 2*((frequencyCutoff X)^4/Real.sqrt (X^(1/Real.exp 1))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (fourth_cutoff_error_bound hX) (by norm_num)

theorem frequencyCutoff_inverse_sqrt {X : ℝ} (hX : 0 ≤ X) :
    (frequencyCutoff X)^(-(1/2 : ℝ)) = X^(-(1/60 : ℝ)) := by
  rw [frequencyCutoff, ← Real.rpow_mul hX]
  norm_num

theorem smoothingWidth_sqrt {X : ℝ} (hX : 0 ≤ X) :
    Real.sqrt (smoothingWidth X) = Real.sqrt (2*Real.pi)*X^(-(1/60 : ℝ)) := by
  rw [smoothingWidth, Real.sqrt_div (by positivity), div_eq_mul_inv]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg
    (show 0 ≤ frequencyCutoff X from Real.rpow_nonneg hX _)]
  exact frequencyCutoff_inverse_sqrt hX

theorem eventual_cutoff_conditions :
    ∀ᶠ X : ℝ in atTop, 2 ≤ X^(1/Real.exp 1) ∧ 1 ≤ frequencyCutoff X ∧
      0 < smoothingWidth X ∧ smoothingWidth X ≤ 1 ∧
      frequencyCutoff X ≤ Real.sqrt (X^(1/Real.exp 1)) := by
  have hY := tendsto_rpow_atTop (by positivity : 0 < 1/Real.exp 1)
  have hT := tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/30)
  filter_upwards [hY.eventually_ge_atTop 2, hT.eventually_ge_atTop (2*Real.pi),
    eventually_ge_atTop (1 : ℝ)] with X hY hT hX
  have hpos := frequencyCutoff_pos (show 0 < X by linarith)
  refine ⟨hY, frequencyCutoff_ge_one hX, div_pos (by positivity) hpos, ?_,
    frequencyCutoff_le_sqrt_lower hX⟩
  exact (div_le_one hpos).mpr hT

theorem blockCharacteristic_frequency_error {x : ℝ} (hx : 1 < x) (l : ℕ)
    (hY : 2 ≤ blockLower x l) (t : ℝ) {u : ℝ}
    (hu : |u| ≤ frequencyCutoff (blockUpper x l)) :
    ‖blockCharacteristic x l t u-rangeGaussian (primeBlock x l) (fun _ => t) u‖ ≤
      4*comparisonConstant*(|u|+|u|^3)*(blockUpper x l)^(-(1/(2*Real.exp 1))) := by
  have hu' : |u| ≤ Real.sqrt (blockLower x l) := by
    rw [blockLower_power (by linarith : 0 ≤ x)]
    exact hu.trans (frequencyCutoff_le_sqrt_lower (blockUpper_gt_one hx l).le)
  have h := blockCharacteristic_gaussian_error hx.le l hY t hu'
  rw [blockLower_power (by linarith : 0 ≤ x),
    ← Real.rpow_mul (by linarith [blockUpper_gt_one hx l] : 0 ≤ blockUpper x l)] at h
  convert h using 1
  congr 2
  ring

end NField.Alignment.HarperGaussianSmoothingScales

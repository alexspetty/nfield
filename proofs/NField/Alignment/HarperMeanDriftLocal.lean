/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperPrimeBlockPath
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Local leading-mean drift for source prime blocks

The comparison Gaussian mean differs from one by a Mertens remainder
and a quadratic frequency correction. These are the leading prime-sum
parameters, not assertions about exact weighted logarithmic expectations.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperMeanDriftLocal
open scoped BigOperators Topology
open Filter Set HarperPrimeBlocks HarperPrimeRangeCharacteristic HarperPrimeBlockVariance

def meanMertensConstant : ℝ :=
  (|Real.log 4+6+Mertens.E₁|+1)*(1+Real.exp 1)

theorem meanMertensConstant_pos : 0 < meanMertensConstant := by
  unfold meanMertensConstant
  positivity

theorem rangeMean_frequency_error {X : ℝ} (S : Finset ℕ)
    (hS : ∀ q ∈ S, q.Prime ∧ (q : ℝ) ≤ X) (t : ℝ) :
    |rangeMean S (fun _ => t)-2*rangeVariance S| ≤ rangeVariance S*(t*Real.log X)^2 := by
  have he : 2*rangeVariance S = ∑ q ∈ S, (1 : ℝ)/q := by
    unfold rangeVariance
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    simp only [one_div]
    ring
  rw [he,rangeMean,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ q ∈ S, |Real.cos (t*Real.log q)/q-1/q| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ S, (t*Real.log X)^2*((q : ℝ)⁻¹/2) := by
      apply Finset.sum_le_sum
      intro q hq
      obtain ⟨hp,hqX⟩ := hS q hq
      have hq0 : (0 : ℝ) < q := by exact_mod_cast hp.pos
      have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hp.one_lt.le
      have hl0 := Real.log_nonneg hq1
      have hl := Real.log_le_log hq0 hqX
      have hlsq : (t*Real.log q)^2 ≤ (t*Real.log X)^2 := by
        simp only [mul_pow]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl0 hl 2) (sq_nonneg t)
      have hc : |Real.cos (t*Real.log q)-1| ≤ (t*Real.log q)^2/2 := by
        rw [abs_of_nonpos (sub_nonpos.mpr (Real.cos_le_one _))]
        linarith [Real.one_sub_sq_div_two_le_cos (x := t*Real.log q)]
      calc
        _ = |Real.cos (t*Real.log q)-1|/q := by
          rw [← sub_div,abs_div,abs_of_pos hq0]
        _ ≤ ((t*Real.log X)^2/2)/q :=
          div_le_div_of_nonneg_right (hc.trans (by linarith)) hq0.le
        _ = _ := by ring
    _ = rangeVariance S*(t*Real.log X)^2 := by
      rw [← Finset.mul_sum]
      unfold rangeVariance
      ring

theorem blockVariance_mean_error {X : ℝ} (hX : 2 ≤ X) (hY : 2 ≤ sourceCutoff X) :
    |2*blockVariance X-1| ≤ meanMertensConstant/Real.log X := by
  have hX0 : 0 < X := by linarith
  have hlog : 0 < Real.log X := Real.log_pos (by linarith)
  have hlogY : 0 < Real.log (sourceCutoff X) := Real.log_pos (by linarith)
  have hlogeq : Real.log (sourceCutoff X) = Real.log X/Real.exp 1 := by
    rw [sourceCutoff,Real.log_rpow hX0]
    ring
  let C : ℝ := |Real.log 4+6+Mertens.E₁|+1
  have hC : Real.log 4+6+Mertens.E₁ ≤ C := by
    dsimp [C]
    linarith [le_abs_self (Real.log 4+6+Mertens.E₁)]
  have hx := (Mertens.E₂p.abs_le hX).trans (div_le_div_of_nonneg_right hC hlog.le)
  have hy := (Mertens.E₂p.abs_le hY).trans (div_le_div_of_nonneg_right hC hlogY.le)
  rw [blockVariance_mertens_identity (by linarith)]
  calc
    _ = |Mertens.E₂p X-Mertens.E₂p (sourceCutoff X)| := by congr 1; ring
    _ ≤ |Mertens.E₂p X|+|Mertens.E₂p (sourceCutoff X)| := abs_sub _ _
    _ ≤ C/Real.log X+C/Real.log (sourceCutoff X) := add_le_add hx hy
    _ = meanMertensConstant/Real.log X := by
      rw [hlogeq]
      unfold meanMertensConstant C
      field_simp

theorem source_mean_error {x : ℝ} (hx : 1 < x) (l : ℕ) (t : ℝ)
    (hX : 2 ≤ blockUpper x l) (hY : 2 ≤ sourceCutoff (blockUpper x l))
    (hv : blockVariance (blockUpper x l) ≤ 3/4) :
    |rangeMean (primeBlock x l) (fun _ => t)-1| ≤
      meanMertensConstant/Real.log (blockUpper x l)+(3/4)*(t*Real.log (blockUpper x l))^2 := by
  have hf := rangeMean_frequency_error (primeBlock x l)
    (fun q hq => ⟨(primeBlock_mem.mp hq).1,(primeBlock_mem.mp hq).2.2⟩) t
  rw [source_blockVariance (by linarith : 0 ≤ x)] at hf
  have hm := blockVariance_mean_error hX hY
  calc
    _ ≤ |rangeMean (primeBlock x l) (fun _ => t)-2*blockVariance (blockUpper x l)|+
        |2*blockVariance (blockUpper x l)-1| := abs_sub_le _ _ _
    _ ≤ blockVariance (blockUpper x l)*(t*Real.log (blockUpper x l))^2+
        meanMertensConstant/Real.log (blockUpper x l) := add_le_add hf hm
    _ ≤ _ := by nlinarith [sq_nonneg (t*Real.log (blockUpper x l))]

theorem small_frequency_square {L j t : ℝ} (hL : 0 < L) (hj : 0 < j)
    (ht : |t| ≤ 1/(j^(2/3 : ℝ)*L)) : (t*L)^2 ≤ j^(-(4/3 : ℝ)) := by
  have hp := Real.rpow_pos_of_pos hj (2/3 : ℝ)
  have htl : |t*L| ≤ j^(-(2/3 : ℝ)) := by
    rw [abs_mul,abs_of_pos hL,Real.rpow_neg hj.le]
    have h := (mul_le_mul_of_nonneg_right ht hL.le)
    have he : 1/(j^(2/3 : ℝ)*L)*L = (j^(2/3 : ℝ))⁻¹ := by field_simp
    rwa [he] at h
  have hs := pow_le_pow_left₀ (abs_nonneg _) htl 2
  rw [sq_abs] at hs
  have he : (j^(-(2/3 : ℝ)))^2 = j^(-(4/3 : ℝ)) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hj.le]
    norm_num
  rwa [he] at hs

end NField.Alignment.HarperMeanDriftLocal

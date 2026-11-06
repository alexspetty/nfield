/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.RealLinearKernelEstimate

/-! # Normalized savings in the one-dimensional real frequency kernel -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.RealKernelSaving
open scoped BigOperators
open RealPolynomialFrequency RealLinearKernelEstimate

def saving (β : ℝ) (K : ℕ) : ℝ :=
  min 1 (|β|+(K:ℝ)⁻¹+(|β| *(K:ℝ)^2)⁻¹)

theorem saving_nonneg (β : ℝ) (K : ℕ) : 0 ≤ saving β K := by
  unfold saving
  positivity

theorem saving_le_one (β : ℝ) (K : ℕ) : saving β K ≤ 1 := min_le_left _ _

theorem linearKernel_sq_saving (β : ℝ) (hβ : β ≠ 0) (K : ℕ) (hK : 0 < K) :
    linearKernel β K^2 ≤ 1000*(K:ℝ)^4*saving β K := by
  have hK1 : (1:ℝ) ≤ K := by exact_mod_cast hK
  have hK0 : (0:ℝ) < K := by exact_mod_cast hK
  have h₁ : linearKernel β K^2 ≤ 1000*(K:ℝ)^4 := by
    have h := pow_le_pow_left₀ (linearKernel_nonneg β K) (linearKernel_trivial β K) 2
    have hp := pow_le_pow_left₀ (show 0 ≤ 2*(K:ℝ)+1 by positivity)
      (show 2*(K:ℝ)+1 ≤ 3*K by linarith) 4
    have he : ((2*(K:ℝ)+1)^2)^2 = (2*(K:ℝ)+1)^4 := by ring
    rw [he] at h
    have he' : (3*(K:ℝ))^4 = 81*(K:ℝ)^4 := by ring
    rw [he'] at hp
    nlinarith [pow_nonneg hK0.le 4]
  have h₂ : linearKernel β K^2 ≤
      1000*(K:ℝ)^4*(|β|+(K:ℝ)⁻¹+(|β| *(K:ℝ)^2)⁻¹) := by
    convert linearKernel_sq_estimate β hβ K hK using 1
    field_simp
    <;> ring
  unfold saving
  rcases le_total 1 (|β|+(K:ℝ)⁻¹+(|β| *(K:ℝ)^2)⁻¹) with hh | hh
  · simpa only [min_eq_left hh,mul_one] using h₁
  · simpa only [min_eq_right hh] using h₂

end NField.Alignment.RealKernelSaving

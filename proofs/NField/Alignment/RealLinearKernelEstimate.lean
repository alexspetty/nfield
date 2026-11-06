/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.RealLinearKernelBound

/-! # Explicit size and sign bounds for the real frequency kernel -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.RealLinearKernelEstimate
open scoped BigOperators ComplexConjugate
open RealBilinearMoment RealPolynomialMomentBox RealPolynomialFrequency
  RealLinearKernelBound

theorem linearKernel_neg (β : ℝ) (K : ℕ) : linearKernel (-β) K = linearKernel β K := by
  unfold linearKernel
  apply Finset.sum_congr rfl
  intro v _
  have he : (∑ u ∈ Finset.Icc (-(K:ℤ)) K, realCharacter (-β*(u:ℝ)*(v:ℝ))) =
      conj (∑ u ∈ Finset.Icc (-(K:ℤ)) K, realCharacter (β*(u:ℝ)*(v:ℝ))) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro u _
    rw [character_conj realCharacter realCharacter_norm]
    congr 1
    ring
  rw [he, Complex.norm_conj]

theorem linearKernel_abs (β : ℝ) (K : ℕ) : linearKernel |β| K = linearKernel β K := by
  rcases le_total 0 β with hβ | hβ
  · rw [abs_of_nonneg hβ]
  · rw [abs_of_nonpos hβ, linearKernel_neg]

theorem linearKernel_trivial (β : ℝ) (K : ℕ) :
    linearKernel β K ≤ (2*(K:ℝ)+1)^2 := by
  have hc : ((Finset.Icc (-(K:ℤ)) (K:ℤ)).card:ℝ) = 2*(K:ℝ)+1 := by
    rw [symmetric_Icc_card]
    push_cast
    rfl
  calc
    _ ≤ ∑ _v ∈ Finset.Icc (-(K:ℤ)) K,
        ∑ _u ∈ Finset.Icc (-(K:ℤ)) K, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro v _
      calc
        _ ≤ ∑ u ∈ Finset.Icc (-(K:ℤ)) K, ‖realCharacter (β*(u:ℝ)*(v:ℝ))‖ :=
          norm_sum_le _ _
        _ = _ := by simp only [realCharacter_norm]
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one, hc]; ring

theorem linearKernel_sq_estimate_pos (β : ℝ) (hβ : 0 < β) (K : ℕ) (hK : 0 < K) :
    linearKernel β K^2 ≤
      1000*((K:ℝ)^4*β+(K:ℝ)^3+(K:ℝ)^2/β) := by
  have hK1 : (1:ℝ) ≤ K := by exact_mod_cast hK
  have hK0 : (0:ℝ) ≤ K := Nat.cast_nonneg _
  have hN : 2*(K:ℝ)+1 ≤ 3*K := by linarith
  have hpi : 1+4*Real.pi*K*β ≤ 1+16*K*β := by
    nlinarith [mul_nonneg (show 0 ≤ 4-Real.pi by linarith [Real.pi_lt_four])
      (mul_nonneg hK0 hβ.le)]
  have hb := linearKernel_sq_grid_bound β hβ K hK
  have hprod : (2*(K:ℝ)+1)^2*((2*(K:ℝ)+1)*β+1)*(1+4*Real.pi*K*β) ≤
      (3*(K:ℝ))^2*(3*K*β+1)*(1+16*K*β) := by
    apply mul_le_mul
    · exact mul_le_mul (pow_le_pow_left₀ (by positivity) hN 2)
        (by nlinarith) (by positivity) (by positivity)
    · exact hpi
    · positivity
    · positivity
  have hlast : (3*(K:ℝ))^2*(3*K*β+1)*(1+16*K*β) ≤
      β*(1000*((K:ℝ)^4*β+(K:ℝ)^3+(K:ℝ)^2/β)) := by
    field_simp
    nlinarith [mul_nonneg (pow_nonneg hK0 4) (sq_nonneg β),
      mul_nonneg (pow_nonneg hK0 3) hβ.le, sq_nonneg (K:ℝ)]
  exact (mul_le_mul_iff_right₀ hβ).mp (by
    simpa only [mul_comm β] using hb.trans (hprod.trans hlast))

theorem linearKernel_sq_estimate (β : ℝ) (hβ : β ≠ 0) (K : ℕ) (hK : 0 < K) :
    linearKernel β K^2 ≤
      1000*((K:ℝ)^4*|β|+(K:ℝ)^3+(K:ℝ)^2/|β|) := by
  simpa only [linearKernel_abs] using
    linearKernel_sq_estimate_pos |β| (abs_pos.mpr hβ) K hK

end NField.Alignment.RealLinearKernelEstimate

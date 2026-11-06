/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetDerivativePartition

/-! # A proved second-derivative estimate for finite exponential sums -/

noncomputable section

namespace NField.Alignment.CommonResetSecondDerivative

open scoped BigOperators
open Set CommonResetDerivativeFirst CommonResetDerivativePartition

theorem phase_sum_trivial (f : ℝ → ℝ) (a : ℝ) (N : ℕ) :
    ‖∑ i ∈ Finset.range (N+1), phase (f (a+i))‖ ≤ (N : ℝ)+1 := by
  calc
    _ ≤ ∑ i ∈ Finset.range (N+1), ‖phase (f (a+i))‖ := norm_sum_le _ _
    _ = _ := by simp only [phase_norm, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
      Nat.cast_add, Nat.cast_one]

/-- Title: `Positive bounded curvature gives the actual square-root second-derivative estimate`. -/
theorem second_derivative_bound (f g k : ℝ → ℝ) (a : ℝ) (N : ℕ)
    {lam A : ℝ} (hlam : 0 < lam) (hA : 1 ≤ A)
    (hf : ContinuousOn f (Icc a (a+N)))
    (hfg : ∀ x ∈ Ioo a (a+N), HasDerivAt f (g x) x)
    (hg : ContinuousOn g (Icc a (a+N)))
    (hgk : ∀ x ∈ Ioo a (a+N), HasDerivAt g (k x) x)
    (hk : ∀ x ∈ Ioo a (a+N), lam ≤ k x ∧ k x ≤ A*lam) :
    ‖∑ i ∈ Finset.range (N+1), phase (f (a+i))‖ ≤
      10*(A+1)*(((N : ℝ)+1)*Real.sqrt lam + 1/Real.sqrt lam) := by
  let s := Real.sqrt lam
  have hs : 0 < s := Real.sqrt_pos.mpr hlam
  have hsq : s^2 = lam := Real.sq_sqrt hlam.le
  have hN : (0 : ℝ) ≤ N := by positivity
  have hA0 : 0 ≤ A := by linarith
  by_cases hsmall : s ≤ 1/2
  · have hb := second_derivative_split_bound f g k a N hlam hA hs hsmall hf hfg hg hgk hk
    have he : (A*lam*N+2)*(2*s/lam+1+2/s) =
        4*A*N*s + A*N*s^2 + 8/s+2 := by
      rw [← hsq]
      field_simp
      ring
    rw [he] at hb
    have hs1 : s ≤ 1 := by linarith
    have hs2 : s^2 ≤ s := by nlinarith
    have hterm : A*N*s^2 ≤ A*N*s := mul_le_mul_of_nonneg_left hs2 (mul_nonneg hA0 hN)
    have htwo : (2 : ℝ) ≤ 2/s := (le_div_iff₀ hs).mpr (by linarith)
    have hmid : 4*A*N*s + A*N*s^2 + 8/s+2 ≤ 5*A*N*s+10/s := by
      rw [show (10 : ℝ)/s=8/s+2/s by ring]
      linarith
    have hleft : 5*A*N*s ≤ 10*(A+1)*((N : ℝ)+1)*s := by
      apply mul_le_mul_of_nonneg_right _ hs.le
      nlinarith
    have hright : (10 : ℝ)/s ≤ 10*(A+1)/s := div_le_div_of_nonneg_right (by linarith) hs.le
    calc
      _ ≤ 5*A*N*s+10/s := hb.trans hmid
      _ ≤ 10*(A+1)*((N : ℝ)+1)*s+10*(A+1)/s := add_le_add hleft hright
      _ = _ := by dsimp [s]; ring
  · have ht := phase_sum_trivial f a N
    have hL : (0 : ℝ) ≤ (N : ℝ)+1 := by positivity
    have he : (N : ℝ)+1 ≤ 2*(((N : ℝ)+1)*s) := by nlinarith
    have hbig : 2*(((N : ℝ)+1)*s) ≤ 10*(A+1)*(((N : ℝ)+1)*s+1/s) := by
      have hinv : 0 ≤ 1/s := by positivity
      have hprod : 0 ≤ ((N : ℝ)+1)*s := mul_nonneg hL hs.le
      nlinarith
    exact ht.trans (he.trans hbig)

end NField.Alignment.CommonResetSecondDerivative

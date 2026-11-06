/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StationaryReciprocalFloorIntegral
import NField.Alignment.StationaryReciprocalKernels

/-! # An explicit uniform bound for the exact tail remainder functional -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.StationaryTailFunctionalBound
open scoped BigOperators
open MeasureTheory Set StationaryTailFunctional StationaryReciprocalFloorIntegral
  StationaryReciprocalKernels StationaryBernoulliPrimitive StationaryDiagonalDefinitions

theorem inverseSquare_finite_integral {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, 1 / t ^ 2) = 1 / a - 1 / b := by
  have hb : 0 < b := ha.trans_le hab
  have hh := intervalIntegral.integral_Ioi_sub_Ioi (inverseSquare_integrable ha) hab
  rw [inverseSquare_integral ha, inverseSquare_integral hb] at hh
  exact hh.symm

theorem reciprocal_remainder_integral_bound {F : ℝ → ℝ} {a b B : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hB : 0 ≤ B)
    (hi : IntervalIntegrable (fun t => F t / t ^ 2) volume a b)
    (hF : ∀ t ∈ Icc a b, |F t| ≤ B) :
    |∫ t in a..b, F t / t ^ 2| ≤ B / a := by
  have hb : 0 < b := ha.trans_le hab
  have hc : ContinuousOn (fun t : ℝ => B / t ^ 2) (uIcc a b) :=
    continuousOn_const.div (continuousOn_id.pow 2) (fun t ht =>
      pow_ne_zero 2 (StationarySawtoothIntegrals.positive_interval_ne_zero ha hab ht))
  calc
    _ ≤ ∫ t in a..b, |F t / t ^ 2| := intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ t in a..b, B / t ^ 2 := by
      apply intervalIntegral.integral_mono_on hab hi.abs hc.intervalIntegrable
      intro t ht
      rw [abs_div, abs_of_nonneg (sq_nonneg t)]
      exact div_le_div_of_nonneg_right (hF t ht) (sq_nonneg t)
    _ = B * (1 / a - 1 / b) := by
      have he (t : ℝ) : B / t ^ 2 = B * (1 / t ^ 2) := by ring
      simp_rw [he]
      rw [intervalIntegral.integral_const_mul, inverseSquare_finite_integral ha hab]
    _ = B / a - B / b := by ring
    _ ≤ B / a := sub_le_self _ (div_nonneg hB hb.le)

theorem tailFunctional_sub {F G : ℝ → ℝ} {M n : ℕ}
    (hiF : IntervalIntegrable (fun t => F t / t ^ 2) volume (M : ℝ) n)
    (hiG : IntervalIntegrable (fun t => G t / t ^ 2) volume (M : ℝ) n) :
    tailFunctional (fun t => F t - G t) M n = tailFunctional F M n - tailFunctional G M n := by
  unfold tailFunctional
  simp_rw [sub_div]
  rw [intervalIntegral.integral_sub hiF hiG, Finset.sum_sub_distrib]
  ring

/-- Title: `The exact tail functional is bounded uniformly by its cumulative remainder`. -/
theorem tailFunctional_uniform_bound {F : ℝ → ℝ} {M n : ℕ} {B : ℝ}
    (hM : 0 < M) (hMn : M ≤ n) (hB : 0 ≤ B)
    (hi : IntervalIntegrable (fun t => F t / t ^ 2) volume (M : ℝ) n)
    (hF : ∀ t ∈ Icc (M : ℝ) n, |F t| ≤ B) :
    |tailFunctional F M n| ≤ 3 * n * B / M := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hMnR : (M : ℝ) ≤ n := by exact_mod_cast hMn
  have hnR : (0 : ℝ) ≤ n := by positivity
  have hbM := hF M ⟨le_rfl, hMnR⟩
  have hbn := hF n ⟨hMnR, le_rfl⟩
  have hb1 : |F n / 2| ≤ B / 2 := by
    simpa only [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using
      div_le_div_of_nonneg_right hbn (by norm_num : (0 : ℝ) ≤ 2)
  have hb2 : |psi ((n : ℝ) / M) * F M| ≤ B / 2 := by
    rw [abs_mul]
    calc
      _ ≤ (1 / 2 : ℝ) * B := mul_le_mul (psi_abs_bound _) hbM (abs_nonneg _) (by norm_num)
      _ = _ := by ring
  have hb3 : |(n : ℝ) * (∫ t in (M : ℝ)..n, F t / t ^ 2)| ≤ n * B / M := by
    rw [abs_mul, abs_of_nonneg hnR]
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left
      (reciprocal_remainder_integral_bound hMR hMnR hB hi hF) hnR
  have hq : ((n / M : ℕ) : ℝ) ≤ (n : ℝ) / M := by
    rw [← Nat.floor_div_eq_div (K := ℝ)]
    exact Nat.floor_le (by positivity)
  have hb4 : |∑ j ∈ Finset.Icc 1 (n / M), F ((n : ℝ) / j)| ≤ n * B / M := by
    calc
      _ ≤ ∑ j ∈ Finset.Icc 1 (n / M), |F ((n : ℝ) / j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.Icc 1 (n / M), B := Finset.sum_le_sum (fun j hj => hF _ (reciprocal_threshold hM hj))
      _ = ((n / M : ℕ) : ℝ) * B := by simp
      _ ≤ ((n : ℝ) / M) * B := mul_le_mul_of_nonneg_right hq hB
      _ = _ := by ring
  have hbN : B ≤ (n : ℝ) * B / M := by
    apply (le_div_iff₀ hMR).mpr
    nlinarith
  unfold tailFunctional
  calc
    _ ≤ |F n / 2 - psi ((n : ℝ) / M) * F M +
        (n : ℝ) * (∫ t in (M : ℝ)..n, F t / t ^ 2)| +
          |∑ j ∈ Finset.Icc 1 (n / M), F ((n : ℝ) / j)| := abs_sub _ _
    _ ≤ (|F n / 2 - psi ((n : ℝ) / M) * F M| +
        |(n : ℝ) * (∫ t in (M : ℝ)..n, F t / t ^ 2)|) +
          |∑ j ∈ Finset.Icc 1 (n / M), F ((n : ℝ) / j)| := by gcongr; exact abs_add_le _ _
    _ ≤ ((|F n / 2| + |psi ((n : ℝ) / M) * F M|) +
        |(n : ℝ) * (∫ t in (M : ℝ)..n, F t / t ^ 2)|) +
          |∑ j ∈ Finset.Icc 1 (n / M), F ((n : ℝ) / j)| := by gcongr; exact abs_sub _ _
    _ ≤ (B / 2 + B / 2) + n * B / M + n * B / M := by gcongr
    _ = B + 2 * ((n : ℝ) * B / M) := by ring
    _ ≤ 3 * ((n : ℝ) * B / M) := by linarith
    _ = _ := by ring

end NField.Alignment.StationaryTailFunctionalBound

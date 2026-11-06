/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StationaryExactDiagonal
import NField.Alignment.CollisionMultipleTailDisplay

/-! # The exact diagonal-cutoff difference and its omitted mass -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.StationaryDiagonalTailMass
open scoped BigOperators
open Finset StationaryDiagonalDefinitions CollisionRemainderDynamics
  CollisionMultipleTailDisplay StationaryExactDiagonal

theorem finite_age_psi (M n : ℕ) :
    finiteAge collisionWeight M n = (2 / 3 : ℝ) *
      ∑ k ∈ Icc 1 M, coefficient k * psi ((n : ℝ) / k) + weightPrefix M / 3 := by
  rw [age_as_sum_from_one]
  have he : (∑ k ∈ Icc 1 M, collisionWeight k * centeredRemainder k n) =
      (∑ k ∈ Icc 1 M, coefficient k * psi ((n : ℝ) / k)) + weightPrefix M / 2 := by
    unfold weightPrefix
    rw [sum_div, ← sum_add_distrib]
    apply sum_congr rfl
    intro k hk
    rw [centered_remainder_psi n (mem_Icc.mp hk).1]
    unfold coefficient
    ring
  rw [he]
  ring

theorem sum_from_one_difference (f : ℕ → ℝ) {M n : ℕ} (hMn : M ≤ n) :
    (∑ k ∈ Icc 1 n, f k) - (∑ k ∈ Icc 1 M, f k) = ∑ k ∈ Ioc M n, f k := by
  have he (N : ℕ) : Icc 1 N = Ioc 0 N := by ext k; simp only [mem_Icc, mem_Ioc]; omega
  rw [he, he]
  have hh := sum_Ioc_consecutive f (Nat.zero_le M) hMn
  linarith

/-- Title: `The moving diagonal differs from a finite stationary cutoff by its exact sawtooth tail`. -/
theorem diagonal_cutoff_tail {M n : ℕ} (hMn : M ≤ n) :
    diagonal n - finiteAge collisionWeight M n =
      (2 / 3 : ℝ) * (∑ k ∈ Ioc M n, coefficient k * psi ((n : ℝ) / k)) +
        (weightPrefix n - weightPrefix M) / 3 := by
  rw [diagonal_psi, finite_age_psi]
  have he := sum_from_one_difference (fun k => coefficient k * psi ((n : ℝ) / k)) hMn
  linarith

theorem weightPrefix_tail_nonneg {M n : ℕ} (hMn : M ≤ n) :
    0 ≤ weightPrefix n - weightPrefix M := by
  unfold weightPrefix
  rw [sum_from_one_difference collisionWeight hMn]
  exact sum_nonneg (fun k hk => collisionWeight_nonneg k)

/-- Title: `The omitted collision mass has a uniform logarithmic inverse-linear bound`. -/
theorem weightPrefix_tail_bound {M n : ℕ} (hM : 1 ≤ M) (hMn : M ≤ n) :
    weightPrefix n - weightPrefix M ≤ 6 * Real.log (2 * (M : ℝ)) / M := by
  unfold weightPrefix
  rw [sum_from_one_difference collisionWeight hMn]
  calc
    _ = ∑ k ∈ Ioc M n, if M < k ∧ 1 ∣ k then collisionWeight k else 0 := by
      apply sum_congr rfl
      intro k hk
      simp [(mem_Ioc.mp hk).1]
    _ ≤ omittedMass 1 M := (omittedMass_summable 1 M).sum_le_tsum _ (fun k hk => by
      split_ifs <;> simp [collisionWeight_nonneg])
    _ ≤ _ := by simpa using omittedMass_log_bound (by norm_num : 0 < (1 : ℕ)) hM

end NField.Alignment.StationaryDiagonalTailMass

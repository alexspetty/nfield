/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StationaryReciprocalAbel

/-! # One exact functional for both discrete and smooth reciprocal tails -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.StationaryTailFunctional
open scoped BigOperators
open Finset StationaryFloorInterchange StationaryReciprocalAbel StationaryDiagonalDefinitions

def tailFunctional (F : ℝ → ℝ) (M n : ℕ) : ℝ :=
  F n / 2 - psi ((n : ℝ) / M) * F M +
    (n : ℝ) * (∫ t in (M : ℝ)..n, F t / t ^ 2) -
      ∑ j ∈ Icc 1 (n / M), F ((n : ℝ) / j)

/-- Title: `The discrete sawtooth tail equals its exact cumulative-weight functional`. -/
theorem weighted_psi_tail_functional (a : ℕ → ℝ) {M n : ℕ} (hM : 0 < M) (hMn : M ≤ n) :
    (∑ k ∈ Ioc M n, a k * psi ((n : ℝ) / k)) = tailFunctional (summatory a) M n := by
  rw [weighted_psi_tail_identity a hM, ← floor_sum_interchange a hM,
    floor_sum_summatory a hM, reciprocal_tail_abel a hM hMn,
    interval_sum_eq_summatory_diff a hMn]
  unfold tailFunctional
  rw [psi_nat_ratio]
  simp only [sum_sub_distrib, sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (hM.trans_le hMn).ne'
  field_simp
  ring

/-- Title: `The actual collision coefficients have the exact sawtooth tail functional`. -/
theorem coefficient_tail_functional {M n : ℕ} (hM : 0 < M) (hMn : M ≤ n) :
    (∑ k ∈ Ioc M n, coefficient k * psi ((n : ℝ) / k)) =
      tailFunctional cumulativeWeight M n := by
  rw [weighted_psi_tail_functional coefficient hM hMn]
  congr 1
  funext t
  exact coefficient_summatory t

end NField.Alignment.StationaryTailFunctional

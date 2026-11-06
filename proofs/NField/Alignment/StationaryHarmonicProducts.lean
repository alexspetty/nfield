/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StationaryDiagonalDefinitions
import NField.Alignment.DivisorHarmonicMain

/-! # The precise harmonic product used in the cumulative-weight expansion -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.StationaryHarmonicProducts
open scoped BigOperators
open CollisionStationaryAgeAsymptotic CollisionHarmonicRemainder
  DivisorHarmonicMain MobiusReciprocalSquare CollisionMassReadout

def harmonicMain (u : ℝ) : ℝ :=
  Real.log u ^ 2 / 2 + Real.eulerMascheroniConstant * Real.log u +
    (Real.eulerMascheroniConstant ^ 2 - Real.pi ^ 2 / 6) / 2

theorem harmonic_square_tail_identity (N : ℕ) :
    Real.pi ^ 2 / 6 - harmonicSquareSum N =
      ∑' j : ℕ, 1 / ((j + N + 1 : ℕ) : ℝ) ^ 2 := by
  have hs := hasSum_zeta_two.summable.sum_add_tsum_nat_add (N + 1)
  have hrange : (∑ d ∈ Finset.range (N + 1), (1 : ℝ) / (d : ℝ) ^ 2) =
      harmonicSquareSum N := by
    symm
    unfold harmonicSquareSum
    apply Finset.sum_subset
    · intro d hd
      simp only [Finset.mem_Icc, Finset.mem_range] at hd ⊢
      omega
    · intro d hd hnot
      have hz : d = 0 := by
        simp only [Finset.mem_Icc, Finset.mem_range] at hd hnot
        omega
      simp [hz]
  rw [← hasSum_zeta_two.tsum_eq, ← hs, hrange, add_sub_cancel_left]
  apply tsum_congr
  intro j
  simp only [Nat.add_assoc]

theorem harmonic_square_tail_bound {N : ℕ} (hN : 1 ≤ N) :
    0 ≤ Real.pi ^ 2 / 6 - harmonicSquareSum N ∧
      Real.pi ^ 2 / 6 - harmonicSquareSum N ≤ 1 / (N : ℝ) := by
  rw [harmonic_square_tail_identity]
  constructor
  · exact tsum_nonneg (fun _ => by positivity)
  · convert shifted_reciprocal_square_tsum_le hN using 1
    apply tsum_congr
    intro j
    rw [Real.rpow_neg (by positivity), Real.rpow_two]
    simp only [one_div]

theorem harmonic_center_error {N : ℕ} (hN : 1 ≤ N) :
    0 ≤ (harmonic N : ℝ) - Real.log N - Real.eulerMascheroniConstant ∧
      (harmonic N : ℝ) - Real.log N - Real.eulerMascheroniConstant ≤ 1 / (N : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hlo := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' N
  simp only [Real.eulerMascheroniSeq', if_neg (by omega : N ≠ 0)] at hlo
  constructor
  · linarith
  · rw [harmonic_with_endpoint hN]
    have he := (harmonicError_bounds hN).2.le
    have hhalf : 1 / (2 * (N : ℝ)) ≤ 1 / (N : ℝ) := by
      apply one_div_le_one_div_of_le hN0
      linarith
    linarith

/-- Title: `The finite harmonic product has its full constant term`. -/
theorem harmonic_product_natural_error {N : ℕ} (hN : 1 ≤ N) :
    |((harmonic N : ℝ) ^ 2 - harmonicSquareSum N) / 2 - harmonicMain N| ≤
      2 * (1 + Real.log N) / (N : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hl : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hg0 : 0 ≤ Real.eulerMascheroniConstant := by
    linarith [Real.one_half_lt_eulerMascheroniConstant]
  have hg1 : Real.eulerMascheroniConstant ≤ 1 := by
    linarith [Real.eulerMascheroniConstant_lt_two_thirds]
  have herr := harmonic_center_error hN
  have ht := harmonic_square_tail_bound hN
  have hH := harmonic_le_one_add_log N
  have hH0 := harmonic_nonneg N
  have hfac0 : 0 ≤ (harmonic N : ℝ) + Real.log N + Real.eulerMascheroniConstant := by positivity
  have hfac : (harmonic N : ℝ) + Real.log N + Real.eulerMascheroniConstant ≤
      2 * (1 + Real.log N) := by linarith
  have hs0 : 0 ≤ (harmonic N : ℝ) ^ 2 - (Real.log N + Real.eulerMascheroniConstant) ^ 2 := by
    nlinarith [mul_nonneg herr.1 hfac0]
  have hs : (harmonic N : ℝ) ^ 2 - (Real.log N + Real.eulerMascheroniConstant) ^ 2 ≤
      2 * (1 + Real.log N) / (N : ℝ) := by
    have hmul := mul_le_mul herr.2 hfac hfac0 (by positivity : 0 ≤ 1 / (N : ℝ))
    calc
      _ = ((harmonic N : ℝ) - Real.log N - Real.eulerMascheroniConstant) *
          ((harmonic N : ℝ) + Real.log N + Real.eulerMascheroniConstant) := by ring
      _ ≤ (1 / (N : ℝ)) * (2 * (1 + Real.log N)) := hmul
      _ = _ := by ring
  have hid : ((harmonic N : ℝ) ^ 2 - harmonicSquareSum N) / 2 - harmonicMain N =
      ((harmonic N : ℝ) ^ 2 - (Real.log N + Real.eulerMascheroniConstant) ^ 2 +
        (Real.pi ^ 2 / 6 - harmonicSquareSum N)) / 2 := by
    unfold harmonicMain
    ring
  rw [hid, abs_of_nonneg (div_nonneg (add_nonneg hs0 ht.1) (by norm_num))]
  have hunit : 1 / (N : ℝ) ≤ 2 * (1 + Real.log N) / (N : ℝ) := by
    apply div_le_div_of_nonneg_right _ hN0.le
    linarith
  linarith

end NField.Alignment.StationaryHarmonicProducts

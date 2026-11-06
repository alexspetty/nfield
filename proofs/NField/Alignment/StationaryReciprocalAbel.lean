/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StationaryFloorInterchange
import NField.Alignment.StationarySawtoothIntegrals
import Mathlib.NumberTheory.AbelSummation

/-! # Exact Abel summation for the reciprocal part of the diagonal tail -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.StationaryReciprocalAbel
open scoped BigOperators
open MeasureTheory Finset StationaryFloorInterchange StationarySawtoothIntegrals
  StationaryDiagonalDefinitions

def summatory (a : ℕ → ℝ) (t : ℝ) : ℝ := ∑ k ∈ Icc 0 ⌊t⌋₊, a k

theorem interval_sum_eq_summatory_diff (a : ℕ → ℝ) {M N : ℕ} (hMN : M ≤ N) :
    (∑ k ∈ Ioc M N, a k) = summatory a N - summatory a M := by
  have h := sum_Ioc_consecutive a (Nat.zero_le M) hMN
  have hM := add_sum_Ioc_eq_sum_Icc (f := a) (Nat.zero_le M)
  have hN := add_sum_Ioc_eq_sum_Icc (f := a) (Nat.zero_le N)
  unfold summatory
  simp only [Nat.floor_natCast]
  linarith

theorem floor_sum_summatory (a : ℕ → ℝ) {M n : ℕ} (hM : 0 < M) :
    (∑ k ∈ Ioc M n, a k * (n / k : ℕ)) =
      ∑ j ∈ Icc 1 (n / M), (summatory a ((n : ℝ) / j) - summatory a M) := by
  rw [floor_sum_interchange a hM]
  apply sum_congr rfl
  intro j hj
  have hj0 : 0 < j := (mem_Icc.mp hj).1
  have hMj : M ≤ n / j := (Nat.le_div_iff_mul_le hj0).mpr (by
    simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hM).mp (mem_Icc.mp hj).2)
  rw [interval_sum_eq_summatory_diff a hMj]
  simp only [summatory, Nat.floor_div_eq_div, Nat.floor_natCast]

/-- Title: `Abel summation evaluates the reciprocal diagonal tail exactly`. -/
theorem reciprocal_tail_abel (a : ℕ → ℝ) {M n : ℕ} (hM : 0 < M) (hMn : M ≤ n) :
    (∑ k ∈ Ioc M n, a k / k) = summatory a n / n - summatory a M / M +
      ∫ t in (M : ℝ)..n, summatory a t / t ^ 2 := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hMnR : (M : ℝ) ≤ n := by exact_mod_cast hMn
  have hne {t : ℝ} (ht : t ∈ Set.Icc (M : ℝ) n) : t ≠ 0 :=
    ne_of_gt (hMR.trans_le ht.1)
  have hd : ∀ t ∈ Set.Icc (M : ℝ) n, DifferentiableAt ℝ (fun x : ℝ => 1 / x) t :=
    fun t ht => (inverse_hasDerivAt (hne ht)).differentiableAt
  have hderiv (t : ℝ) : deriv (fun x : ℝ => 1 / x) t = -1 / t ^ 2 := by
    simp only [one_div, deriv_inv, neg_div, one_div]
  have hc : ContinuousOn (fun t : ℝ => -1 / t ^ 2) (Set.Icc (M : ℝ) n) :=
    continuousOn_const.div (continuousOn_id.pow 2) (fun t ht => pow_ne_zero 2 (hne ht))
  have hi : IntegrableOn (deriv (fun x : ℝ => 1 / x)) (Set.Icc (M : ℝ) n) := by
    rw [show deriv (fun x : ℝ => 1 / x) = (fun t : ℝ => -1 / t ^ 2) from funext hderiv]
    exact hc.integrableOn_Icc
  have hh := sum_mul_eq_sub_sub_integral_mul' a hMn hd hi
  have hleft (k : ℕ) : (1 / (k : ℝ)) * a k = a k / k := by ring
  have hright (t : ℝ) : (-1 / t ^ 2) * (∑ k ∈ Icc 0 ⌊t⌋₊, a k) =
      -(summatory a t / t ^ 2) := by unfold summatory; ring
  simp only [hleft, hderiv, hright, integral_neg] at hh
  rw [← intervalIntegral.integral_of_le hMnR] at hh
  convert! hh using 1
  simp only [summatory, Nat.floor_natCast]
  ring

theorem coefficient_summatory (t : ℝ) : summatory coefficient t = cumulativeWeight t := by
  unfold summatory cumulativeWeight
  symm
  apply sum_subset
  · intro k hk
    exact mem_Icc.mpr ⟨Nat.zero_le k, (mem_Icc.mp hk).2⟩
  · intro k hk hnot
    have hk0 : k = 0 := by simp only [mem_Icc] at hk hnot; omega
    subst k
    simp [coefficient]

end NField.Alignment.StationaryReciprocalAbel

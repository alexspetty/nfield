/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StationaryExactDiagonal

/-! # The exact nonpositive cumulative sum of the moving diagonal -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.StationaryIncompleteCycles
open scoped BigOperators
open CollisionRemainderDynamics StationaryDiagonalDefinitions

/-- Title: `Exact centered remainder sum over an incomplete cycle`. -/
theorem centered_incomplete_cycle {k N : ℕ} (hk : 2 ≤ k) (hN : k ≤ N) :
    (∑ n ∈ Finset.Icc k N, centeredRemainder k n) =
      -(1 / 2 : ℝ) * ((N % k : ℕ) + 1) * ((k : ℝ) - 1 - (N % k : ℕ)) := by
  induction N, hN using Nat.le_induction with
  | base => simp [centeredRemainder]; ring
  | succ N hN ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    have hr := Nat.mod_lt N (show 0 < k by omega)
    have hone : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
    by_cases hwrap : N % k + 1 = k
    · have hz : (N + 1) % k = 0 := by rw [Nat.add_mod, hone, hwrap, Nat.mod_self]
      have he : ((N % k : ℕ) : ℝ) + 1 = k := by exact_mod_cast hwrap
      simp only [centeredRemainder, hz, Nat.cast_zero]
      nlinarith
    · have hz : (N + 1) % k = N % k + 1 := by
        rw [Nat.add_mod, hone, Nat.mod_eq_of_lt (by omega : N % k + 1 < k)]
      simp only [centeredRemainder, hz, Nat.cast_add, Nat.cast_one]
      ring

theorem triangular_sum (N : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 n, f k n) =
      ∑ k ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc k N, f k n := by
  calc
    _ = ∑ n ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, if k ≤ n then f k n else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext k
        have := (Finset.mem_Icc.mp hn).2
        simp only [Finset.mem_filter, Finset.mem_Icc]
        omega
      · intro k hk; rfl
    _ = ∑ k ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, if k ≤ n then f k n else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext n
        have := (Finset.mem_Icc.mp hk).1
        simp only [Finset.mem_filter, Finset.mem_Icc]
        omega
      · intro n hn; rfl

/-- Title: `The cumulative moving diagonal is an exact incomplete-cycle sum`. -/
theorem diagonal_total (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, diagonal n) =
      -(1 / 3 : ℝ) * ∑ k ∈ Finset.Icc 1 N,
        collisionWeight k * ((N % k : ℕ) + 1) * ((k : ℝ) - 1 - (N % k : ℕ)) := by
  simp only [diagonal, age_as_sum_from_one]
  rw [← Finset.mul_sum, triangular_sum]
  simp_rw [← Finset.mul_sum]
  have he : (∑ k ∈ Finset.Icc 1 N, collisionWeight k *
      ∑ n ∈ Finset.Icc k N, centeredRemainder k n) =
      -(1 / 2 : ℝ) * ∑ k ∈ Finset.Icc 1 N,
        collisionWeight k * ((N % k : ℕ) + 1) * ((k : ℝ) - 1 - (N % k : ℕ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hk1 : k = 1
    · subst k; simp [weight_one]
    · rw [centered_incomplete_cycle (by have := (Finset.mem_Icc.mp hk).1; omega)
        (Finset.mem_Icc.mp hk).2]
      ring
  rw [he]
  ring

/-- Title: `The moving diagonal has a nonpositive cumulative sum`. -/
theorem diagonal_total_nonpos (N : ℕ) : (∑ n ∈ Finset.Icc 1 N, diagonal n) ≤ 0 := by
  rw [diagonal_total]
  apply mul_nonpos_of_nonpos_of_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro k hk
  have hk0 := (Finset.mem_Icc.mp hk).1
  have hr : (N % k : ℕ) + 1 ≤ k := Nat.mod_lt N hk0
  have hrR : ((N % k : ℕ) : ℝ) + 1 ≤ k := by exact_mod_cast hr
  exact mul_nonneg (mul_nonneg (collisionWeight_nonneg _) (by positivity)) (by linarith)

end NField.Alignment.StationaryIncompleteCycles

/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StationaryExactDiagonal

/-! # Exact finite treatment of every reciprocal sawtooth jump -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.StationaryFloorInterchange
open scoped BigOperators
open Finset StationaryDiagonalDefinitions

theorem floor_multiplicity (a : ℕ → ℝ) {M n k : ℕ} (hM : 0 < M)
    (hk : k ∈ Ioc M n) :
    a k * (n / k : ℕ) = ∑ j ∈ Icc 1 (n / M), if k * j ≤ n then a k else 0 := by
  have hk0 : 0 < k := lt_trans hM (mem_Ioc.mp hk).1
  have hle : n / k ≤ n / M := Nat.div_le_div_left (mem_Ioc.mp hk).1.le hM
  have he : (Icc 1 (n / M)).filter (fun j => k * j ≤ n) = Icc 1 (n / k) := by
    ext j
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨hj, _⟩, hkj⟩
      exact ⟨hj, (Nat.le_div_iff_mul_le hk0).mpr (by simpa [Nat.mul_comm] using hkj)⟩
    · rintro ⟨hj, hkj⟩
      exact ⟨⟨hj, hkj.trans hle⟩, by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hk0).mp hkj⟩
  rw [← sum_filter, he]
  simp [mul_comm]

/-- Title: `Every integer reciprocal jump is retained by exact finite interchange`. -/
theorem floor_sum_interchange (a : ℕ → ℝ) {M n : ℕ} (hM : 0 < M) :
    (∑ k ∈ Ioc M n, a k * (n / k : ℕ)) =
      ∑ j ∈ Icc 1 (n / M), ∑ k ∈ Ioc M (n / j), a k := by
  calc
    _ = ∑ k ∈ Ioc M n, ∑ j ∈ Icc 1 (n / M), if k * j ≤ n then a k else 0 := by
      exact sum_congr rfl (fun k hk => floor_multiplicity a hM hk)
    _ = ∑ j ∈ Icc 1 (n / M), ∑ k ∈ Ioc M n, if k * j ≤ n then a k else 0 := by
      rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro j hj
      have hj0 : 0 < j := (mem_Icc.mp hj).1
      have he : (Ioc M n).filter (fun k => k * j ≤ n) = Ioc M (n / j) := by
        ext k
        simp only [mem_filter, mem_Ioc]
        constructor
        · rintro ⟨⟨hMk, _⟩, hkj⟩
          exact ⟨hMk, (Nat.le_div_iff_mul_le hj0).mpr hkj⟩
        · rintro ⟨hMk, hkj⟩
          exact ⟨⟨hMk, hkj.trans (Nat.div_le_self _ _)⟩, (Nat.le_div_iff_mul_le hj0).mp hkj⟩
      rw [← sum_filter, he]

theorem psi_nat_ratio (n k : ℕ) :
    psi ((n : ℝ) / k) = (n : ℝ) / k - (n / k : ℕ) - 1 / 2 := by
  unfold psi Int.fract
  rw [← natCast_floor_eq_intCast_floor (by positivity : (0 : ℝ) ≤ (n : ℝ) / k), Nat.floor_div_eq_div]

/-- Title: `The moving sawtooth tail has an exact reciprocal-floor decomposition`. -/
theorem weighted_psi_tail_identity (a : ℕ → ℝ) {M n : ℕ} (hM : 0 < M) :
    (∑ k ∈ Ioc M n, a k * psi ((n : ℝ) / k)) =
      (n : ℝ) * (∑ k ∈ Ioc M n, a k / k) -
        (∑ j ∈ Icc 1 (n / M), ∑ k ∈ Ioc M (n / j), a k) -
          (1 / 2 : ℝ) * ∑ k ∈ Ioc M n, a k := by
  rw [← floor_sum_interchange a hM]
  simp only [mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro k hk
  rw [psi_nat_ratio]
  ring

end NField.Alignment.StationaryFloorInterchange

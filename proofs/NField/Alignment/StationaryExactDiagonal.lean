/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StationaryDiagonalDefinitions

/-! # Exact raw-sawtooth and Möbius coordinates of the moving diagonal -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.StationaryExactDiagonal
open scoped BigOperators
open StationaryDiagonalDefinitions CollisionRemainderDynamics ReducedHarmonicMobius
  SecondaryCapacityLedger MobiusReciprocalSquare

/-- Title: `The moving diagonal uses the raw sawtooth at every integer atom`. -/
theorem diagonal_psi (n : ℕ) :
    diagonal n = (2 / 3 : ℝ) *
      ∑ k ∈ Finset.Icc 1 n, coefficient k * psi ((n : ℝ) / k) + weightPrefix n / 3 := by
  rw [diagonal, age_as_sum_from_one]
  have he : (∑ k ∈ Finset.Icc 1 n, collisionWeight k * centeredRemainder k n) =
      (∑ k ∈ Finset.Icc 1 n, coefficient k * psi ((n : ℝ) / k)) + weightPrefix n / 2 := by
    unfold weightPrefix
    rw [Finset.sum_div, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [centered_remainder_psi n (Finset.mem_Icc.mp hk).1]
    unfold coefficient
    ring
  rw [he]
  ring

theorem coefficient_mobius {k : ℕ} (hk : 0 < k) :
    coefficient k = ∑ d ∈ k.divisors,
      mobiusReciprocalSquare d * (harmonic (k / d - 1) : ℝ) / (k / d : ℕ) := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [coefficient, collisionWeight, reducedHarmonicStar_moebius hk,
    Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdk := (Nat.mem_divisors.mp hd).1
  have hdpos := Nat.pos_of_dvd_of_pos hdk hk
  have hnpos := Nat.div_pos (Nat.le_of_dvd hk hdk) hdpos
  have hde : (k : ℝ) = (d : ℝ) * ((k / d : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mul_div_cancel' hdk).symm
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hdpos.ne'
  have hnR : ((k / d : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
  unfold mobiusReciprocalSquare
  rw [hde]
  field_simp

theorem weighted_coefficient_mobius (N : ℕ) (f : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 1 N, coefficient k * f k) =
      ∑ d ∈ Finset.Icc 1 N, mobiusReciprocalSquare d *
        ∑ j ∈ Finset.Icc 1 (N / d), (harmonic (j - 1) : ℝ) / j * f (d * j) := by
  have he : (∑ k ∈ Finset.Icc 1 N, coefficient k * f k) =
      ∑ k ∈ Finset.Icc 1 N, ∑ d ∈ k.divisors,
        mobiusReciprocalSquare d * (harmonic (k / d - 1) : ℝ) / (k / d : ℕ) * f (d * (k / d)) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [coefficient_mobius (Finset.mem_Icc.mp hk).1, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Nat.mul_div_cancel' (Nat.mem_divisors.mp hd).1]
  rw [he, sum_divisor_triangle N (fun d j =>
    mobiusReciprocalSquare d * (harmonic (j - 1) : ℝ) / j * f (d * j))]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Title: `The moving diagonal has the exact Möbius sawtooth expansion`. -/
theorem diagonal_mobius (n : ℕ) :
    diagonal n = (2 / 3 : ℝ) *
      (∑ d ∈ Finset.Icc 1 n, mobiusReciprocalSquare d *
        ∑ j ∈ Finset.Icc 1 (n / d), (harmonic (j - 1) : ℝ) / j *
          psi ((n : ℝ) / ((d * j : ℕ) : ℝ))) + weightPrefix n / 3 := by
  rw [diagonal_psi, weighted_coefficient_mobius]

end NField.Alignment.StationaryExactDiagonal

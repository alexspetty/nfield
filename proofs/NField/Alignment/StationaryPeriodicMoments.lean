/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StationaryPeriodicBounds
import NField.Alignment.CollisionPotentialHilbert

/-! # Quantitative dyadic first and second moments of the finite stationary potential -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.StationaryPeriodicMoments
open scoped BigOperators
open CollisionRemainderDynamics CollisionMassReadout CollisionPotentialHilbert
  StationaryDiagonalDefinitions StationaryPeriodicBounds

def squareWeightedMass (L : ℕ) : ℝ := ∑ k ∈ Finset.Icc 2 L, collisionWeight k * (k : ℝ) ^ 2

theorem squareWeightedMass_nonneg (L : ℕ) : 0 ≤ squareWeightedMass L := by
  exact Finset.sum_nonneg (fun _ _ => mul_nonneg (collisionWeight_nonneg _) (sq_nonneg _))

theorem squareWeightedMass_bound {L : ℕ} (hL : 1 ≤ L) :
    squareWeightedMass L ≤ (L : ℝ) * (1 + Real.log L) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hlog : 0 ≤ 1 + Real.log L := by linarith [Real.log_nonneg (by exact_mod_cast hL : (1 : ℝ) ≤ L)]
  calc
    _ ≤ ∑ _k ∈ Finset.Icc 2 L, (1 + Real.log L) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k from lt_of_lt_of_le (by norm_num) (Finset.mem_Icc.mp hk).1)
      have hkL : (k : ℝ) ≤ L := by exact_mod_cast (Finset.mem_Icc.mp hk).2
      have hh := mul_le_mul_of_nonneg_right (collisionWeight_log_bound (k := k) (by have := (Finset.mem_Icc.mp hk).1; omega))
        (sq_nonneg (k : ℝ))
      have he : ((1 + Real.log k) / (k : ℝ) ^ 2) * (k : ℝ) ^ 2 = 1 + Real.log k := by field_simp
      rw [he] at hh
      exact hh.trans (by linarith [Real.log_le_log hk0 hkL])
    _ = ((Finset.Icc 2 L).card : ℝ) * (1 + Real.log L) := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hlog
      exact_mod_cast (show (Finset.Icc 2 L).card ≤ L by simp)

theorem finite_age_interval_sum (L a b : ℕ) :
    (∑ n ∈ Finset.Ioc a b, finiteAge collisionWeight L n) =
      (2 / 3 : ℝ) * ∑ k ∈ Finset.Icc 2 L,
        collisionWeight k * ∑ n ∈ Finset.Ioc a b, centeredRemainder k n := by
  simp only [finiteAge, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mul_sum]

theorem finite_age_interval_bound (L : ℕ) {a b : ℕ} (hab : a ≤ b) :
    |∑ n ∈ Finset.Ioc a b, finiteAge collisionWeight L n| ≤ (2 / 3 : ℝ) * squareWeightedMass L := by
  rw [finite_age_interval_sum, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2 / 3)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    _ ≤ ∑ k ∈ Finset.Icc 2 L, |collisionWeight k * ∑ n ∈ Finset.Ioc a b, centeredRemainder k n| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro k hk
      rw [abs_mul, abs_of_nonneg (collisionWeight_nonneg k)]
      exact mul_le_mul_of_nonneg_left (centered_remainder_interval_bound
        (by have := (Finset.mem_Icc.mp hk).1; omega) hab) (collisionWeight_nonneg k)

/-- Title: `The finite stationary potential has the stated dyadic first-moment rate`. -/
theorem periodic_first_moment {L X : ℕ} (hL : 1 ≤ L) (hX : 0 < X) :
    |dyadicMean X (finiteAge collisionWeight L)| ≤
      (2 / 3 : ℝ) * (L : ℝ) * (1 + Real.log L) / X := by
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  unfold dyadicMean
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hX0.le)]
  calc
    _ ≤ (X : ℝ)⁻¹ * ((2 / 3 : ℝ) * squareWeightedMass L) :=
      mul_le_mul_of_nonneg_left (finite_age_interval_bound L (by omega)) (inv_nonneg.mpr hX0.le)
    _ ≤ (X : ℝ)⁻¹ * ((2 / 3 : ℝ) * ((L : ℝ) * (1 + Real.log L))) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (squareWeightedMass_bound hL)
        (by norm_num)) (inv_nonneg.mpr hX0.le)
    _ = _ := by ring

theorem finite_age_square_expansion (L n : ℕ) :
    finiteAge collisionWeight L n ^ 2 = (4 / 9 : ℝ) *
      ∑ k ∈ Finset.Icc 2 L, ∑ l ∈ Finset.Icc 2 L,
        collisionWeight k * collisionWeight l * (centeredRemainder k n * centeredRemainder l n) := by
  unfold finiteAge
  rw [mul_pow]
  norm_num only
  rw [pow_two, Finset.sum_mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  ring

theorem finite_age_square_interval_error (L : ℕ) {a b : ℕ} (hab : a ≤ b) :
    (∑ n ∈ Finset.Ioc a b, finiteAge collisionWeight L n ^ 2) -
      ((b : ℝ) - a) * ‖finitePotential collisionWeight L‖ ^ 2 =
      (4 / 9 : ℝ) * ∑ k ∈ Finset.Icc 2 L, ∑ l ∈ Finset.Icc 2 L,
        collisionWeight k * collisionWeight l *
          ((∑ n ∈ Finset.Ioc a b, centeredRemainder k n * centeredRemainder l n) -
            ((b : ℝ) - a) * (((k.gcd l : ℝ) ^ 2 - 1) / 12)) := by
  rw [finite_potential_norm_sq]
  simp only [finite_age_square_expansion, ← Finset.mul_sum]
  have he : (∑ n ∈ Finset.Ioc a b, ∑ k ∈ Finset.Icc 2 L, ∑ l ∈ Finset.Icc 2 L,
      collisionWeight k * collisionWeight l * (centeredRemainder k n * centeredRemainder l n)) =
      ∑ k ∈ Finset.Icc 2 L, ∑ l ∈ Finset.Icc 2 L, collisionWeight k * collisionWeight l *
        ∑ n ∈ Finset.Ioc a b, centeredRemainder k n * centeredRemainder l n := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l hl
    rw [Finset.mul_sum]
  rw [he]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  simp only [← Finset.mul_sum]
  ring

theorem finite_age_second_error_bound (L : ℕ) {a b : ℕ} (hab : a ≤ b) :
    |(∑ n ∈ Finset.Ioc a b, finiteAge collisionWeight L n ^ 2) -
      ((b : ℝ) - a) * ‖finitePotential collisionWeight L‖ ^ 2| ≤
      (4 / 9 : ℝ) * squareWeightedMass L ^ 2 := by
  rw [finite_age_square_interval_error L hab, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4 / 9)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    _ ≤ ∑ k ∈ Finset.Icc 2 L, ∑ l ∈ Finset.Icc 2 L,
        |collisionWeight k * collisionWeight l *
          ((∑ n ∈ Finset.Ioc a b, centeredRemainder k n * centeredRemainder l n) -
            ((b : ℝ) - a) * (((k.gcd l : ℝ) ^ 2 - 1) / 12))| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ k ∈ Finset.Icc 2 L, ∑ l ∈ Finset.Icc 2 L,
        collisionWeight k * collisionWeight l * ((k : ℝ) ^ 2 * (l : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro l hl
      rw [abs_mul, abs_of_nonneg (mul_nonneg (collisionWeight_nonneg _) (collisionWeight_nonneg _))]
      exact mul_le_mul_of_nonneg_left (centered_product_interval_bound
        (by have := (Finset.mem_Icc.mp hk).1; omega)
        (by have := (Finset.mem_Icc.mp hl).1; omega) hab)
        (mul_nonneg (collisionWeight_nonneg _) (collisionWeight_nonneg _))
    _ = _ := by
      rw [squareWeightedMass, pow_two, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      ring

/-- Title: `The finite stationary second moment approaches its actual Haar norm at the stated rate`. -/
theorem periodic_second_moment {L X : ℕ} (hL : 1 ≤ L) (hX : 0 < X) :
    |dyadicMean X (fun n => finiteAge collisionWeight L n ^ 2) -
      ‖finitePotential collisionWeight L‖ ^ 2| ≤
      (4 / 9 : ℝ) * (L : ℝ) ^ 2 * (1 + Real.log L) ^ 2 / X := by
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have he : dyadicMean X (fun n => finiteAge collisionWeight L n ^ 2) -
      ‖finitePotential collisionWeight L‖ ^ 2 =
      (X : ℝ)⁻¹ * ((∑ n ∈ Finset.Ioc X (2 * X), finiteAge collisionWeight L n ^ 2) -
        (((2 * X : ℕ) : ℝ) - X) * ‖finitePotential collisionWeight L‖ ^ 2) := by
    unfold dyadicMean
    push_cast
    field_simp
    ring
  rw [he, abs_mul, abs_of_nonneg (inv_nonneg.mpr hX0.le)]
  calc
    _ ≤ (X : ℝ)⁻¹ * ((4 / 9 : ℝ) * squareWeightedMass L ^ 2) :=
      mul_le_mul_of_nonneg_left (finite_age_second_error_bound L (by omega)) (inv_nonneg.mpr hX0.le)
    _ ≤ (X : ℝ)⁻¹ * ((4 / 9 : ℝ) * ((L : ℝ) * (1 + Real.log L)) ^ 2) := by
      gcongr
      exact squareWeightedMass_nonneg L
      exact squareWeightedMass_bound hL
    _ = _ := by ring

end NField.Alignment.StationaryPeriodicMoments

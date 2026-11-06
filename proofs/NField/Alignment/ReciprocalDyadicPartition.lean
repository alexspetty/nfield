/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ReciprocalDyadicDecay
import Mathlib.Data.Nat.Log

/-! # Exact finite dyadic partition with a truncated final block -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.ReciprocalDyadicPartition
open ReciprocalBlockDiscrepancy FejerWeightedDiscrepancy
open scoped BigOperators Classical

def start (j : ℕ) : ℕ := 4*2^j

def length (Y j : ℕ) : ℕ := min (start j) (Y-start j)

def prefixSum {A : Type*} [AddCommMonoid A] (f : ℕ → A) (Y : ℕ) : A :=
  ∑ i ∈ Finset.range Y, f (i+1)

theorem length_le_start (Y j : ℕ) : length Y j ≤ start j := min_le_left _ _

theorem truncated_step {A : Type*} [AddCommMonoid A] (f : ℕ → A) (Y p : ℕ) :
    prefixSum f (min Y p) + (∑ i ∈ Finset.range (min p (Y-p)), f (p+i+1)) =
      prefixSum f (min Y (2*p)) := by
  by_cases hy : Y ≤ p
  · have hmin : min Y p = Y := min_eq_left hy
    have hmin' : min Y (2*p) = Y := min_eq_left (by omega)
    simp [hmin, hmin', Nat.sub_eq_zero_of_le hy]
  · have hmin : min Y p = p := min_eq_right (by omega)
    have he : min Y (2*p) = p+min p (Y-p) := by omega
    rw [hmin, he]
    unfold prefixSum
    rw [Finset.sum_range_add]

theorem prefix_partition {A : Type*} [AddCommMonoid A] (f : ℕ → A) (Y N : ℕ) :
    prefixSum f (min Y (start N)) = prefixSum f (min Y 4) +
      ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range (length Y j), f (start j+i+1) := by
  induction N with
  | zero => simp [start]
  | succ N ih =>
      have he : start (N+1) = 2*start N := by unfold start; rw [pow_succ]; omega
      rw [he, ← truncated_step f Y (start N), ih, Finset.sum_range_succ]
      simp only [length]
      rw [add_assoc]

theorem full_prefix_partition {A : Type*} [AddCommMonoid A] (f : ℕ → A)
    (Y N : ℕ) (hY : Y ≤ start N) :
    prefixSum f Y = prefixSum f (min Y 4) +
      ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range (length Y j), f (start j+i+1) := by
  simpa only [min_eq_left hY] using prefix_partition f Y N

/-- A canonical finite number of blocks reaches every positive endpoint. -/
theorem logarithmic_cover (Y : ℕ) : Y ≤ start (Nat.log 2 Y) := by
  have hh := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) Y
  rw [pow_succ] at hh
  unfold start
  omega

/-- The unweighted dyadic start costs sum to an absolute multiple of Y. -/
theorem dyadic_start_cost (Y : ℕ) (hY : 0 < Y) (x : ℝ) (hx : 0 < x) :
    (∑ j ∈ Finset.range (Nat.log 2 Y), (start j : ℝ)/x) ≤ 4*(Y : ℝ)/x := by
  have hg := geom_sum_mul (2 : ℝ) (Nat.log 2 Y)
  norm_num at hg
  have hp := Nat.pow_log_le_self 2 (by omega : Y ≠ 0)
  have hpr : (2 : ℝ)^(Nat.log 2 Y) ≤ Y := by exact_mod_cast hp
  have he : (∑ j ∈ Finset.range (Nat.log 2 Y), (start j : ℝ)/x) =
      4*(∑ j ∈ Finset.range (Nat.log 2 Y), (2 : ℝ)^j)/x := by
    simp only [start, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow,
      Finset.sum_div, Finset.mul_sum]
  rw [he]
  apply div_le_div_of_nonneg_right _ hx.le
  nlinarith

/-- Centered observables decompose exactly, including empty tail blocks. -/
theorem centered_partition (Y : ℕ) (x α : ℝ) :
    prefixSum (fun n => (n : ℝ)⁻¹*((if Int.fract (x/n) < α then 1 else 0)-α)) Y =
      prefixSum (fun n => (n : ℝ)⁻¹*((if Int.fract (x/n) < α then 1 else 0)-α)) (min Y 4) +
      ∑ j ∈ Finset.range (Nat.log 2 Y),
        (blockDistribution (start j) (length Y j) x α - α*blockMass (start j) (length Y j)) := by
  rw [full_prefix_partition _ Y (Nat.log 2 Y) (logarithmic_cover Y)]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  unfold blockDistribution thresholdSum blockMass
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The initial four samples have bounded centered discrepancy, including atoms. -/
theorem initial_centered_bound (Y : ℕ) (x α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    |prefixSum (fun n => (n : ℝ)⁻¹*((if Int.fract (x/n) < α then 1 else 0)-α)) (min Y 4)| ≤ 4 := by
  have hh (i : ℕ) :
      |(((i+1 : ℕ) : ℝ)⁻¹)*((if Int.fract (x/((i+1 : ℕ) : ℝ)) < α then 1 else 0)-α)| ≤ 1 := by
    have ha : |(if Int.fract (x/((i+1 : ℕ) : ℝ)) < α then (1 : ℝ) else 0)-α| ≤ 1 := by
      split_ifs <;> apply abs_le.mpr <;> constructor <;> linarith
    have hw := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
      (show (1 : ℝ) ≤ (i+1 : ℕ) by exact_mod_cast (by omega : 1 ≤ i+1))
    simp only [one_div] at hw
    rw [abs_mul, abs_of_nonneg (by positivity)]
    have hm := mul_le_mul_of_nonneg_left ha (show 0 ≤ (((i+1 : ℕ) : ℝ)⁻¹) by positivity)
    nlinarith
  unfold prefixSum
  calc
    _ ≤ ∑ i ∈ Finset.range (min Y 4),
        |(((i+1 : ℕ) : ℝ)⁻¹)*((if Int.fract (x/((i+1 : ℕ) : ℝ)) < α then 1 else 0)-α)| := by
      simpa only [Real.norm_eq_abs] using norm_sum_le (Finset.range (min Y 4))
        (fun i : ℕ => (((i+1 : ℕ) : ℝ)⁻¹)*((if Int.fract (x/((i+1 : ℕ) : ℝ)) < α then 1 else 0)-α))
    _ ≤ ∑ i ∈ Finset.range (min Y 4), (1 : ℝ) := Finset.sum_le_sum (fun i _ => hh i)
    _ ≤ 4 := by simp

/-- The full centered discrepancy is bounded by the sum of literal block errors. -/
theorem centered_error_sum (Y : ℕ) (x α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    |prefixSum (fun n => (n : ℝ)⁻¹*((if Int.fract (x/n) < α then 1 else 0)-α)) Y| ≤
      4 + ∑ j ∈ Finset.range (Nat.log 2 Y),
        |blockDistribution (start j) (length Y j) x α - α*blockMass (start j) (length Y j)| := by
  rw [centered_partition]
  apply (abs_add_le _ _).trans
  have hh : |∑ j ∈ Finset.range (Nat.log 2 Y),
      (blockDistribution (start j) (length Y j) x α - α*blockMass (start j) (length Y j))| ≤
      ∑ j ∈ Finset.range (Nat.log 2 Y),
      |blockDistribution (start j) (length Y j) x α - α*blockMass (start j) (length Y j)| := by
    simpa only [Real.norm_eq_abs] using norm_sum_le (Finset.range (Nat.log 2 Y))
      (fun j : ℕ => blockDistribution (start j) (length Y j) x α - α*blockMass (start j) (length Y j))
  linarith [initial_centered_bound Y x α hα0 hα1]

end NField.Alignment.ReciprocalDyadicPartition

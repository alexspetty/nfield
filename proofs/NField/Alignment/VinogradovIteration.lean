/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.VinogradovNormalizedRecurrence

/-!
# Iterating the normalized mean-value recurrence

The exponent deficit contracts geometrically at every degree-sized step.
The full product of the explicitly proved step constants is retained.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.VinogradovIteration
open scoped BigOperators Classical
open VinogradovNormalizedRecurrence

def contraction (n : ℕ) : ℝ := 1 - (n : ℝ)⁻¹
def deficit (n t : ℕ) : ℝ := (weight n : ℝ) * contraction n ^ t
def iterationCost (C n s₀ t : ℕ) : ℕ :=
  2 * ∏ i ∈ Finset.range t, stepConstant C n (s₀ + n * i)

theorem contraction_nonneg {n : ℕ} (hn : 1 ≤ n) : 0 ≤ contraction n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hi : (n : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hn0).mpr (by exact_mod_cast hn)
  dsimp [contraction]
  linarith

theorem deficit_nonneg {n : ℕ} (hn : 1 ≤ n) (t : ℕ) : 0 ≤ deficit n t :=
  mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (contraction_nonneg hn) _)

theorem iterationCost_succ (C n s₀ t : ℕ) :
    iterationCost C n s₀ (t + 1) = stepConstant C n (s₀ + n * t) * iterationCost C n s₀ t := by
  simp only [iterationCost, Finset.prod_range_succ]
  ring

theorem deficit_le_exponential {n : ℕ} (hn : 1 ≤ n) (t : ℕ) :
    deficit n t ≤ (weight n : ℝ) * Real.exp (-(t : ℝ) / n) := by
  have hr : contraction n ≤ Real.exp (-(n : ℝ)⁻¹) := by
    have := Real.add_one_le_exp (-(n : ℝ)⁻¹)
    dsimp [contraction]
    linarith
  have hp := pow_le_pow_left₀ (contraction_nonneg hn) hr t
  rw [← Real.exp_nat_mul] at hp
  have he : (t : ℝ) * (-(n : ℝ)⁻¹) = -(t : ℝ) / n := by ring
  rw [he] at hp
  exact mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)

/-- Mean-value exponent decay with the complete, explicit finite product of losses. -/
theorem iterated_mean_bound :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ n s₀ t H : ℕ, 2 ≤ n → n ^ 2 ≤ s₀ → 1 ≤ H →
      mean (s₀ + n * t) n H + 1 ≤
        (iterationCost C n s₀ t : ℝ) * (H : ℝ) ^ deficit n t := by
  obtain ⟨C, hC, hrec⟩ := normalized_recurrence
  refine ⟨C, hC, ?_⟩
  intro n s₀ t H hn hs₀ hH
  have hn1 : 1 ≤ n := by omega
  induction t generalizing H with
  | zero =>
    have hK : weight n ≤ 2 * s₀ := by
      have := (weight_le_sq hn1).trans hs₀
      omega
    have hmean := mean_le_weight_power hH hK
    have hpower : (1 : ℝ) ≤ (H : ℝ) ^ weight n := one_le_pow₀ (by exact_mod_cast hH)
    simp only [Nat.mul_zero, Nat.add_zero, iterationCost, Finset.range_zero,
      Finset.prod_empty, mul_one, Nat.cast_ofNat, deficit, pow_zero,
      Real.rpow_natCast]
    linarith
  | succ t ih =>
    have hs : n ^ 2 ≤ s₀ + n * t := by omega
    obtain ⟨q, hq, hqsmall, hstep⟩ := hrec H n (s₀ + n * t) hH hn hs
    have hi := ih q hq
    have hqpow := Real.rpow_le_rpow (Nat.cast_nonneg q) hqsmall (deficit_nonneg hn1 t)
    have he : ((H : ℝ) ^ contraction n) ^ deficit n t = (H : ℝ) ^ deficit n (t + 1) := by
      rw [← Real.rpow_mul (Nat.cast_nonneg H)]
      congr 1
      dsimp [deficit]
      rw [pow_succ]
      ring
    change (q : ℝ) ^ deficit n t ≤ ((H : ℝ) ^ contraction n) ^ deficit n t at hqpow
    rw [he] at hqpow
    have hindex : s₀ + n * (t + 1) = n + (s₀ + n * t) := by ring
    calc
      _ = mean (n + (s₀ + n * t)) n H + 1 := by rw [hindex]
      _ ≤ _ := hstep
      _ ≤ (stepConstant C n (s₀ + n * t) : ℝ) *
          ((iterationCost C n s₀ t : ℝ) * (q : ℝ) ^ deficit n t) :=
        mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg _)
      _ ≤ (stepConstant C n (s₀ + n * t) : ℝ) *
          ((iterationCost C n s₀ t : ℝ) * (H : ℝ) ^ deficit n (t + 1)) := by gcongr
      _ = _ := by rw [iterationCost_succ, Nat.cast_mul]; ring

end NField.Alignment.VinogradovIteration

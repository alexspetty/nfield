/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.VinogradovLossBudget

/-!
# A uniform classical Vinogradov mean-value bound

The finite recurrence, prime supply, normalization, induction, and loss
budget are combined for every degree at least two and every moment order
at least the square of the degree. Both constants are absolute.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.VinogradovMeanValue
open scoped BigOperators Classical
open VinogradovDiagonal VinogradovNormalizedRecurrence VinogradovIteration VinogradovLossBudget

def baseOrder (l n : ℕ) : ℕ := n ^ 2 + (l - n ^ 2) % n
def stepCount (l n : ℕ) : ℕ := (l - n ^ 2) / n

theorem baseOrder_add_steps {l n : ℕ} (hl : n ^ 2 ≤ l) :
    baseOrder l n + n * stepCount l n = l := by
  have h := Nat.mod_add_div (l - n ^ 2) n
  dsimp [baseOrder, stepCount]
  omega

theorem baseOrder_le_two_sq {l n : ℕ} (hn : 1 ≤ n) : baseOrder l n ≤ 2 * n ^ 2 := by
  have hm := Nat.mod_lt (l - n ^ 2) (show 0 < n by omega)
  dsimp [baseOrder]
  nlinarith

/-- The discrete number of degree-sized steps gives an absolute exponential deficit. -/
theorem deficit_le_uniform {l n : ℕ} (hn : 1 ≤ n) (hl : n ^ 2 ≤ l) :
    deficit n (stepCount l n) ≤
      (n : ℝ) ^ 2 * Real.exp 2 * Real.exp (-(l : ℝ) / (n : ℝ) ^ 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hindex := baseOrder_add_steps hl
  have hbase := baseOrder_le_two_sq (l := l) hn
  have hraw : (l : ℝ) ≤ 2 * (n : ℝ) ^ 2 + (n : ℝ) * stepCount l n := by
    exact_mod_cast (show l ≤ 2 * n ^ 2 + n * stepCount l n by omega)
  have htime : -(stepCount l n : ℝ) / n ≤ 2 - (l : ℝ) / (n : ℝ) ^ 2 := by
    calc
      _ = (-(n : ℝ) * stepCount l n) / (n : ℝ) ^ 2 := by field_simp
      _ ≤ (2 * (n : ℝ) ^ 2 - l) / (n : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
      _ = _ := by field_simp
  calc
    _ ≤ (weight n : ℝ) * Real.exp (-(stepCount l n : ℝ) / n) := deficit_le_exponential hn _
    _ ≤ (n : ℝ) ^ 2 * Real.exp (2 - (l : ℝ) / (n : ℝ) ^ 2) :=
      mul_le_mul (by exact_mod_cast weight_le_sq hn) (Real.exp_le_exp.mpr htime)
        (Real.exp_nonneg _) (sq_nonneg _)
    _ = _ := by rw [sub_eq_add_neg, Real.exp_add]; simp only [neg_div]; ring

/-- Uniform normalized mean values, with the quadratic exponential loss explicit. -/
theorem uniform_normalized_mean_value :
    ∃ A : ℝ, 0 < A ∧ ∀ n l H : ℕ, 2 ≤ n → n ^ 2 ≤ l → 1 ≤ H →
      mean l n H + 1 ≤ Real.exp (A * (l : ℝ) ^ 2) *
        (H : ℝ) ^ ((n : ℝ) ^ 2 * Real.exp 2 * Real.exp (-(l : ℝ) / (n : ℝ) ^ 2)) := by
  obtain ⟨C, hC, hiter⟩ := iterated_mean_bound
  refine ⟨2 * (C : ℝ) + 52, by positivity, ?_⟩
  intro n l H hn hl hH
  have hn1 : 1 ≤ n := by omega
  have hbase : n ^ 2 ≤ baseOrder l n := by dsimp [baseOrder]; omega
  have hindex := baseOrder_add_steps hl
  have hbound := hiter n (baseOrder l n) (stepCount l n) H hn hbase hH
  have hcost := iterationCost_le_exp (C := C) (t := stepCount l n) hn1 hbase
  rw [hindex] at hbound hcost
  have hpower := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hH : (1 : ℝ) ≤ H)
    (deficit_le_uniform hn1 hl)
  exact hbound.trans (mul_le_mul hcost hpower (by positivity) (Real.exp_nonneg _))

/-- The actual integer solution count satisfies a uniform classical Vinogradov estimate. -/
theorem uniform_mean_value :
    ∃ A : ℝ, 0 < A ∧ ∀ n l H : ℕ, 2 ≤ n → n ^ 2 ≤ l → 1 ≤ H →
      (momentCount (Finset.Icc 1 (H : ℤ)) l n : ℝ) ≤
        Real.exp (A * (l : ℝ) ^ 2) *
          (H : ℝ) ^ ((2 * l : ℕ) - (weight n : ℝ) +
            (n : ℝ) ^ 2 * Real.exp 2 * Real.exp (-(l : ℝ) / (n : ℝ) ^ 2)) := by
  obtain ⟨A, hA, hnorm⟩ := uniform_normalized_mean_value
  refine ⟨A, hA, ?_⟩
  intro n l H hn hl hH
  have hH0 : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hK : weight n ≤ 2 * l := by
    have := (weight_le_sq (show 1 ≤ n by omega)).trans hl
    omega
  have hexp : (exponent l n : ℝ) = (2 * l : ℕ) - (weight n : ℝ) := by
    exact Nat.cast_sub hK
  have hm := hnorm n l H hn hl hH
  have hm' : mean l n H ≤ Real.exp (A * (l : ℝ) ^ 2) *
      (H : ℝ) ^ ((n : ℝ) ^ 2 * Real.exp 2 * Real.exp (-(l : ℝ) / (n : ℝ) ^ 2)) := by linarith
  calc
    _ = mean l n H * (H : ℝ) ^ exponent l n := by
      exact (div_mul_cancel₀ _ (ne_of_gt (pow_pos hH0 _))).symm
    _ ≤ (Real.exp (A * (l : ℝ) ^ 2) *
        (H : ℝ) ^ ((n : ℝ) ^ 2 * Real.exp 2 * Real.exp (-(l : ℝ) / (n : ℝ) ^ 2))) *
          (H : ℝ) ^ exponent l n := mul_le_mul_of_nonneg_right hm' (by positivity)
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_natCast (H : ℝ) (exponent l n), ← Real.rpow_add hH0, hexp]
      congr 2
      ring

end NField.Alignment.VinogradovMeanValue

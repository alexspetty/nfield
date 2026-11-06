/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionFluctuationSum
import Mathlib.Analysis.PSeries

/-! # Absolute summability of the constructive-mean correction remainder -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000

namespace NField.Alignment.CollisionPrimeLimits

open Filter Finset
open scoped BigOperators Topology

def correctionTail (b n : ℕ) : ℝ :=
  (((n - 1) % b : ℕ) : ℝ) * ((b : ℝ) - ((n - 1) % b : ℕ)) /
    ((b : ℝ) * ((n : ℝ) - b - 1) * n)

theorem correctionTail_norm_bound {b n : ℕ} (hb : 2 ≤ b)
    (hn : 2 * (b + 1) ≤ n) :
    ‖correctionTail b n‖ ≤ (2 * (b : ℝ)) * (1 / (n : ℝ) ^ 2) := by
  let R : ℝ := ((n - 1) % b : ℕ)
  have hb0 : 0 < (b : ℝ) := by exact_mod_cast (show 0 < b by omega)
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hlarge : 2 * ((b : ℝ) + 1) ≤ n := by exact_mod_cast hn
  have hR0 : 0 ≤ R := Nat.cast_nonneg _
  have hRb : R ≤ b := by
    dsimp only [R]
    exact_mod_cast (Nat.mod_lt (n - 1) (by omega : 0 < b)).le
  have hN : (n : ℝ) / 2 ≤ (n : ℝ) - b - 1 := by linarith
  have hN0 : 0 < (n : ℝ) - b - 1 := by linarith
  have hnum : R * ((b : ℝ) - R) ≤ (b : ℝ) ^ 2 := by
    have h := mul_le_mul hRb (show (b : ℝ) - R ≤ b by linarith)
      (by linarith : 0 ≤ (b : ℝ) - R) hb0.le
    nlinarith
  have hden0 : 0 < (b : ℝ) * ((n : ℝ) - b - 1) * n := by positivity
  have hden : (b : ℝ) * (n : ℝ) ^ 2 / 2 ≤
      (b : ℝ) * ((n : ℝ) - b - 1) * n := by
    have h := mul_le_mul_of_nonneg_left hN (mul_nonneg hb0.le hn0.le)
    nlinarith [h]
  change ‖R * ((b : ℝ) - R) / ((b : ℝ) * ((n : ℝ) - b - 1) * n)‖ ≤ _
  rw [Real.norm_of_nonneg (div_nonneg (mul_nonneg hR0 (sub_nonneg.mpr hRb)) hden0.le)]
  calc
    R * ((b : ℝ) - R) / ((b : ℝ) * ((n : ℝ) - b - 1) * n) ≤
        (b : ℝ) ^ 2 / ((b : ℝ) * ((n : ℝ) - b - 1) * n) :=
      div_le_div_of_nonneg_right hnum hden0.le
    _ ≤ (b : ℝ) ^ 2 / ((b : ℝ) * (n : ℝ) ^ 2 / 2) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hden
    _ = (2 * (b : ℝ)) * (1 / (n : ℝ) ^ 2) := by
      field_simp [hb0.ne', hn0.ne']

/-- Title: `The reciprocal weighted correction remainder is absolutely summable`. -/
theorem correctionTail_summable {b : ℕ} (hb : 2 ≤ b) : Summable (correctionTail b) := by
  have hs : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by omega)
  apply (hs.mul_left (2 * (b : ℝ))).of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop (2 * (b + 1))] with n hn
  exact correctionTail_norm_bound hb hn

theorem correctionTail_prime_summable {b : ℕ} (hb : 2 ≤ b) :
    Summable (fun n : ℕ => if n.Prime then correctionTail b n else 0) := by
  apply ((correctionTail_summable hb).indicator {n | n.Prime}).congr
  intro n
  simp only [Set.indicator_apply, Set.mem_setOf_eq]

end NField.Alignment.CollisionPrimeLimits

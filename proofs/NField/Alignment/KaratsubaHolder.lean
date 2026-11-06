/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KaratsubaTupleSumRange
import Mathlib.Analysis.MeanInequalities

/-! # Finite Holder step for the bilinear prime sum -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KaratsubaHolder
open scoped BigOperators

theorem sum_norm_pow_le {ι : Type*} (S : Finset ι) (f : ι → ℂ) {n : ℕ} (hn : 1 ≤ n) :
    (∑ i ∈ S, ‖f i‖) ^ n ≤ (S.card : ℝ) ^ (n-1) * ∑ i ∈ S, ‖f i‖ ^ n := by
  have h := Real.rpow_sum_le_const_mul_sum_rpow
    (s := S) (f := fun i => ‖f i‖) (p := (n : ℝ)) (by exact_mod_cast hn)
  have he : (n : ℝ)-1 = ((n-1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hn]
    norm_num
  rw [he] at h
  simpa only [abs_norm, Real.rpow_natCast] using h

theorem norm_sum_pow_le {ι : Type*} (S : Finset ι) (f : ι → ℂ) {n : ℕ} (hn : 1 ≤ n) :
    ‖∑ i ∈ S, f i‖ ^ n ≤ (S.card : ℝ) ^ (n-1) * ∑ i ∈ S, ‖f i‖ ^ n := by
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le S f) n).trans (sum_norm_pow_le S f hn)

end NField.Alignment.KaratsubaHolder

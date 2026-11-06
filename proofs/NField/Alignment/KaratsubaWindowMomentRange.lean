/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevPrimeWindows

/-! # The source upper endpoint satisfies the short-range moment inequality -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KaratsubaWindowMomentRange
open KorolevPrimeWindows

/-- The source's factor four leaves enough room for the moment order. -/
theorem order_lt_four_power {k : ℕ} (hk : 1 ≤ k) : k < 4^(2*k-1) := by
  exact (show k < 2^k from Nat.lt_two_pow_self).trans_le
    ((pow_le_pow_left₀ (by norm_num : 0 ≤ (2 : ℕ)) (by norm_num : (2 : ℕ) ≤ 4) k).trans
      (pow_le_pow_right₀ (by norm_num : 1 ≤ (4 : ℕ)) (by omega : k ≤ 2*k-1)))

/-- The literal source upper endpoint meets the strict reciprocal-moment size hypothesis. -/
theorem upperEndpoint_short_moment {M : ℝ} (hM : 0 < M) {k : ℕ} (hk : 1 ≤ k) :
    (k : ℝ)*(upperEndpoint (Real.log M) k)^(2*k-1) < M := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hd : 2*(k : ℝ)-1 ≠ 0 := by linarith
  have hn : ((2*k-1 : ℕ) : ℝ) = 2*(k : ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2*k)]
    norm_num
  have hpow : (upperEndpoint (Real.log M) k)^(2*k-1) = M/(4:ℝ)^(2*k-1) := by
    rw [upperEndpoint, div_pow, ← Real.exp_nat_mul, hn]
    have he : (2*(k : ℝ)-1)*(Real.log M/(2*(k : ℝ)-1)) = Real.log M := by field_simp
    rw [he, Real.exp_log hM]
  rw [hpow]
  have horder : (k : ℝ) < (4 : ℝ)^(2*k-1) := by exact_mod_cast order_lt_four_power hk
  have hp : (0 : ℝ) < (4 : ℝ)^(2*k-1) := by positivity
  rw [← mul_div_assoc]
  apply (div_lt_iff₀ hp).mpr
  nlinarith only [mul_lt_mul_of_pos_right horder hM]

end NField.Alignment.KaratsubaWindowMomentRange

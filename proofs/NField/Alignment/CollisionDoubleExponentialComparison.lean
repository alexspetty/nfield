/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionLowerTailCutoffAlignment

/-!
# The double-exponential comparison for lower tails

A fixed second-moment constant and the lcm logarithm are absorbed by the
strict gap between the chosen cutoff exponent and the requested exponent.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionDoubleExponentialComparison

open Filter CollisionExponentialFloorScale

theorem exponential_scale_domination {d0 d : ℝ} (hd0 : 0 < d0) (hgap : d0 < d) (b : ℝ) :
    ∀ᶠ H : ℝ in atTop, 4*Real.exp (d0*Real.sqrt H)+b ≤ Real.exp (d*Real.sqrt H) := by
  have hexp := Real.tendsto_exp_atTop.comp (tail_exponent_tendsto (sub_pos.mpr hgap))
  have hlarge : ∀ᶠ H : ℝ in atTop, 4+|b| ≤ Real.exp ((d-d0)*Real.sqrt H) :=
    hexp.eventually_ge_atTop (4+|b|)
  filter_upwards [hlarge] with H hH
  have h1 : 1 ≤ Real.exp (d0*Real.sqrt H) := Real.one_le_exp_iff.mpr
    (mul_nonneg hd0.le (Real.sqrt_nonneg H))
  have hb : b ≤ |b| * Real.exp (d0*Real.sqrt H) :=
    (le_abs_self b).trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left h1 (abs_nonneg b))
  calc
    _ ≤ (4+|b|)*Real.exp (d0*Real.sqrt H) := by nlinarith
    _ ≤ Real.exp ((d-d0)*Real.sqrt H)*Real.exp (d0*Real.sqrt H) :=
      mul_le_mul_of_nonneg_right hH (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem double_exponential_below_reciprocal {L : ℕ} {V a : ℝ}
    (hL : 0 < L) (hV : 0 < V) (ha : 2*Real.log (L : ℝ)+Real.log V ≤ a) :
    Real.exp (-a) ≤ 1/((L : ℝ)^2*V) := by
  have hLR : 0 < (L : ℝ) := by exact_mod_cast hL
  have hden : 0 < (L : ℝ)^2*V := mul_pos (sq_pos_of_pos hLR) hV
  have he : Real.log ((L : ℝ)^2*V)=2*Real.log (L : ℝ)+Real.log V := by
    rw [Real.log_mul (pow_ne_zero _ hLR.ne') hV.ne',Real.log_pow]
    norm_num
  have hlog : Real.log ((L : ℝ)^2*V) ≤ a := by rw [he]; exact ha
  have h := Real.exp_le_exp.mpr (neg_le_neg hlog)
  simpa only [Real.exp_neg,Real.exp_log hden,one_div] using h

end NField.Alignment.CollisionDoubleExponentialComparison

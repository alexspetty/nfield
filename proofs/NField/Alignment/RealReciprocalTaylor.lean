/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.RealPolynomialMomentBox
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.Field.GeomSum

/-! # The exact finite reciprocal expansion and its real phase error -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.RealReciprocalTaylor
open scoped BigOperators ComplexConjugate
open RealPolynomialMomentBox

def reciprocalTaylor (Q x z : ℝ) (n : ℕ) : ℝ :=
  Q/x * ∑ j ∈ Finset.range (n+1), (-z/x)^j

theorem reciprocal_taylor_remainder (Q x z : ℝ) (hx : x ≠ 0) (hxz : x+z ≠ 0)
    (n : ℕ) :
    Q/(x+z)-reciprocalTaylor Q x z n = Q/(x+z)*(-z/x)^(n+1) := by
  have hg := geom_sum_mul_neg (-z/x) (n+1)
  have he : 1-(-z/x) = (x+z)/x := by field_simp; ring
  rw [he] at hg
  dsimp [reciprocalTaylor]
  apply (mul_right_inj' hxz).mp
  field_simp at hg ⊢
  rw [hg]
  ring

theorem reciprocal_taylor_remainder_bound (Q x z : ℝ) (hQ : 0 ≤ Q) (hx : 0 < x)
    (hz : 0 ≤ z) (n : ℕ) :
    |Q/(x+z)-reciprocalTaylor Q x z n| ≤ Q/x*(z/x)^(n+1) := by
  have hxz : 0 < x+z := by linarith
  rw [reciprocal_taylor_remainder Q x z hx.ne' hxz.ne' n,
    abs_mul, abs_pow, abs_of_nonneg (div_nonneg hQ hxz.le),
    abs_div, abs_neg, abs_of_nonneg hz, abs_of_pos hx]
  exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hQ hx (by linarith))
    (by positivity)

theorem realCharacter_sub_one_bound (t : ℝ) :
    ‖realCharacter t-1‖ ≤ 2*Real.pi*|t| := by
  change ‖fourier 1 (t : AddCircle (1:ℝ))-1‖ ≤ _
  rw [fourier_coe_apply]
  have he : (2*Real.pi*Complex.I*(1:ℤ)*(t:ℂ)/(1:ℝ)) =
      Complex.I*((2*Real.pi*t:ℝ):ℂ) := by push_cast; ring
  rw [he]
  simpa [norm_mul, Real.norm_eq_abs, abs_of_pos Real.pi_pos] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2*Real.pi*t))

theorem realCharacter_sub_bound (u v : ℝ) :
    ‖realCharacter u-realCharacter v‖ ≤ 2*Real.pi*|u-v| := by
  have he : realCharacter u-realCharacter v =
      realCharacter v*(realCharacter (u-v)-1) := by
    rw [mul_sub, ← AddChar.map_add_eq_mul]
    congr 1 <;> ring
  rw [he,norm_mul,realCharacter_norm,one_mul]
  exact realCharacter_sub_one_bound (u-v)

theorem reciprocal_phase_taylor_bound (Q x z : ℝ) (hQ : 0 ≤ Q) (hx : 0 < x)
    (hz : 0 ≤ z) (n : ℕ) :
    ‖realCharacter (Q/(x+z))-realCharacter (reciprocalTaylor Q x z n)‖ ≤
      2*Real.pi*(Q/x*(z/x)^(n+1)) := by
  exact (realCharacter_sub_bound _ _).trans
    (mul_le_mul_of_nonneg_left (reciprocal_taylor_remainder_bound Q x z hQ hx hz n)
      (by positivity))

end NField.Alignment.RealReciprocalTaylor

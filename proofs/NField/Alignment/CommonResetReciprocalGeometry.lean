/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetCompletedDerivative

/-! # The printed reciprocal phase and its actual curvature on a quotient band -/

noncomputable section

namespace NField.Alignment.CommonResetReciprocalGeometry

open scoped BigOperators
open Set CommonResetCompletedDerivative

theorem reciprocal_first_derivative (b : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => b/y) (-b/x^2) x := by
  convert! (hasDerivAt_const x b).div (hasDerivAt_id' x) hx using 1 <;> simp

theorem reciprocal_second_derivative (b : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => -b/y^2) (2*b/x^3) x := by
  have h := (hasDerivAt_const x (-b)).div ((hasDerivAt_id' x).pow 2) (pow_ne_zero 2 hx)
  convert! h using 1
  simp only [Pi.pow_apply, zero_mul, mul_one, zero_sub, Nat.reduceSub, pow_one]
  field_simp
  ring

/-- Title: `The reciprocal phase has exactly the stated positive curvature across the whole band`. -/
theorem reciprocal_curvature_bounds {X b x : ℝ} (hX : 0 < X) (hb : 0 < b)
    (hx : x ∈ Icc X (2*X)) :
    b/(4*X^3) ≤ 2*b/x^3 ∧ 2*b/x^3 ≤ 8*(b/(4*X^3)) := by
  have hxpos := hX.trans_le hx.1
  have hup : x^3 ≤ (2*X)^3 := pow_le_pow_left₀ hxpos.le hx.2 3
  have hlo : X^3 ≤ x^3 := pow_le_pow_left₀ hX.le hx.1 3
  constructor
  · apply (div_le_div_iff₀ (by positivity : 0 < 4*X^3) (pow_pos hxpos 3)).mpr
    have hm := mul_le_mul_of_nonneg_left hup hb.le
    nlinarith
  · calc
      _ ≤ 2*b/X^3 := div_le_div_of_nonneg_left (by positivity) (pow_pos hX 3) hlo
      _ = _ := by ring

/-- Title: `The actual reciprocal phase satisfies the completed estimate on every band subinterval`. -/
theorem reciprocal_box_completion {u : ℕ} [NeZero u] (n : ZMod u) (a : ℤ) (N : ℕ)
    {X b : ℝ} (hX : 0 < X) (hb : 0 < b)
    (hsub : Icc (a : ℝ) (a+N) ⊆ Icc X (2*X)) :
    ‖reciprocalInterval n a N (fun t : ℝ => b/t)‖ ≤
      12960*(u.divisors.card : ℝ)*Real.sqrt (n.val.gcd u : ℝ)*
        completedDerivativeScale u N (b/(4*X^3)) := by
  have hxpos (x : ℝ) (hx : x ∈ Icc (a : ℝ) (a+N)) : 0 < x :=
    hX.trans_le (hsub hx).1
  have hf : ContinuousOn (fun t : ℝ => b/t) (Icc (a : ℝ) (a+N)) := by
    intro x hx
    exact (reciprocal_first_derivative b (hxpos x hx).ne').continuousAt.continuousWithinAt
  have hg : ContinuousOn (fun t : ℝ => -b/t^2) (Icc (a : ℝ) (a+N)) := by
    intro x hx
    exact (reciprocal_second_derivative b (hxpos x hx).ne').continuousAt.continuousWithinAt
  have hbound := completed_reciprocal_interval_bound n a N
    (fun t : ℝ => b/t) (fun t : ℝ => -b/t^2) (fun t : ℝ => 2*b/t^3)
    (A := 8) (lam := b/(4*X^3)) (by positivity) (by norm_num) hf
    (fun x hx => reciprocal_first_derivative b (hxpos x (Ioo_subset_Icc_self hx)).ne') hg
    (fun x hx => reciprocal_second_derivative b (hxpos x (Ioo_subset_Icc_self hx)).ne')
    (fun x hx => reciprocal_curvature_bounds hX hb (hsub (Ioo_subset_Icc_self hx)))
  norm_num at hbound
  exact hbound

end NField.Alignment.CommonResetReciprocalGeometry

/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.SpectralPower

/-!
# Real sine form of the finite interval kernel

The additive-character quotient used by the reusable spectral-power core is
converted here to the real sine quotient printed for consecutive digit bins.
-/

namespace NField.Alignment.SpectralPower

open NField.Alignment
open ZMod

/-- The negative standard additive character is the complex exponential with
the corresponding negative real angle. -/
theorem stdAddChar_neg_eq_exp_angle {p : ℕ} [NeZero p] (k : ZMod p) :
    stdAddChar (-k) =
      Complex.exp (Complex.I *
        (-(2 * Real.pi * (k.val : ℝ) / (p : ℝ)))) := by
  rw [AddChar.map_neg_eq_inv, stdAddChar_apply, toCircle_apply]
  rw [← Complex.exp_neg]
  congr 1
  push_cast
  ring

private theorem norm_exp_I_mul_pow_sub_one (x : ℝ) (n : ℕ) :
    ‖Complex.exp (Complex.I * x) ^ n - 1‖ =
      ‖2 * Real.sin ((n : ℝ) * x / 2)‖ := by
  rw [← Complex.exp_nat_mul]
  have harg : (n : ℂ) * (Complex.I * (x : ℂ)) =
      Complex.I * (((n : ℝ) * x : ℝ) : ℂ) := by
    push_cast
    ring
  rw [harg]
  exact Complex.norm_exp_I_mul_ofReal_sub_one ((n : ℝ) * x)

/-- Absolute value of the finite interval transform in the real sine form
printed in the manuscript. -/
theorem intervalFourier_norm_eq_sine_quotient (p n : ℕ) [NeZero p]
    {k : ZMod p} (hk : k ≠ 0) :
    ‖intervalFourier p n k‖ =
      |Real.sin (Real.pi * (k.val : ℝ) * n / p)| /
        |Real.sin (Real.pi * (k.val : ℝ) / p)| := by
  rw [intervalFourier_eq_geom_quotient p n hk, norm_div,
    stdAddChar_neg_eq_exp_angle]
  let x : ℝ := -(2 * Real.pi * (k.val : ℝ) / (p : ℝ))
  have hx : -(2 * (Real.pi : ℂ) * ((k.val : ℝ) : ℂ) /
      ((p : ℝ) : ℂ)) = (x : ℂ) := by
    dsimp [x]
    push_cast
    rfl
  rw [hx]
  rw [norm_exp_I_mul_pow_sub_one,
    Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]
  apply congrArg₂ (· / ·)
  · have harg : (n : ℝ) * x / 2 =
        -(Real.pi * (k.val : ℝ) * n / p) := by
      dsimp [x]
      ring
    rw [harg, Real.sin_neg, abs_neg]
  · have harg : x / 2 = -(Real.pi * (k.val : ℝ) / p) := by
      dsimp [x]
      ring
    rw [harg, Real.sin_neg, abs_neg]

/-- Squared interval power in the real sine-ratio form used by the spectral
power formula. -/
theorem intervalPower_eq_sine_quotient_sq (p n : ℕ) [NeZero p]
    {k : ZMod p} (hk : k ≠ 0) :
    intervalPower p n k =
      (((|Real.sin (Real.pi * (k.val : ℝ) * n / p)| /
        |Real.sin (Real.pi * (k.val : ℝ) / p)|) ^ 2 : ℝ) : ℂ) := by
  unfold intervalPower
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
    intervalFourier_norm_eq_sine_quotient p n hk]

/-- The same power with the square distributed across the real sine ratio. -/
theorem intervalPower_eq_sine_sq_div_sq (p n : ℕ) [NeZero p]
    {k : ZMod p} (hk : k ≠ 0) :
    intervalPower p n k =
      (((Real.sin (Real.pi * (k.val : ℝ) * n / p) ^ 2 /
        Real.sin (Real.pi * (k.val : ℝ) / p) ^ 2 : ℝ)) : ℂ) := by
  rw [intervalPower_eq_sine_quotient_sq p n hk, div_pow,
    sq_abs, sq_abs]

end NField.Alignment.SpectralPower

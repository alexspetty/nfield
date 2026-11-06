/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.RealSawtoothDistribution
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-! # The logarithmic boundary value of the Bernoulli Abel series -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.BernoulliAbelPhase
open Complex

def unitPhase (y : ℝ) : ℂ := exp (-2*(Real.pi : ℂ)*I*y)

theorem unitPhase_norm (y : ℝ) : ‖unitPhase y‖ = 1 := by
  simp [unitPhase,Complex.norm_exp,Complex.mul_re,Complex.mul_im]

theorem unitPhase_fract (y : ℝ) : unitPhase (Int.fract y)=unitPhase y := by
  have he : (-2*(Real.pi : ℂ)*I*(y : ℂ)) =
      -2*(Real.pi : ℂ)*I*((Int.fract y : ℝ) : ℂ) +
        (-(⌊y⌋ : ℤ) : ℂ)*(2*(Real.pi : ℂ)*I) := by
    have hy : ((Int.fract y : ℝ) : ℂ)+(⌊y⌋ : ℤ)=y := by
      exact_mod_cast Int.fract_add_floor y
    rw [← hy]
    ring
  unfold unitPhase
  have hz := Complex.exp_int_mul_two_pi_mul_I (-⌊y⌋)
  simp only [Int.cast_neg] at hz
  rw [he,Complex.exp_add,hz,mul_one]

theorem phase_factor (y : ℝ) :
    1-unitPhase y = ((2*Real.sin (Real.pi*y) : ℝ) : ℂ)*
      exp (((Real.pi/2-Real.pi*y : ℝ) : ℂ)*I) := by
  have he : -2*(Real.pi : ℂ)*I*(y : ℂ) = ((-2*(Real.pi*y) : ℝ) : ℂ)*I := by
    push_cast
    ring
  unfold unitPhase
  rw [he]
  apply Complex.ext
  · simp only [Complex.sub_re,Complex.one_re,Complex.mul_re,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
      mul_zero,mul_one,sub_zero,zero_mul,add_zero,neg_mul,Complex.exp_re,Complex.exp_im,
      Real.exp_zero,one_mul,Real.cos_neg,Real.cos_pi_div_two_sub]
    rw [Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi*y)]
  · simp only [Complex.sub_im,Complex.one_im,Complex.mul_re,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
      mul_zero,mul_one,sub_zero,zero_sub,zero_mul,add_zero,neg_mul,Complex.exp_re,Complex.exp_im,
      Real.exp_zero,one_mul,Real.sin_neg,Real.sin_pi_div_two_sub]
    rw [Real.sin_two_mul]
    ring

theorem phase_log_im {y : ℝ} (hy : 0 < y) (hy1 : y < 1) :
    (Complex.log (1-unitPhase y)).im = Real.pi/2-Real.pi*y := by
  have hsin : 0 < Real.sin (Real.pi*y) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  rw [phase_factor,Complex.log_ofReal_mul (by positivity : 0 < 2*Real.sin (Real.pi*y))
    (Complex.exp_ne_zero _)]
  rw [Complex.log_exp]
  · simp
  · simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_im,
      Complex.I_re,mul_one,mul_zero,add_zero]
    nlinarith [Real.pi_pos]
  · simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_im,
      Complex.I_re,mul_one,mul_zero,add_zero]
    nlinarith [Real.pi_pos]

theorem phase_slitPlane {y : ℝ} (hy : 0 < y) (hy1 : y < 1) :
    1-unitPhase y ∈ Complex.slitPlane := by
  have hsin : 0 < Real.sin (Real.pi*y) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  rw [phase_factor,Complex.mem_slitPlane_iff]
  left
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.mul_im,
    Complex.I_re,Complex.I_im,mul_zero,mul_one,sub_zero,zero_mul,add_zero,
    Complex.exp_re,Real.exp_zero,one_mul,Real.cos_pi_div_two_sub]
  positivity

end NField.Alignment.BernoulliAbelPhase

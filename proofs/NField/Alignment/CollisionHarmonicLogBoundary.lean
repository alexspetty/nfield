/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionHarmonicRootSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# The principal logarithm on the full open unit-circle arc

The factorization, magnitude, argument and logarithm are proved for every
real angle strictly between zero and two pi, as required by the harmonic
root identity. No restriction to rational angles is used.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionHarmonicLogBoundary

open CollisionHarmonicRootSeries

theorem one_sub_circle_exp_factor (θ : ℝ) :
    (1 : ℂ)-Complex.exp ((θ : ℂ)*Complex.I) =
      ((2*Real.sin (θ/2) : ℝ) : ℂ)*
        (((Real.cos (θ/2-Real.pi/2) : ℝ) : ℂ)+
          ((Real.sin (θ/2-Real.pi/2) : ℝ) : ℂ)*Complex.I) := by
  rw [Complex.exp_mul_I,← Complex.ofReal_cos,← Complex.ofReal_sin]
  apply Complex.ext
  · simp only [Complex.sub_re,Complex.one_re,Complex.add_re,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
      mul_zero,zero_mul,sub_zero,add_zero]
    have hcos := Real.cos_two_mul (θ/2)
    rw [show 2*(θ/2)=θ by ring] at hcos
    rw [Real.cos_sub,Real.cos_pi_div_two,Real.sin_pi_div_two,hcos]
    nlinarith [Real.sin_sq_add_cos_sq (θ/2)]
  · simp only [Complex.sub_im,Complex.one_im,Complex.add_im,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
      mul_zero,zero_mul,add_zero,mul_one,zero_sub]
    have hsin := Real.sin_two_mul (θ/2)
    rw [show 2*(θ/2)=θ by ring] at hsin
    rw [Real.sin_sub,Real.cos_pi_div_two,Real.sin_pi_div_two,hsin]
    ring

theorem half_angle_sine_pos {θ : ℝ} (hθ0 : 0<θ) (hθ2 : θ<2*Real.pi) :
    0<Real.sin (θ/2) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)

theorem norm_one_sub_circle_exp {θ : ℝ} (hθ0 : 0<θ) (hθ2 : θ<2*Real.pi) :
    ‖(1 : ℂ)-Complex.exp ((θ : ℂ)*Complex.I)‖=2*Real.sin (θ/2) := by
  have hsin := half_angle_sine_pos hθ0 hθ2
  rw [one_sub_circle_exp_factor,norm_mul]
  rw [Complex.norm_of_nonneg (by positivity : 0≤2*Real.sin (θ/2))]
  rw [Complex.ofReal_cos,Complex.ofReal_sin,Complex.norm_cos_add_sin_mul_I,mul_one]

theorem circle_exp_ne_one {θ : ℝ} (hθ0 : 0<θ) (hθ2 : θ<2*Real.pi) :
    Complex.exp ((θ : ℂ)*Complex.I)≠1 := by
  intro heq
  have hnorm := norm_one_sub_circle_exp hθ0 hθ2
  rw [heq,sub_self,norm_zero] at hnorm
  have hsin := half_angle_sine_pos hθ0 hθ2
  nlinarith

theorem arg_one_sub_circle_exp {θ : ℝ} (hθ0 : 0<θ) (hθ2 : θ<2*Real.pi) :
    Complex.arg (1-Complex.exp ((θ : ℂ)*Complex.I))=(θ-Real.pi)/2 := by
  have hsin := half_angle_sine_pos hθ0 hθ2
  have hangle : θ/2-Real.pi/2∈Set.Ioc (-Real.pi) Real.pi := by
    constructor <;> linarith [Real.pi_pos]
  rw [one_sub_circle_exp_factor,Complex.ofReal_cos,Complex.ofReal_sin,
    Complex.arg_mul_cos_add_sin_mul_I (mul_pos two_pos hsin) hangle]
  ring

theorem log_one_sub_circle_exp_re {θ : ℝ} (hθ0 : 0<θ) (hθ2 : θ<2*Real.pi) :
    (Complex.log (1-Complex.exp ((θ : ℂ)*Complex.I))).re=
      Real.log (2*Real.sin (θ/2)) := by
  rw [Complex.log_re,norm_one_sub_circle_exp hθ0 hθ2]

theorem log_one_sub_circle_exp_im {θ : ℝ} (hθ0 : 0<θ) (hθ2 : θ<2*Real.pi) :
    (Complex.log (1-Complex.exp ((θ : ℂ)*Complex.I))).im=(θ-Real.pi)/2 := by
  rw [Complex.log_im,arg_one_sub_circle_exp hθ0 hθ2]

theorem literal_principal_log_boundary {θ : ℝ} (hθ0 : 0<θ) (hθ2 : θ<2*Real.pi) :
    Complex.log (1-Complex.exp ((θ : ℂ)*Complex.I))=
      (Real.log (2*Real.sin (θ/2)) : ℂ)+((θ-Real.pi)/2 : ℝ)*Complex.I := by
  apply Complex.ext
  · simpa using log_one_sub_circle_exp_re hθ0 hθ2
  · simpa using log_one_sub_circle_exp_im hθ0 hθ2

end NField.Alignment.CollisionHarmonicLogBoundary

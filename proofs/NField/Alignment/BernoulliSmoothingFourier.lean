/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.BernoulliSymmetricSmoothing
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Absolute Fourier expansion and two coefficient bounds for symmetric smoothing -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.BernoulliSmoothingFourier
open scoped ComplexConjugate
open Complex BernoulliSymmetricSmoothing BernoulliFourierIdentity

def smoothingCoefficient (δ : ℝ) (j : ℤ) : ℂ :=
  -(exp (2*(Real.pi : ℂ)*I*j*δ)-exp (-2*(Real.pi : ℂ)*I*j*δ))/
    (2*(δ : ℂ)*(2*(Real.pi : ℂ)*I*j)^2)

theorem smoothing_hasSum (δ y : ℝ) :
    HasSum (fun j : ℤ => smoothingCoefficient δ j*exp (2*(Real.pi : ℂ)*I*j*y))
      (smoothedSaw δ y : ℂ) := by
  have h := ((bernoulli_two_fourier_positive (y+δ)).sub
    (bernoulli_two_fourier_positive (y-δ))).mul_left (-1/(2*(δ : ℂ)))
  have he : (fun j : ℤ => smoothingCoefficient δ j*exp (2*(Real.pi : ℂ)*I*j*y))=
      (fun j : ℤ => (-1/(2*(δ : ℂ)))*
        (exp (2*(Real.pi : ℂ)*I*j*(y+δ))/(2*(Real.pi : ℂ)*I*j)^2-
          exp (2*(Real.pi : ℂ)*I*j*(y-δ))/(2*(Real.pi : ℂ)*I*j)^2)) := by
    funext j
    unfold smoothingCoefficient
    rw [show 2*(Real.pi : ℂ)*I*j*((y : ℂ)+δ)=
      2*(Real.pi : ℂ)*I*j*y+2*(Real.pi : ℂ)*I*j*δ by ring,
      show 2*(Real.pi : ℂ)*I*j*((y : ℂ)-δ)=
      2*(Real.pi : ℂ)*I*j*y+(-2*(Real.pi : ℂ)*I*j*δ) by ring,
      exp_add,exp_add]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  have hv : (smoothedSaw δ y : ℂ)=(-1/(2*(δ : ℂ)))*
      (-(1/2 : ℂ)*(RealCarrierGridAlias.bernoulliTwo (y+δ) : ℂ)-
        (-(1/2 : ℂ)*(RealCarrierGridAlias.bernoulliTwo (y-δ) : ℂ))) := by
    unfold smoothedSaw
    push_cast
    field_simp
    ring
  rw [he,hv]
  simpa only [Complex.ofReal_add,Complex.ofReal_sub] using h

theorem exponential_norm (t : ℝ) : ‖exp ((t : ℂ)*I)‖=1 := by
  simp [Complex.norm_exp,Complex.mul_re]

theorem exponential_difference_bound (t : ℝ) :
    ‖exp ((t : ℂ)*I)-exp (-(t : ℂ)*I)‖ ≤ 2*|t| := by
  have he : exp ((t : ℂ)*I)-exp (-(t : ℂ)*I)=
      exp (-(t : ℂ)*I)*(exp (I*((2*t : ℝ) : ℂ))-1) := by
    rw [mul_sub,← exp_add]
    push_cast
    rw [show -(t : ℂ)*I+I*(2*(t : ℂ))=(t : ℂ)*I by ring]
    ring
  rw [he,norm_mul,show exp (-(t : ℂ)*I)=exp (((-t : ℝ) : ℂ)*I) by simp,
    exponential_norm,one_mul]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2*t)
  simpa only [Real.norm_eq_abs,abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<2)] using h

theorem coefficient_norm_formula {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    ‖smoothingCoefficient δ (n : ℤ)‖ =
      ‖exp (((2*Real.pi*n*δ : ℝ) : ℂ)*I)-exp (((-2*Real.pi*n*δ : ℝ) : ℂ)*I)‖ /
        (2*δ*(2*Real.pi*n)^2) := by
  unfold smoothingCoefficient
  simp only [Int.cast_natCast,norm_div,norm_neg,norm_mul,norm_pow,Complex.norm_I,
    norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hδ,
    abs_of_pos Real.pi_pos,Complex.norm_natCast,mul_one]
  congr 2
  · congr 2 <;> push_cast <;> ring

theorem coefficient_harmonic_bound {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (hn : 1 ≤ n) :
    ‖smoothingCoefficient δ (n : ℤ)‖ ≤ 1/(n : ℝ) := by
  have hn0 : (0 : ℝ)<n := by exact_mod_cast (by omega : 0<n)
  rw [coefficient_norm_formula hδ]
  have hd : 0 < 2*δ*(2*Real.pi*n)^2 := by positivity
  have he := exponential_difference_bound (2*Real.pi*n*δ)
  have hnneg : 0 ≤ 2*Real.pi*n*δ := by positivity
  simp only [abs_of_nonneg hnneg] at he
  have ha : (((-2*Real.pi*n*δ : ℝ) : ℂ)*I)= -((2*Real.pi*n*δ : ℝ) : ℂ)*I := by
    push_cast
    ring
  rw [ha]
  apply (div_le_iff₀ hd).mpr
  calc
    _ ≤ 2*(2*Real.pi*n*δ) := he
    _ ≤ (1/(n : ℝ))*(2*δ*(2*Real.pi*n)^2) := by
      field_simp
      nlinarith [Real.pi_gt_three]

theorem coefficient_square_bound {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (hn : 1 ≤ n) :
    ‖smoothingCoefficient δ (n : ℤ)‖ ≤ 1/(δ*(n : ℝ)^2) := by
  have hn0 : (0 : ℝ)<n := by exact_mod_cast (by omega : 0<n)
  rw [coefficient_norm_formula hδ]
  have hd : 0 < 2*δ*(2*Real.pi*n)^2 := by positivity
  have he : ‖exp (((2*Real.pi*n*δ : ℝ) : ℂ)*I)-
      exp (((-2*Real.pi*n*δ : ℝ) : ℂ)*I)‖ ≤ 2 := by
    calc
      _ ≤ ‖exp (((2*Real.pi*n*δ : ℝ) : ℂ)*I)‖+
          ‖exp (((-2*Real.pi*n*δ : ℝ) : ℂ)*I)‖ := norm_sub_le _ _
      _ = 2 := by rw [exponential_norm,exponential_norm]; norm_num
  apply (div_le_iff₀ hd).mpr
  calc
    _ ≤ 2 := he
    _ ≤ (1/(δ*(n : ℝ)^2))*(2*δ*(2*Real.pi*n)^2) := by
      field_simp
      nlinarith [Real.pi_gt_three]

end NField.Alignment.BernoulliSmoothingFourier

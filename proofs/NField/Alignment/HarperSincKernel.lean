/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# A normalized positive kernel for the Harper partition

The unit kernel is the square of sinc(pi*x). Its integral is proved by
Fourier inversion of the convolution of two unit-interval indicators.
Scaling gives a nonnegative integral-one kernel with triangular Fourier
transform, exact compact frequency support and quantitative tail mass.
These are ingredients of the partition construction; this module does not
assume or assert the character/random approximation errors.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory Set FourierTransform Convolution

namespace NField.Alignment.HarperSincKernel

def window : ℝ → ℂ := (Icc (-(1/2 : ℝ)) (1/2)).indicator (fun _ => 1)

def tent (x : ℝ) : ℝ := max (1 - |x|) 0

def unitKernel (x : ℝ) : ℝ := Real.sinc (Real.pi*x)^2

theorem integrable_window : Integrable window := by
  change Integrable ((Icc (-(1/2 : ℝ)) (1/2)).indicator (fun _ => (1 : ℂ)))
  rw [integrable_indicator_iff measurableSet_Icc]
  exact integrableOn_const (C := (1 : ℂ)) measure_Icc_lt_top.ne

theorem window_convolution (x : ℝ) :
    (window ⋆[ContinuousLinearMap.mul ℂ ℂ] window) x = (tent x : ℂ) := by
  have hi : (fun t => window t * window (x-t)) =
      (Icc (max (-(1/2 : ℝ)) (x-1/2)) (min (1/2) (x+1/2))).indicator
        (fun _ => (1 : ℂ)) := by
    funext t
    have hm : t ∈ Icc (max (-(1/2 : ℝ)) (x-1/2)) (min (1/2) (x+1/2)) ↔
        t ∈ Icc (-(1/2 : ℝ)) (1/2) ∧ x-t ∈ Icc (-(1/2 : ℝ)) (1/2) := by
      simp only [mem_Icc, max_le_iff, le_min_iff]
      constructor <;> rintro ⟨⟨h1,h2⟩,⟨h3,h4⟩⟩ <;> constructor <;> constructor <;> linarith
    by_cases h1 : t ∈ Icc (-(1/2 : ℝ)) (1/2) <;>
      by_cases h2 : x-t ∈ Icc (-(1/2 : ℝ)) (1/2) <;>
      simp only [window, indicator_apply, hm, h1, h2, and_self, and_false, false_and,
        if_true, if_false, mul_one, mul_zero]
  change (∫ t, window t * window (x-t)) = _
  rw [hi, integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc]
  rw [Complex.real_smul, mul_one]
  congr 1
  unfold tent
  congr 1
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx, max_eq_right (by linarith), min_eq_left (by linarith)]
    ring
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [abs_of_nonpos hx', max_eq_left (by linarith), min_eq_right (by linarith)]
    ring

theorem fourier_window (x : ℝ) : 𝓕 window x = (Real.sinc (Real.pi*x) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hi : (fun v : ℝ => Complex.exp (↑(-2*Real.pi*v*x)*Complex.I) • window v) =
      (Icc (-(1/2 : ℝ)) (1/2)).indicator
        (fun v => Complex.exp (↑(-2*Real.pi*v*x)*Complex.I)) := by
    funext v
    simp only [window, indicator_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [hi, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : -(1/2 : ℝ) ≤ 1/2)]
  by_cases hx : x = 0
  · norm_num [hx]
  have hc : -2*Real.pi*x ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hx
  have he : (fun v : ℝ => Complex.exp (↑(-2*Real.pi*v*x)*Complex.I)) =
      (fun v => Complex.exp (↑((-2*Real.pi*x)*v)*Complex.I)) := by
    ext v
    congr 2
    push_cast
    ring
  rw [he, intervalIntegral.integral_comp_mul_left
    (fun t : ℝ => Complex.exp (t*Complex.I)) hc]
  have hb : (-2*Real.pi*x)*(1/2) = -Real.pi*x := by ring
  have ha : (-2*Real.pi*x)*(-(1/2)) = -(-Real.pi*x) := by ring
  rw [ha, hb, integral_exp_mul_I_eq_sinc]
  rw [show -Real.pi*x = -(Real.pi*x) by ring, Real.sinc_neg]
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_neg]
  norm_num only [Complex.ofReal_ofNat]
  field_simp [hx, Real.pi_ne_zero]

theorem continuous_tent : Continuous tent := by unfold tent; fun_prop

theorem integrable_tent_complex : Integrable (fun x => (tent x : ℂ)) := by
  have h := integrable_window.integrable_convolution
    (L := ContinuousLinearMap.mul ℂ ℂ) integrable_window
  rw [show (window ⋆[ContinuousLinearMap.mul ℂ ℂ] window) =
    (fun t => (tent t : ℂ)) from funext window_convolution] at h
  exact h

theorem fourier_tent (x : ℝ) : 𝓕 (fun t => (tent t : ℂ)) x = (unitKernel x : ℂ) := by
  rw [← show (window ⋆[ContinuousLinearMap.mul ℂ ℂ] window) =
    (fun t => (tent t : ℂ)) from funext window_convolution]
  rw [Real.fourier_mul_convolution_eq integrable_window integrable_window, fourier_window]
  simp [unitKernel, pow_two]

theorem unitKernel_nonneg (x : ℝ) : 0 ≤ unitKernel x := sq_nonneg _

theorem continuous_unitKernel : Continuous unitKernel := by
  exact (Real.continuous_sinc.comp (continuous_const.mul continuous_id)).pow 2

theorem unitKernel_le_one (x : ℝ) : unitKernel x ≤ 1 := by
  have h := Real.abs_sinc_le_one (Real.pi*x)
  unfold unitKernel
  obtain ⟨hlo,hhi⟩ := abs_le.mp h
  nlinarith

theorem unitKernel_sq_mul_le_one (x : ℝ) : x^2*unitKernel x ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  have hpi : 1 ≤ Real.pi^2 := by nlinarith [Real.two_le_pi]
  have hn : 0 ≤ x^2*unitKernel x := mul_nonneg (sq_nonneg _) (unitKernel_nonneg _)
  have he : Real.pi^2*(x^2*unitKernel x) = Real.sin (Real.pi*x)^2 := by
    rw [unitKernel, Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hx)]
    field_simp
  have hs : Real.sin (Real.pi*x)^2 ≤ 1 := by
    have h := Real.abs_sin_le_one (Real.pi*x)
    obtain ⟨hlo,hhi⟩ := abs_le.mp h
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hpi hn]

theorem integrable_unitKernel : Integrable unitKernel := by
  refine (integrable_inv_one_add_sq.const_mul (2 : ℝ)).mono'
    continuous_unitKernel.aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_of_nonneg (unitKernel_nonneg x), ← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 1+x^2)).2
  nlinarith [unitKernel_le_one x, unitKernel_sq_mul_le_one x]

theorem integral_unitKernel : (∫ x, unitKernel x) = 1 := by
  have ht : Continuous (fun x => (tent x : ℂ)) := Complex.continuous_ofReal.comp continuous_tent
  have hk : Integrable (𝓕 (fun x => (tent x : ℂ))) := by
    rw [show 𝓕 (fun x => (tent x : ℂ)) = (fun x => (unitKernel x : ℂ)) from
      funext fourier_tent]
    exact integrable_unitKernel.ofReal
  have h := integrable_tent_complex.fourierInv_fourier_eq hk (ht.continuousAt (x := 0))
  rw [Real.fourierInv_eq'] at h
  simp only [inner_zero_right, mul_zero, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, one_smul] at h
  simp_rw [fourier_tent] at h
  rw [integral_complex_ofReal] at h
  norm_num [tent] at h
  exact_mod_cast h

theorem unitKernel_even (x : ℝ) : unitKernel (-x) = unitKernel x := by
  simp [unitKernel, Real.sinc_neg]

theorem fourier_unitKernel (x : ℝ) :
    𝓕 (fun t => (unitKernel t : ℂ)) x = (tent x : ℂ) := by
  have hf : 𝓕 (fun t => (tent t : ℂ)) = (fun t => (unitKernel t : ℂ)) := funext fourier_tent
  have hfi : 𝓕⁻ (fun t => (tent t : ℂ)) = (fun t => (unitKernel t : ℂ)) := by
    ext t
    rw [Real.fourierInv_eq_fourier_neg, fourier_tent, unitKernel_even]
  have h := integrable_tent_complex.fourier_fourierInv_eq
    (by rw [hf]; exact integrable_unitKernel.ofReal)
    ((Complex.continuous_ofReal.comp continuous_tent).continuousAt (x := x))
  rwa [hfi] at h

def kernel (delta x : ℝ) : ℝ := delta⁻¹ * unitKernel (x/delta)

theorem kernel_nonneg {delta : ℝ} (hd : 0 < delta) (x : ℝ) : 0 ≤ kernel delta x :=
  mul_nonneg (inv_nonneg.mpr hd.le) (unitKernel_nonneg _)

theorem continuous_kernel (delta : ℝ) : Continuous (kernel delta) :=
  continuous_const.mul (continuous_unitKernel.comp (continuous_id.div_const delta))

theorem integrable_kernel {delta : ℝ} (hd : 0 < delta) : Integrable (kernel delta) :=
  (integrable_unitKernel.comp_div hd.ne').const_mul _

theorem integral_kernel {delta : ℝ} (hd : 0 < delta) : (∫ x, kernel delta x) = 1 := by
  change (∫ x, delta⁻¹ * unitKernel (x/delta)) = 1
  rw [integral_const_mul, Measure.integral_comp_div, integral_unitKernel,
    smul_eq_mul, mul_one, abs_of_pos hd, inv_mul_cancel₀ hd.ne']

theorem kernel_even (delta x : ℝ) : kernel delta (-x) = kernel delta x := by
  simp only [kernel, neg_div, unitKernel_even]

theorem kernel_le_inverse {delta : ℝ} (hd : 0 < delta) (x : ℝ) :
    kernel delta x ≤ delta⁻¹ := by
  exact (mul_le_mul_of_nonneg_left (unitKernel_le_one _) (inv_nonneg.mpr hd.le)).trans_eq
    (mul_one _)

theorem kernel_tail_bound {delta x : ℝ} (hd : 0 < delta) (hx : x ≠ 0) :
    kernel delta x ≤ delta / (Real.pi^2*x^2) := by
  have hden : 0 < Real.pi^2*x^2 := mul_pos (sq_pos_of_pos Real.pi_pos) (sq_pos_of_ne_zero hx)
  have he : (Real.pi^2*x^2)*kernel delta x = delta*Real.sin (Real.pi*(x/delta))^2 := by
    rw [kernel, unitKernel, Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero (div_ne_zero hx hd.ne'))]
    field_simp
  have hs : Real.sin (Real.pi*(x/delta))^2 ≤ 1 := by
    obtain ⟨hlo,hhi⟩ := abs_le.mp (Real.abs_sin_le_one (Real.pi*(x/delta)))
    nlinarith
  apply (le_div_iff₀ hden).2
  nlinarith [mul_le_mul_of_nonneg_left hs hd.le]

theorem fourier_kernel {delta : ℝ} (hd : 0 < delta) (x : ℝ) :
    𝓕 (fun t => (kernel delta t : ℂ)) x = (tent (delta*x) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  let f : ℝ → ℂ := fun t => Complex.exp (↑(-2*Real.pi*t*(delta*x))*Complex.I) *
    (unitKernel t : ℂ)
  have he : (fun t : ℝ => Complex.exp (↑(-2*Real.pi*t*x)*Complex.I) •
      (kernel delta t : ℂ)) = (fun t => (delta⁻¹ : ℝ) * f (t/delta)) := by
    funext t
    have hh : -2*Real.pi*(t/delta)*(delta*x) = -2*Real.pi*t*x := by field_simp
    dsimp only [f]
    rw [hh]
    simp only [kernel, Complex.ofReal_mul, smul_eq_mul]
    ring
  rw [he, integral_const_mul, Measure.integral_comp_div, abs_of_pos hd,
    Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hd.ne',
    Complex.ofReal_one, one_mul]
  simpa only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul] using
    fourier_unitKernel (delta*x)

theorem fourier_kernel_support {delta x : ℝ} (hd : 0 < delta) (hx : delta⁻¹ ≤ |x|) :
    𝓕 (fun t => (kernel delta t : ℂ)) x = 0 := by
  rw [fourier_kernel hd]
  have hh : 1 ≤ delta*|x| := by
    have h := mul_le_mul_of_nonneg_left hx hd.le
    rwa [mul_inv_cancel₀ hd.ne'] at h
  simp only [tent, abs_mul, abs_of_pos hd]
  rw [max_eq_right (by linarith), Complex.ofReal_zero]

theorem integral_kernel_Ioi_le {delta a : ℝ} (hd : 0 < delta) (ha : 0 < a) :
    (∫ x in Ioi a, kernel delta x) ≤ delta / (Real.pi^2*a) := by
  have hr := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ha
  have hb : (∫ x in Ioi a, kernel delta x) ≤
      ∫ x in Ioi a, (delta/Real.pi^2) * x^(-2 : ℝ) := by
    apply setIntegral_mono_on (integrable_kernel hd).integrableOn (hr.const_mul _) measurableSet_Ioi
    intro x hx
    have hxp : 0 < x := ha.trans hx
    calc
      _ ≤ delta / (Real.pi^2*x^2) := kernel_tail_bound hd hxp.ne'
      _ = _ := by
        rw [Real.rpow_neg hxp.le, Real.rpow_two]
        field_simp
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ha] at hb
  norm_num only [show (-2 : ℝ)+1 = -1 by norm_num, Real.rpow_neg_one, neg_div_neg_eq,
    div_one] at hb
  convert hb using 1
  field_simp

theorem integral_kernel_Iio_eq_Ioi (delta a : ℝ) :
    (∫ x in Iio (-a), kernel delta x) = ∫ x in Ioi a, kernel delta x := by
  have he : (fun x => (Iio (-a)).indicator (kernel delta) (-x)) =
      (Ioi a).indicator (kernel delta) := by
    ext x
    simp only [indicator_apply, mem_Iio, mem_Ioi, neg_lt_neg_iff, kernel_even]
  have h := integral_neg_eq_self ((Iio (-a)).indicator (kernel delta)) volume
  rw [he, integral_indicator measurableSet_Ioi, integral_indicator measurableSet_Iio] at h
  exact h.symm

theorem integral_kernel_tail_le {delta a : ℝ} (hd : 0 < delta) (ha : 0 < a) :
    (∫ x in {x : ℝ | a < |x|}, kernel delta x) ≤ 2*delta/(Real.pi^2*a) := by
  have hs : {x : ℝ | a < |x|} = Iio (-a) ∪ Ioi a := by
    ext x
    simp only [mem_setOf_eq, mem_union, mem_Iio, mem_Ioi, lt_abs]
    constructor <;> rintro (h | h)
    · exact Or.inr h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
    · exact Or.inl h
  have hj : Disjoint (Iio (-a)) (Ioi a) := by
    apply Set.disjoint_left.2
    intro x hx hy
    change x < -a at hx
    change a < x at hy
    linarith
  rw [hs, setIntegral_union hj measurableSet_Ioi (integrable_kernel hd).integrableOn
    (integrable_kernel hd).integrableOn, integral_kernel_Iio_eq_Ioi]
  have hb := integral_kernel_Ioi_le hd ha
  calc
    _ ≤ delta/(Real.pi^2*a) + delta/(Real.pi^2*a) := add_le_add hb hb
    _ = _ := by ring

theorem integral_kernel_half_tail_le {delta : ℝ} (hd : 0 < delta) :
    (∫ x in {x : ℝ | (1/2 : ℝ) < |x|}, kernel delta x) ≤ delta := by
  have hb := integral_kernel_tail_le hd (by norm_num : (0 : ℝ) < 1/2)
  have hpi : 4 ≤ Real.pi^2 := by nlinarith [Real.two_le_pi]
  refine hb.trans ?_
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < Real.pi^2*(1/2))).2
  nlinarith [mul_le_mul_of_nonneg_left hpi hd.le]

end NField.Alignment.HarperSincKernel

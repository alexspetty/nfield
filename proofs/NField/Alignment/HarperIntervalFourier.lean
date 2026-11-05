/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperIntervalSmoothing
import NField.Alignment.HarperCharacteristicTaylor

/-!
# Compact Fourier representation of every smoothed interval

The Fourier density is the transform of the literal interval indicator
times the triangular kernel multiplier. Its norm is at most the interval
length and its support lies in |xi|<=1/delta. Convolution and inversion
give the exact positive-sign characteristic-function convention, including
empty and zero-length intervals, without an affine rescaling exception.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperIntervalFourier
open scoped Topology
open MeasureTheory Set FourierTransform Convolution HarperSincKernel
  HarperIntervalSmoothing HarperCharacteristicTaylor

def intervalIndicator (a b : ℝ) : ℝ → ℂ := (Icc a b).indicator (fun _ => 1)
def spectralDensity (delta a b xi : ℝ) : ℂ :=
  𝓕 (intervalIndicator a b) xi*(tent (delta*xi) : ℂ)

theorem intervalIndicator_integrable (a b : ℝ) : Integrable (intervalIndicator a b) := by
  change Integrable ((Icc a b).indicator (fun _ => (1 : ℂ)))
  rw [integrable_indicator_iff measurableSet_Icc]
  exact integrableOn_const (C := (1 : ℂ)) measure_Icc_lt_top.ne

theorem intervalIndicator_norm_integral (a b : ℝ) :
    (∫ z, ‖intervalIndicator a b z‖) = max (b-a) 0 := by
  have he : (fun z => ‖intervalIndicator a b z‖) = (Icc a b).indicator (fun _ => (1 : ℝ)) := by
    funext z
    simp only [intervalIndicator, indicator_apply]
    split_ifs <;> simp
  rw [he, integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc, smul_eq_mul, mul_one]

theorem intervalIndicator_fourier_norm (a b xi : ℝ) :
    ‖𝓕 (intervalIndicator a b) xi‖ ≤ max (b-a) 0 := by
  rw [Real.fourier_eq]
  apply (norm_integral_le_integral_norm _).trans
  simp only [Circle.norm_smul]
  exact (intervalIndicator_norm_integral a b).le

theorem intervalWindow_convolution (delta a b z : ℝ) :
    (intervalIndicator a b ⋆[ContinuousLinearMap.mul ℂ ℂ]
      (fun y => (kernel delta y : ℂ))) z = (intervalWindow delta a b z : ℂ) := by
  classical
  change (∫ u, intervalIndicator a b u*(kernel delta (z-u) : ℂ)) = _
  have he : (fun u => intervalIndicator a b u*(kernel delta (z-u) : ℂ)) =
      (Icc a b).indicator (fun u => (kernel delta (u-z) : ℂ)) := by
    funext u
    simp only [intervalIndicator, indicator_apply]
    have hk : kernel delta (z-u) = kernel delta (u-z) := by
      simpa only [neg_sub] using kernel_even delta (u-z)
    split_ifs <;> simp [hk]
  rw [he, integral_indicator measurableSet_Icc]
  by_cases hab : a ≤ b
  · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
      intervalIntegral.integral_comp_sub_right (fun y => (kernel delta y : ℂ)) z,
      intervalIntegral.integral_of_le (sub_le_sub_right hab z),
      ← integral_Icc_eq_integral_Ioc, integral_complex_ofReal]
    rfl
  · rw [Icc_eq_empty_of_lt (lt_of_not_ge hab), setIntegral_empty,
      intervalWindow_empty delta (lt_of_not_ge hab)]
    simp

theorem intervalWindow_complex_integrable {delta : ℝ} (hd : 0 < delta) (a b : ℝ) :
    Integrable (fun z => (intervalWindow delta a b z : ℂ)) := by
  have hk : Integrable (fun y => (kernel delta y : ℂ)) := (integrable_kernel hd).ofReal
  have hi := (intervalIndicator_integrable a b).integrable_convolution
    (L := ContinuousLinearMap.mul ℂ ℂ) hk
  rw [show (intervalIndicator a b ⋆[ContinuousLinearMap.mul ℂ ℂ]
    (fun y => (kernel delta y : ℂ))) = (fun z => (intervalWindow delta a b z : ℂ))
    from funext (intervalWindow_convolution delta a b)] at hi
  exact hi

theorem intervalWindow_complex_continuous {delta : ℝ} (hd : 0 < delta) (a b : ℝ) :
    Continuous (fun z => (intervalWindow delta a b z : ℂ)) := by
  have hb : BddAbove (Set.range (fun y => ‖(kernel delta y : ℂ)‖)) := by
    refine ⟨delta⁻¹, ?_⟩
    rintro v ⟨y,rfl⟩
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg hd y)] using
      kernel_le_inverse hd y
  have hc := hb.continuous_convolution_right_of_integrable (ContinuousLinearMap.mul ℂ ℂ)
    (intervalIndicator_integrable a b) (Complex.continuous_ofReal.comp (continuous_kernel delta))
  rw [show (intervalIndicator a b ⋆[ContinuousLinearMap.mul ℂ ℂ]
    (fun y => (kernel delta y : ℂ))) = (fun z => (intervalWindow delta a b z : ℂ))
    from funext (intervalWindow_convolution delta a b)] at hc
  exact hc

theorem intervalWindow_fourier {delta : ℝ} (hd : 0 < delta) (a b xi : ℝ) :
    𝓕 (fun z => (intervalWindow delta a b z : ℂ)) xi = spectralDensity delta a b xi := by
  have hk : Integrable (fun y => (kernel delta y : ℂ)) := (integrable_kernel hd).ofReal
  rw [← show (intervalIndicator a b ⋆[ContinuousLinearMap.mul ℂ ℂ]
    (fun y => (kernel delta y : ℂ))) = (fun z => (intervalWindow delta a b z : ℂ))
    from funext (intervalWindow_convolution delta a b)]
  rw [Real.fourier_mul_convolution_eq (intervalIndicator_integrable a b) hk,
    fourier_kernel hd]
  rfl

theorem spectralDensity_continuous (delta a b : ℝ) : Continuous (spectralDensity delta a b) := by
  have hf : Continuous (𝓕 (intervalIndicator a b)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ (intervalIndicator_integrable a b)
  exact hf.mul (Complex.continuous_ofReal.comp
    (continuous_tent.comp (continuous_const.mul continuous_id)))

theorem spectralDensity_norm (delta a b xi : ℝ) :
    ‖spectralDensity delta a b xi‖ ≤ max (b-a) 0 := by
  have hn : 0 ≤ tent (delta*xi) := le_max_right _ _
  have ht : tent (delta*xi) ≤ 1 := max_le (by linarith [abs_nonneg (delta*xi)]) zero_le_one
  rw [spectralDensity, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn]
  exact (mul_le_mul (intervalIndicator_fourier_norm a b xi) ht hn (le_max_right _ _)).trans_eq
    (mul_one _)

theorem spectralDensity_zero_of_outside {delta : ℝ} (hd : 0 < delta) (a b : ℝ)
    {xi : ℝ} (hxi : delta⁻¹ ≤ |xi|) : spectralDensity delta a b xi = 0 := by
  have he := fourier_kernel_support hd hxi
  rw [fourier_kernel hd] at he
  simp only [spectralDensity, he, mul_zero]

theorem spectralDensity_compactSupport {delta : ℝ} (hd : 0 < delta) (a b : ℝ) :
    HasCompactSupport (spectralDensity delta a b) := by
  apply HasCompactSupport.intro' (K := Icc (-delta⁻¹) delta⁻¹) isCompact_Icc isClosed_Icc
  intro xi hxi
  apply spectralDensity_zero_of_outside hd a b
  by_contra h
  exact hxi (abs_le.mp (le_of_lt (lt_of_not_ge h)))

theorem spectralDensity_integrable {delta : ℝ} (hd : 0 < delta) (a b : ℝ) :
    Integrable (spectralDensity delta a b) :=
  (spectralDensity_continuous delta a b).integrable_of_hasCompactSupport
    (spectralDensity_compactSupport hd a b)

theorem intervalWindow_fourier_representation {delta : ℝ} (hd : 0 < delta) (a b z : ℝ) :
    (intervalWindow delta a b z : ℂ) =
      ∫ xi, phaseExponential (2*Real.pi*xi) z*spectralDensity delta a b xi := by
  have hf : 𝓕 (fun z => (intervalWindow delta a b z : ℂ)) = spectralDensity delta a b :=
    funext (intervalWindow_fourier hd a b)
  have h := (intervalWindow_complex_integrable hd a b).fourierInv_fourier_eq
    (by rw [hf]; exact spectralDensity_integrable hd a b)
    ((intervalWindow_complex_continuous hd a b).continuousAt (x := z))
  simp only [hf, Real.fourierInv_eq', RCLike.inner_apply,
    RCLike.conj_to_real, mul_assoc, smul_eq_mul] at h
  convert h.symm using 1
  apply integral_congr_ae
  filter_upwards [] with xi
  unfold phaseExponential
  congr 3
  ring_nf

end NField.Alignment.HarperIntervalFourier

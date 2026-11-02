/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperPartition
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Fourier representation of the actual partition cell

The frequency density is computed from the constructed interval convolution.
Its compact support and bound supply integrable moments at every order.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory Set FourierTransform Convolution

namespace NField.Alignment.HarperPartitionFourier

open HarperSincKernel HarperPartition

def density (delta t : ℝ) : ℂ :=
  (Real.sinc (Real.pi*t) * tent (delta*t) : ℝ)

theorem cell_convolution (delta x : ℝ) :
    (window ⋆[ContinuousLinearMap.mul ℂ ℂ] (fun t => (kernel delta t : ℂ))) x =
      (cell delta x : ℂ) := by
  change (∫ u, window u * (kernel delta (x-u) : ℂ)) = _
  have he : (fun u => window u * (kernel delta (x-u) : ℂ)) =
      (Icc (-(1/2 : ℝ)) (1/2)).indicator (fun u => (kernel delta (x-u) : ℂ)) := by
    ext u
    simp only [window, indicator_apply]
    split_ifs <;> simp
  rw [he, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : -(1/2 : ℝ) ≤ 1/2),
    intervalIntegral.integral_comp_sub_left (fun u => (kernel delta u : ℂ)) x,
    intervalIntegral.integral_ofReal]
  simp only [sub_neg_eq_add, cell]

theorem integrable_cell_complex {delta : ℝ} (hd : 0 < delta) :
    Integrable (fun x => (cell delta x : ℂ)) := by
  have h := integrable_window.integrable_convolution (L := ContinuousLinearMap.mul ℂ ℂ)
    ((integrable_kernel hd).ofReal : Integrable (fun t => (kernel delta t : ℂ)))
  rw [show (window ⋆[ContinuousLinearMap.mul ℂ ℂ] (fun t => (kernel delta t : ℂ))) =
    (fun x => (cell delta x : ℂ)) from funext (cell_convolution delta)] at h
  exact h

theorem continuous_cell_complex {delta : ℝ} (hd : 0 < delta) :
    Continuous (fun x => (cell delta x : ℂ)) := by
  have hb : BddAbove (Set.range (fun t => ‖(kernel delta t : ℂ)‖)) := by
    refine ⟨delta⁻¹, ?_⟩
    rintro y ⟨t,rfl⟩
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg hd t)] using
      kernel_le_inverse hd t
  have hc := hb.continuous_convolution_right_of_integrable (ContinuousLinearMap.mul ℂ ℂ)
    integrable_window (Complex.continuous_ofReal.comp (continuous_kernel delta))
  rw [show (window ⋆[ContinuousLinearMap.mul ℂ ℂ] (fun t => (kernel delta t : ℂ))) =
    (fun x => (cell delta x : ℂ)) from funext (cell_convolution delta)] at hc
  exact hc

theorem fourier_cell {delta : ℝ} (hd : 0 < delta) (t : ℝ) :
    𝓕 (fun x => (cell delta x : ℂ)) t = density delta t := by
  have hk : Integrable (fun t => (kernel delta t : ℂ)) := (integrable_kernel hd).ofReal
  rw [← show (window ⋆[ContinuousLinearMap.mul ℂ ℂ] (fun t => (kernel delta t : ℂ))) =
    (fun x => (cell delta x : ℂ)) from funext (cell_convolution delta)]
  rw [Real.fourier_mul_convolution_eq integrable_window hk,
    fourier_window, fourier_kernel hd]
  simp only [density, Complex.ofReal_mul]

theorem continuous_density (delta : ℝ) : Continuous (density delta) :=
  Complex.continuous_ofReal.comp
    ((Real.continuous_sinc.comp (continuous_const.mul continuous_id)).mul
      (continuous_tent.comp (continuous_const.mul continuous_id)))

theorem density_even (delta t : ℝ) : density delta (-t) = density delta t := by
  simp [density, tent, Real.sinc_neg]

theorem density_norm_le_one (delta t : ℝ) : ‖density delta t‖ ≤ 1 := by
  have htn : 0 ≤ tent (delta*t) := le_max_right _ _
  have htu : tent (delta*t) ≤ 1 := by unfold tent; exact max_le (by linarith [abs_nonneg (delta*t)]) zero_le_one
  simp only [density, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg htn]
  exact mul_le_one₀ (Real.abs_sinc_le_one _) htn htu

theorem density_zero_of_outside {delta t : ℝ} (hd : 0 < delta) (ht : delta⁻¹ ≤ |t|) :
    density delta t = 0 := by
  have h := fourier_kernel_support hd ht
  rw [fourier_kernel hd] at h
  simp only [density, Complex.ofReal_mul, h, mul_zero]

theorem density_compactSupport {delta : ℝ} (hd : 0 < delta) : HasCompactSupport (density delta) := by
  apply HasCompactSupport.intro' (K := Icc (-delta⁻¹) delta⁻¹) isCompact_Icc isClosed_Icc
  intro t ht
  apply density_zero_of_outside hd
  by_contra h
  exact ht (abs_le.mp (le_of_lt (lt_of_not_ge h)))

theorem integrable_density {delta : ℝ} (hd : 0 < delta) : Integrable (density delta) :=
  (continuous_density delta).integrable_of_hasCompactSupport (density_compactSupport hd)

theorem integrable_density_moment {delta : ℝ} (hd : 0 < delta) (n : ℕ) :
    Integrable (fun t : ℝ => t^n • density delta t) := by
  apply ((continuous_id.pow n).smul (continuous_density delta)).integrable_of_hasCompactSupport
  exact (density_compactSupport hd).smul_left

theorem fourier_density {delta : ℝ} (hd : 0 < delta) :
    𝓕 (density delta) = (fun x => (cell delta x : ℂ)) := by
  have hf : 𝓕 (fun x => (cell delta x : ℂ)) = density delta := funext (fourier_cell hd)
  have h := (continuous_cell_complex hd).fourierInv_fourier_eq (integrable_cell_complex hd)
    (by rw [hf]; exact integrable_density hd)
  rw [hf, Real.fourierInv_eq_fourier_comp_neg] at h
  simpa only [density_even] using h

theorem contDiff_cell_complex {delta : ℝ} (hd : 0 < delta) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => (cell delta x : ℂ)) := by
  rw [← fourier_density hd]
  apply Real.contDiff_fourier
  intro n _
  simpa only [norm_smul, Real.norm_eq_abs, norm_pow] using (integrable_density_moment hd n).norm

theorem contDiff_cell {delta : ℝ} (hd : 0 < delta) : ContDiff ℝ (⊤ : ℕ∞) (cell delta) := by
  simpa only [Function.comp_def, Complex.reCLM_apply, Complex.ofReal_re] using
    Complex.reCLM.contDiff.comp (contDiff_cell_complex hd)

theorem cell_iteratedDeriv_fourier {delta : ℝ} (hd : 0 < delta) (n : ℕ) :
    iteratedDeriv n (fun x => (cell delta x : ℂ)) =
      𝓕 (fun t : ℝ => (-2*Real.pi*Complex.I*t)^n • density delta t) := by
  rw [← fourier_density hd]
  exact Real.iteratedDeriv_fourier (N := ⊤) (fun m _ => integrable_density_moment hd m) le_top

theorem cell_iteratedDeriv_norm {delta : ℝ} (hd : 0 < delta) (n : ℕ) (x : ℝ) :
    ‖iteratedDeriv n (fun x => (cell delta x : ℂ)) x‖ = |iteratedDeriv n (cell delta) x| := by
  have h := Complex.ofRealLI.norm_iteratedFDeriv_comp_left (n := (⊤ : ℕ∞))
    ((contDiff_cell hd).contDiffAt (x := x)) (i := n)
    (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
    Function.comp_def, Complex.ofRealLI_apply] using h

end NField.Alignment.HarperPartitionFourier

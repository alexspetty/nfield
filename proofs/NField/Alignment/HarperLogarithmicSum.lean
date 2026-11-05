/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperEulerIntegral
import NField.Alignment.HarperMainIntegral
import Mathlib.Analysis.MellinInversion
import Mathlib.MeasureTheory.Function.L2Space
import NField.Alignment.DirichletParseval

/-!
# The Fourier transform of the logarithmic smooth sum

The Rankin bound proves L1 and L2 integrability for every positive real
part. Mellin substitution identifies the concrete Fourier transform with
the actual random Euler product divided by its complex argument. Its L2
integrability follows from the previously proved Cauchy majorant. Applying
Plancherel gives the full spectral integral with the exact 1/(2*pi) factor.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperLogarithmicSum

open MeasureTheory Set SteinhausMoment HarperRandomEulerProduct HarperEulerIntegral
  HarperSmoothIntervals HarperSmoothCount HarperMainIntegral
open scoped FourierTransform

def logarithmicSum (P sigma : ℝ) (ω : PhaseSpace) (u : ℝ) : ℂ :=
  Real.exp (sigma*u) • smoothSum (Real.exp (-u)) P (fun n => steinhaus n ω)

theorem logarithmicSum_measurable (P sigma : ℝ) (ω : PhaseSpace) :
    Measurable (logarithmicSum P sigma ω) :=
  (measurable_const.mul measurable_id).exp.smul
    ((smoothSum_measurable P _).comp measurable_neg.exp)

theorem logarithmicSum_zero (P sigma : ℝ) (ω : PhaseSpace) {u : ℝ} (hu : 0 < u) :
    logarithmicSum P sigma ω u = 0 := by
  rw [logarithmicSum, smoothSum_zero_of_lt_one (Real.exp_lt_one_iff.mpr (by linarith)),
    smul_zero]

theorem logarithmicSum_norm_bound (P : ℝ) {sigma : ℝ} (hs : 0 < sigma)
    (ω : PhaseSpace) (u : ℝ) :
    ‖logarithmicSum P sigma ω u‖ ≤
      shiftedProduct P (sigma/2) * Real.exp ((sigma/2)*u) := by
  have h := smoothSum_rankin_bound (Real.exp_pos (-u)) P (half_pos hs) ω
  rw [logarithmicSum, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc
    _ ≤ Real.exp (sigma*u) * ((Real.exp (-u))^(sigma/2) * shiftedProduct P (sigma/2)) :=
      mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = _ := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      rw [← mul_assoc, ← Real.exp_add]
      rw [mul_comm]
      congr 2
      ring

theorem logarithmicSum_integrable (P : ℝ) {sigma : ℝ} (hs : 0 < sigma)
    (ω : PhaseSpace) : Integrable (logarithmicSum P sigma ω) := by
  have hb : Integrable ((Iic (0 : ℝ)).indicator
      (fun u => shiftedProduct P (sigma/2) * Real.exp ((sigma/2)*u))) :=
    (integrable_indicator_iff measurableSet_Iic).mpr
      ((integrableOn_exp_mul_Iic (half_pos hs) 0).const_mul _)
  apply hb.mono' (logarithmicSum_measurable P sigma ω).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro u
  by_cases hu : u ≤ 0
  · rw [Set.indicator_of_mem (show u ∈ Iic (0 : ℝ) from hu)]
    exact logarithmicSum_norm_bound P hs ω u
  · rw [Set.indicator_of_notMem (show u ∉ Iic (0 : ℝ) from hu),
      logarithmicSum_zero P sigma ω (lt_of_not_ge hu), norm_zero]

theorem logarithmicSum_sq_bound (P : ℝ) {sigma : ℝ} (hs : 0 < sigma)
    (ω : PhaseSpace) (u : ℝ) :
    ‖logarithmicSum P sigma ω u‖^2 ≤
      (shiftedProduct P (sigma/2))^2 * Real.exp (sigma*u) := by
  calc
    _ ≤ (shiftedProduct P (sigma/2) * Real.exp ((sigma/2)*u))^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (logarithmicSum_norm_bound P hs ω u) 2
    _ = _ := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      norm_num
      ring

theorem logarithmicSum_memLp (P : ℝ) {sigma : ℝ} (hs : 0 < sigma)
    (ω : PhaseSpace) : MemLp (logarithmicSum P sigma ω) 2 := by
  apply (memLp_two_iff_integrable_sq_norm
    (logarithmicSum_measurable P sigma ω).aestronglyMeasurable).mpr
  have hb : Integrable ((Iic (0 : ℝ)).indicator
      (fun u => (shiftedProduct P (sigma/2))^2 * Real.exp (sigma*u))) :=
    (integrable_indicator_iff measurableSet_Iic).mpr
      ((integrableOn_exp_mul_Iic hs 0).const_mul _)
  apply hb.mono'
    ((logarithmicSum_measurable P sigma ω).norm.pow_const 2).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro u
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  by_cases hu : u ≤ 0
  · rw [Set.indicator_of_mem (show u ∈ Iic (0 : ℝ) from hu)]
    exact logarithmicSum_sq_bound P hs ω u
  · rw [Set.indicator_of_notMem (show u ∉ Iic (0 : ℝ) from hu),
      logarithmicSum_zero P sigma ω (lt_of_not_ge hu), norm_zero,
      zero_pow (by decide : 2 ≠ 0)]

theorem mellin_smoothSum (P : ℝ) {s : ℂ} (hs : 0 < s.re) (ω : PhaseSpace) :
    mellin (fun t => smoothSum t P (fun n => steinhaus n ω)) (-s) =
      eulerProduct P s ω / s := by
  have he : mellin (fun t => smoothSum t P (fun n => steinhaus n ω)) (-s) =
      ∫ t in Ioi (1 : ℝ), smoothSum t P (fun n => steinhaus n ω) *
        (t : ℂ)^(-(s+1)) := by
    unfold mellin
    rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards [Measure.ae_ne volume (1 : ℝ)] with t ht
    by_cases ht1 : 1 < t
    · rw [Set.indicator_of_mem (show t ∈ Ioi (0 : ℝ) from lt_trans zero_lt_one ht1),
        Set.indicator_of_mem (show t ∈ Ioi (1 : ℝ) from ht1), smul_eq_mul, mul_comm]
      congr 2
      ring
    · have htlt : t < 1 := lt_of_le_of_ne (le_of_not_gt ht1) ht
      rw [Set.indicator_of_notMem (show t ∉ Ioi (1 : ℝ) from ht1)]
      by_cases ht0 : 0 < t
      · rw [Set.indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht0),
          smoothSum_zero_of_lt_one htlt, smul_zero]
      · rw [Set.indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from ht0)]
  rw [he, eulerProduct_integral P hs ω]
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  field_simp

theorem logarithmicSum_fourier (P : ℝ) {sigma : ℝ} (hs : 0 < sigma)
    (ω : PhaseSpace) (xi : ℝ) :
    (𝓕 (logarithmicSum P sigma ω)) xi =
      eulerProduct P (linePoint sigma (-2*Real.pi*xi)) ω /
        linePoint sigma (-2*Real.pi*xi) := by
  have h := mellin_smoothSum P (s := linePoint sigma (-2*Real.pi*xi))
    (by rwa [linePoint_re]) ω
  rw [mellin_eq_fourier] at h
  have hi : (-(linePoint sigma (-2*Real.pi*xi))).im / (2*Real.pi) = xi := by
    simp [linePoint, Real.pi_ne_zero]
  unfold logarithmicSum
  simpa only [Complex.neg_re, linePoint_re, neg_neg, hi] using! h

theorem logarithmicSum_fourier_norm_sq (P : ℝ) {sigma : ℝ} (hs : 0 < sigma)
    (ω : PhaseSpace) (xi : ℝ) :
    ‖(𝓕 (logarithmicSum P sigma ω)) xi‖^2 =
      spectralDensity P sigma (-2*Real.pi*xi,ω) := by
  rw [logarithmicSum_fourier P hs ω xi, norm_div, div_pow, spectralDensity_eq]

theorem logarithmicSum_fourier_continuous (P : ℝ) {sigma : ℝ} (hs : 0 < sigma)
    (ω : PhaseSpace) : Continuous (𝓕 (logarithmicSum P sigma ω)) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ (logarithmicSum_integrable P hs ω)

theorem logarithmicSum_fourier_memLp (P : ℝ) {sigma : ℝ} (hs : 0 < sigma)
    (ω : PhaseSpace) : MemLp (𝓕 (logarithmicSum P sigma ω)) 2 := by
  apply (memLp_two_iff_integrable_sq_norm
    (logarithmicSum_fourier_continuous P hs ω).aestronglyMeasurable).mpr
  simp_rw [logarithmicSum_fourier_norm_sq P hs ω]
  exact (spectralDensity_integrable_line P hs ω).comp_mul_left'
    (by positivity : (-2*Real.pi) ≠ 0)

theorem logarithmicSum_parseval (P : ℝ) {sigma : ℝ} (hs : 0 < sigma)
    (ω : PhaseSpace) :
    (∫ u : ℝ, ‖logarithmicSum P sigma ω u‖^2) =
      (1/(2*Real.pi)) * spectralIntegral P sigma ω := by
  rw [← DirichletParseval.integral_norm_sq_fourier (logarithmicSum_integrable P hs ω)
    (logarithmicSum_memLp P hs ω) (logarithmicSum_fourier_memLp P hs ω)]
  simp_rw [logarithmicSum_fourier_norm_sq P hs ω]
  simpa [spectralIntegral, abs_mul, abs_inv, abs_of_pos Real.pi_pos, mul_inv_rev, mul_comm] using
    Measure.integral_comp_mul_left (fun t => spectralDensity P sigma (t,ω)) (-2*Real.pi)

end NField.Alignment.HarperLogarithmicSum

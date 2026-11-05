/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperIntervalProbability
import NField.Alignment.HarperGaussianSmoothingScales
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Gaussian interval comparison with an explicit smoothing error

Variance at least one quarter makes the normal density at most one.
The general two-sided interval comparison is specialized to that actual
normal law. The Fourier and tail scales retain all constants and the
2*pi convention. A characteristic-function comparison is still required.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperGaussianInterval
open scoped Topology NNReal
open MeasureTheory ProbabilityTheory Set HarperIntervalSmoothing HarperIntervalProbability
  HarperGaussianSmoothingScales HarperWeightedCharacteristic

theorem gaussianPDF_le_one (m : ℝ) {v : ℝ≥0} (hv : (1/4 : ℝ) ≤ v) (z : ℝ) :
    gaussianPDFReal m v z ≤ 1 := by
  have hv0 : 0 < (v : ℝ) := by linarith
  have hden : 1 ≤ 2*Real.pi*v := by nlinarith [Real.two_le_pi]
  have hs : 1 ≤ Real.sqrt (2*Real.pi*v) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hden
  have hi : (Real.sqrt (2*Real.pi*v))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs
  have he : Real.exp (-(z-m)^2/(2*v)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _))
      (by positivity))
  exact mul_le_one₀ hi (Real.exp_nonneg _) he

theorem gaussian_interval_mass (m : ℝ) {v : ℝ≥0} (hv : (1/4 : ℝ) ≤ v) (a b : ℝ) :
    (gaussianReal m v).real (Icc a b) ≤ max (b-a) 0 := by
  have hvne : v ≠ 0 := by intro he; rw [he] at hv; norm_num at hv
  rw [measureReal_def, gaussianReal_apply_eq_integral m hvne,
    ENNReal.toReal_ofReal (integral_nonneg (gaussianPDFReal_nonneg m v))]
  calc
    _ ≤ ∫ _ in Icc a b, (1 : ℝ) := integral_mono
      (integrable_gaussianPDFReal m v).integrableOn (integrableOn_const measure_Icc_lt_top.ne)
      (gaussianPDF_le_one m hv)
    _ = _ := by rw [setIntegral_const, Real.volume_real_Icc, smul_eq_mul, mul_one]

theorem gaussian_interval_comparison (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (m : ℝ) {v : ℝ≥0} (hv : (1/4 : ℝ) ≤ v)
    {delta h E : ℝ} (hd : 0 < delta) (hh : 0 < h) (hE : 0 ≤ E)
    (hcf : ∀ u : ℝ, |u| ≤ 2*Real.pi*delta⁻¹ →
      ‖charFun μ u-charFun (gaussianReal m v) u‖ ≤ E) (a b : ℝ) :
    |μ.real (Icc a b)-(gaussianReal m v).real (Icc a b)| ≤
      2*max (b-a+2*h) 0*delta⁻¹*E+4*h+2*tailAllowance delta h := by
  simpa only [mul_one, one_mul] using interval_probability_comparison μ (gaussianReal m v)
    hd hh hE (M := 1) (fun c d => by simpa only [one_mul] using gaussian_interval_mass m hv c d)
    hcf a b

def intervalComparisonConstant : ℝ :=
  24*comparisonConstant/Real.pi+(4+4/Real.pi^2)*Real.sqrt (2*Real.pi)

theorem intervalComparisonConstant_pos : 0 < intervalComparisonConstant := by
  unfold intervalComparisonConstant
  have hc := comparisonConstant_pos
  positivity

theorem smoothingWidth_frequency (X : ℝ) :
    2*Real.pi*(smoothingWidth X)⁻¹ = frequencyCutoff X := by
  rw [smoothingWidth]
  field_simp

theorem gaussian_smoothing_error_scale {X : ℝ} (hX : 1 ≤ X)
    (hd : smoothingWidth X ≤ 1) {a b : ℝ} (hab : b-a ≤ 1) :
    2*max (b-a+2*Real.sqrt (smoothingWidth X)) 0*(smoothingWidth X)⁻¹*
        (4*comparisonConstant*(frequencyCutoff X+(frequencyCutoff X)^3)*
          (X^(1/Real.exp 1))^(-(1/2 : ℝ)))+
      4*Real.sqrt (smoothingWidth X)+
        2*tailAllowance (smoothingWidth X) (Real.sqrt (smoothingWidth X)) ≤
      intervalComparisonConstant*X^(-(1/60 : ℝ)) := by
  have hX0 : 0 < X := by linarith
  have hT := frequencyCutoff_pos hX0
  have hC := comparisonConstant_pos
  have hd0 : 0 < smoothingWidth X := div_pos (by positivity) hT
  have hs0 := Real.sqrt_pos.mpr hd0
  have hs1 : Real.sqrt (smoothingWidth X) ≤ 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hd
  have hlen : max (b-a+2*Real.sqrt (smoothingWidth X)) 0 ≤ 3 :=
    max_le (by linarith) (by norm_num)
  have hY0 : 0 < X^(1/Real.exp 1) := Real.rpow_pos_of_pos hX0 _
  have hlead : 2*max (b-a+2*Real.sqrt (smoothingWidth X)) 0*(smoothingWidth X)⁻¹*
      (4*comparisonConstant*(frequencyCutoff X+(frequencyCutoff X)^3)*
        (X^(1/Real.exp 1))^(-(1/2 : ℝ))) ≤
      (24*comparisonConstant/Real.pi)*X^(-(1/30 : ℝ)) := by
    calc
      _ ≤ 2*3*(smoothingWidth X)⁻¹*
          (4*comparisonConstant*(frequencyCutoff X+(frequencyCutoff X)^3)*
            (X^(1/Real.exp 1))^(-(1/2 : ℝ))) := by
        gcongr
      _ = (12*comparisonConstant/Real.pi)*
          (((frequencyCutoff X)^2+(frequencyCutoff X)^4)/Real.sqrt (X^(1/Real.exp 1))) := by
        rw [smoothingWidth, Real.rpow_neg hY0.le, ← Real.sqrt_eq_rpow]
        field_simp
        ring
      _ ≤ (12*comparisonConstant/Real.pi)*(2*X^(-(1/30 : ℝ))) :=
        mul_le_mul_of_nonneg_left (integrated_cutoff_scale hX)
          (by positivity)
      _ = _ := by ring
  have ht : tailAllowance (smoothingWidth X) (Real.sqrt (smoothingWidth X)) =
      2/Real.pi^2*Real.sqrt (smoothingWidth X) := by
    unfold tailAllowance
    calc
      _ = (2*(Real.sqrt (smoothingWidth X))^2)/
          (Real.pi^2*Real.sqrt (smoothingWidth X)) := by rw [Real.sq_sqrt hd0.le]
      _ = _ := by field_simp
  rw [ht]
  have hpow : X^(-(1/30 : ℝ)) ≤ X^(-(1/60 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hX (by norm_num)
  have hlead' := hlead.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
  calc
    _ ≤ (24*comparisonConstant/Real.pi)*X^(-(1/60 : ℝ))+
        4*Real.sqrt (smoothingWidth X)+2*(2/Real.pi^2*Real.sqrt (smoothingWidth X)) :=
      add_le_add (add_le_add hlead' le_rfl) le_rfl
    _ = _ := by
      rw [smoothingWidth_sqrt hX0.le]
      unfold intervalComparisonConstant
      ring

theorem gaussian_interval_rate (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (m : ℝ) {v : ℝ≥0} (hv : (1/4 : ℝ) ≤ v)
    {X : ℝ} (hX : 1 ≤ X) (hd : smoothingWidth X ≤ 1)
    (hcf : ∀ u : ℝ, |u| ≤ frequencyCutoff X →
      ‖charFun μ u-charFun (gaussianReal m v) u‖ ≤
        4*comparisonConstant*(frequencyCutoff X+(frequencyCutoff X)^3)*
          (X^(1/Real.exp 1))^(-(1/2 : ℝ)))
    (a b : ℝ) (hab : b-a ≤ 1) :
    |μ.real (Icc a b)-(gaussianReal m v).real (Icc a b)| ≤
      intervalComparisonConstant*X^(-(1/60 : ℝ)) := by
  have hT := frequencyCutoff_pos (show 0 < X by linarith)
  have hd0 : 0 < smoothingWidth X := div_pos (by positivity) hT
  have hC := comparisonConstant_pos
  have hb := gaussian_interval_comparison μ m hv hd0 (Real.sqrt_pos.mpr hd0)
    (by positivity : 0 ≤ 4*comparisonConstant*(frequencyCutoff X+(frequencyCutoff X)^3)*
      (X^(1/Real.exp 1))^(-(1/2 : ℝ)))
    (fun u hu => hcf u (by rwa [smoothingWidth_frequency] at hu)) a b
  exact hb.trans (gaussian_smoothing_error_scale hX hd hab)

end NField.Alignment.HarperGaussianInterval

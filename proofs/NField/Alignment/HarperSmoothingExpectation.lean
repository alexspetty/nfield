/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperIntervalFourier
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Probability expectations of the exact interval smoothing

Product integrability justifies Fubini for every probability law. The
expectation is the compact Fourier integral of the actual characteristic
function. A uniform characteristic error on its support gives an explicit
smoothed-expectation error. Both probability sandwiches are also proved;
the comparison law's boundary-strip control is still a separate input.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperSmoothingExpectation
open scoped Topology
open MeasureTheory Set Filter HarperIntervalSmoothing HarperIntervalFourier
  HarperCharacteristicTaylor

theorem spectralPhase_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {delta : ℝ} (hd : 0 < delta) (a b : ℝ) :
    Integrable (fun p : ℝ × ℝ => phaseExponential (2*Real.pi*p.2) p.1*
      spectralDensity delta a b p.2) (μ.prod volume) := by
  have hm : Measurable (fun p : ℝ × ℝ => phaseExponential (2*Real.pi*p.2) p.1*
      spectralDensity delta a b p.2) := by
    unfold phaseExponential
    have hp : Measurable (fun p : ℝ × ℝ =>
        Complex.exp (((2*Real.pi*p.2)*p.1 : ℝ)*Complex.I)) := by fun_prop
    exact hp.mul ((spectralDensity_continuous delta a b).measurable.comp measurable_snd)
  apply ((integrable_const (1 : ℝ) : Integrable (fun _ : ℝ => (1 : ℝ)) μ).mul_prod
    (spectralDensity_integrable hd a b).norm).mono' hm.aestronglyMeasurable
  exact Eventually.of_forall (fun p => by simp only [norm_mul, phaseExponential_norm, one_mul, le_refl])

theorem spectralCharacteristic_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {delta : ℝ} (hd : 0 < delta) (a b : ℝ) :
    Integrable (fun xi => charFun μ (2*Real.pi*xi)*spectralDensity delta a b xi) := by
  have hm : Measurable (fun xi => charFun μ (2*Real.pi*xi)*spectralDensity delta a b xi) :=
    (measurable_charFun.comp (measurable_const.mul measurable_id)).mul
      (spectralDensity_continuous delta a b).measurable
  apply (spectralDensity_integrable hd a b).norm.mono' hm.aestronglyMeasurable
  exact Eventually.of_forall (fun xi => by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_charFun_le_one _))

theorem intervalWindow_expectation_fourier (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {delta : ℝ} (hd : 0 < delta) (a b : ℝ) :
    (∫ z, (intervalWindow delta a b z : ℂ) ∂μ) =
      ∫ xi, charFun μ (2*Real.pi*xi)*spectralDensity delta a b xi := by
  simp_rw [intervalWindow_fourier_representation hd]
  rw [integral_integral_swap (spectralPhase_integrable μ hd a b)]
  apply integral_congr_ae
  filter_upwards [] with xi
  rw [integral_mul_const]
  congr 1

theorem intervalWindow_expectation_error_complex (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {delta E : ℝ} (hd : 0 < delta) (hE : 0 ≤ E) (a b : ℝ)
    (hcf : ∀ u : ℝ, |u| ≤ 2*Real.pi*delta⁻¹ → ‖charFun μ u-charFun ν u‖ ≤ E) :
    ‖(∫ z, (intervalWindow delta a b z : ℂ) ∂μ)-
      (∫ z, (intervalWindow delta a b z : ℂ) ∂ν)‖ ≤ 2*max (b-a) 0*delta⁻¹*E := by
  classical
  rw [intervalWindow_expectation_fourier μ hd, intervalWindow_expectation_fourier ν hd,
    ← integral_sub (spectralCharacteristic_integrable μ hd a b)
      (spectralCharacteristic_integrable ν hd a b)]
  let S := Icc (-delta⁻¹) delta⁻¹
  have hmajor : Integrable (S.indicator (fun _ => max (b-a) 0*E)) := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const measure_Icc_lt_top.ne
  have hb := norm_integral_le_of_norm_le hmajor (f := fun xi =>
      charFun μ (2*Real.pi*xi)*spectralDensity delta a b xi-
        charFun ν (2*Real.pi*xi)*spectralDensity delta a b xi)
    (Eventually.of_forall (fun xi => by
      by_cases hxi : xi ∈ S
      · rw [indicator_of_mem hxi, ← sub_mul, norm_mul]
        have hu : |2*Real.pi*xi| ≤ 2*Real.pi*delta⁻¹ := by
          rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ)<2*Real.pi)]
          exact mul_le_mul_of_nonneg_left (abs_le.mpr hxi) (by positivity)
        exact (mul_le_mul (hcf _ hu) (spectralDensity_norm delta a b xi)
          (norm_nonneg _) hE).trans_eq (mul_comm _ _)
      · have ho : delta⁻¹ ≤ |xi| := by
          by_contra h
          exact hxi (abs_le.mp (le_of_lt (lt_of_not_ge h)))
        rw [indicator_of_notMem hxi, spectralDensity_zero_of_outside hd a b ho]
        simp))
  rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc,
    smul_eq_mul] at hb
  have hm : max (delta⁻¹- -delta⁻¹) 0 = 2*delta⁻¹ := by
    rw [max_eq_left (by linarith [inv_nonneg.mpr hd.le])]
    ring
  rw [hm] at hb
  convert hb using 1
  ring

theorem intervalWindow_expectation_error (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {delta E : ℝ} (hd : 0 < delta) (hE : 0 ≤ E) (a b : ℝ)
    (hcf : ∀ u : ℝ, |u| ≤ 2*Real.pi*delta⁻¹ → ‖charFun μ u-charFun ν u‖ ≤ E) :
    |(∫ z, intervalWindow delta a b z ∂μ)-(∫ z, intervalWindow delta a b z ∂ν)| ≤
      2*max (b-a) 0*delta⁻¹*E := by
  have h := intervalWindow_expectation_error_complex μ ν hd hE a b hcf
  rw [integral_complex_ofReal, integral_complex_ofReal, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] at h
  exact h

theorem intervalProbability_le_expanded_expectation (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {delta h : ℝ} (hd : 0 < delta) (hh : 0 < h) (a b : ℝ) :
    μ.real (Icc a b) ≤ (∫ z, intervalWindow delta (a-h) (b+h) z ∂μ)+tailAllowance delta h := by
  have hi : Integrable ((Icc a b).indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator measurableSet_Icc
  have hw : Integrable (fun z => intervalWindow delta (a-h) (b+h) z) μ :=
    intervalWindow_integrable_comp (μ := μ) measurable_id hd (a-h) (b+h)
  have hbound := integral_mono hi (hw.add (integrable_const (tailAllowance delta h)))
    (indicator_le_expandedWindow hd hh a b)
  simp only [Pi.add_apply] at hbound
  rw [integral_indicator_const _ measurableSet_Icc, smul_eq_mul, mul_one,
    integral_add hw (integrable_const _)] at hbound
  simpa only [integral_const, probReal_univ, one_smul] using hbound

theorem contracted_expectation_le_intervalProbability (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {delta h : ℝ} (hd : 0 < delta) (hh : 0 < h) (a b : ℝ) :
    (∫ z, intervalWindow delta (a+h) (b-h) z ∂μ) ≤ μ.real (Icc a b)+tailAllowance delta h := by
  have hi : Integrable ((Icc a b).indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator measurableSet_Icc
  have hw : Integrable (fun z => intervalWindow delta (a+h) (b-h) z) μ :=
    intervalWindow_integrable_comp (μ := μ) measurable_id hd (a+h) (b-h)
  have hbound := integral_mono hw (hi.add (integrable_const (tailAllowance delta h)))
    (contractedWindow_le_indicator hd hh a b)
  simp only [Pi.add_apply] at hbound
  rw [integral_add hi (integrable_const _), integral_indicator_const _ measurableSet_Icc,
    smul_eq_mul, mul_one] at hbound
  simpa only [integral_const, probReal_univ, one_smul] using hbound

end NField.Alignment.HarperSmoothingExpectation

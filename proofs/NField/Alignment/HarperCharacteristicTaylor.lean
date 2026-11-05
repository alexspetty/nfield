/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperTiltedLogMoments

/-!
# A quantitative characteristic-function Taylor bound

For a real random variable on a probability space, explicit integrability
and a bound on the phase give a cubic remainder controlled by its third
absolute moment. The estimate is quantitative and retains the parameter
factor at zero; it is not a pointwise little-o assertion.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperCharacteristicTaylor
open scoped BigOperators Topology
open MeasureTheory Filter

def phaseExponential (u x : ℝ) : ℂ := Complex.exp ((u*x : ℝ)*Complex.I)
def meanPhase (u m v : ℝ) : ℂ := 1+(u*m : ℝ)*Complex.I-(u^2*v/2 : ℝ)

theorem phaseExponential_norm (u x : ℝ) : ‖phaseExponential u x‖ = 1 := by
  simp [phaseExponential, Complex.norm_exp]

theorem phaseExponential_measurable (u : ℝ) : Measurable (phaseExponential u) := by
  unfold phaseExponential
  fun_prop

theorem phaseExponential_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : Measurable X) (u : ℝ) :
    Integrable (fun ω => phaseExponential u (X ω)) μ := by
  apply Integrable.of_bound ((phaseExponential_measurable u).comp hX).aestronglyMeasurable 1
  exact Eventually.of_forall (fun ω => (phaseExponential_norm u (X ω)).le)

theorem phaseExponential_quadratic_error (u x : ℝ) :
    ‖phaseExponential u x-meanPhase u x (x^2)‖ ≤ |u|^3*|x|^3*Real.exp |u*x| := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp ((u*x : ℝ)*Complex.I) 3
  have he : (∑ m ∈ Finset.range 3, (((u*x : ℝ) : ℂ)*Complex.I)^m/(m.factorial : ℂ)) =
      meanPhase u x (x^2) := by
    norm_num [Finset.sum_range_succ, meanPhase, mul_pow, Complex.I_sq]
    ring
  rw [he] at h
  simpa only [phaseExponential, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_I, mul_one, abs_mul, mul_pow] using h

theorem meanPhase_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ}
    (hX : Integrable X μ) (hX2 : Integrable (fun ω => X ω^2) μ) (u : ℝ) :
    Integrable (fun ω => meanPhase u (X ω) (X ω^2)) μ := by
  exact ((integrable_const (1 : ℂ)).add ((hX.const_mul u).ofReal.mul_const Complex.I)).sub
    ((hX2.const_mul (u^2)).div_const 2).ofReal

theorem meanPhase_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : Integrable X μ) (hX2 : Integrable (fun ω => X ω^2) μ) (u : ℝ) :
    (∫ ω, meanPhase u (X ω) (X ω^2) ∂μ) =
      meanPhase u (∫ ω, X ω ∂μ) (∫ ω, X ω^2 ∂μ) := by
  have hiU : Integrable (fun ω => ((u*X ω : ℝ) : ℂ)*Complex.I) μ :=
    (hX.const_mul u).ofReal.mul_const Complex.I
  have hiS : Integrable (fun ω => 1+((u*X ω : ℝ) : ℂ)*Complex.I) μ :=
    (integrable_const (1 : ℂ)).add hiU
  have hiV : Integrable (fun ω => ((u^2*X ω^2/2 : ℝ) : ℂ)) μ :=
    ((hX2.const_mul (u^2)).div_const 2).ofReal
  unfold meanPhase
  rw [integral_sub hiS hiV, integral_add (integrable_const (1 : ℂ)) hiU,
    integral_mul_const, integral_complex_ofReal, integral_const_mul,
    integral_complex_ofReal, integral_div, integral_const_mul]
  simp only [integral_const, probReal_univ, one_smul]

theorem characteristic_quadratic_error {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} (hXm : Measurable X)
    (hX : Integrable X μ) (hX2 : Integrable (fun ω => X ω^2) μ)
    (hX3 : Integrable (fun ω => |X ω|^3) μ) (u B : ℝ)
    (hB : ∀ ω, |u*X ω| ≤ B) :
    ‖(∫ ω, phaseExponential u (X ω) ∂μ)-
      meanPhase u (∫ ω, X ω ∂μ) (∫ ω, X ω^2 ∂μ)‖ ≤
      |u|^3*Real.exp B*(∫ ω, |X ω|^3 ∂μ) := by
  have h := norm_integral_le_of_norm_le (hX3.const_mul (|u|^3*Real.exp B))
    (f := fun ω => phaseExponential u (X ω)-meanPhase u (X ω) (X ω^2))
    (Eventually.of_forall (fun ω => calc
      _ ≤ |u|^3*|X ω|^3*Real.exp |u*X ω| := phaseExponential_quadratic_error u (X ω)
      _ ≤ |u|^3*|X ω|^3*Real.exp B := by gcongr; exact hB ω
      _ = _ := by ring))
  rw [integral_sub (phaseExponential_integrable hXm u) (meanPhase_integrable hX hX2 u),
    meanPhase_integral hX hX2, integral_const_mul] at h
  exact h

theorem meanPhase_difference (u m m' v v' : ℝ) :
    ‖meanPhase u m v-meanPhase u m' v'‖ ≤
      |u| *|m-m'|+(u^2/2)*|v-v'| := by
  have he : meanPhase u m v-meanPhase u m' v' =
      ((u*(m-m') : ℝ) : ℂ)*Complex.I-((u^2/2*(v-v') : ℝ) : ℂ) := by
    unfold meanPhase
    push_cast
    ring
  rw [he]
  have h := norm_sub_le (((u*(m-m') : ℝ) : ℂ)*Complex.I) (((u^2/2*(v-v') : ℝ) : ℂ))
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
    abs_mul, abs_of_nonneg (div_nonneg (sq_nonneg u) (by norm_num : (0 : ℝ)≤2))] using h

end NField.Alignment.HarperCharacteristicTaylor

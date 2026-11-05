/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperEulerSecondMoment
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The actual Euler-energy weighted phase measure

The density is the squared norm of the literal finite-prime Euler product,
divided by its proved exact second moment. Its normalization and every
change-of-measure identity use the existing infinite Haar model. No moment
saving or probabilistic comparison is assumed.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperTiltedMeasure
open scoped BigOperators
open MeasureTheory Filter SteinhausMoment HarperRandomEulerProduct
  HarperEulerSecondMoment HarperSmoothCount CollisionMertensInput

def energyDensity (P : ℝ) (s : ℂ) (ω : PhaseSpace) : ℝ :=
  ‖eulerProduct P s ω‖^2 / shiftedProduct P (2*s.re)

def tiltedMeasure (P : ℝ) (s : ℂ) : Measure PhaseSpace :=
  phaseMeasure.withDensity (fun ω => ENNReal.ofReal (energyDensity P s ω))

theorem shiftedProduct_pos (P : ℝ) {sigma : ℝ} (hs : 0 < sigma) :
    0 < shiftedProduct P sigma := by
  apply Finset.prod_pos
  intro q hq
  apply inv_pos.mpr
  apply sub_pos.mpr
  exact Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast (primesUpTo_mem.mp hq).1.one_lt) (by linarith)

theorem energyDensity_measurable (P : ℝ) (s : ℂ) : Measurable (energyDensity P s) :=
  ((eulerProduct_measurable P s).norm.pow_const 2).div_const _

theorem energyDensity_nonneg (P : ℝ) {s : ℂ} (hs : 0 < s.re) (ω : PhaseSpace) :
    0 ≤ energyDensity P s ω :=
  div_nonneg (sq_nonneg _) (shiftedProduct_pos P (by positivity)).le

theorem energyDensity_integrable (P : ℝ) {s : ℂ} (hs : 0 < s.re) :
    Integrable (energyDensity P s) phaseMeasure :=
  (eulerProduct_norm_sq_integrable P hs).div_const _

theorem energyDensity_integral (P : ℝ) {s : ℂ} (hs : 0 < s.re) :
    (∫ ω, energyDensity P s ω ∂phaseMeasure) = 1 := by
  unfold energyDensity
  rw [integral_div, eulerProduct_second_moment P hs,
    div_self (ne_of_gt (shiftedProduct_pos P (by positivity)))]

theorem tiltedMeasure_probability (P : ℝ) {s : ℂ} (hs : 0 < s.re) :
    IsProbabilityMeasure (tiltedMeasure P s) := by
  constructor
  rw [tiltedMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (energyDensity_integrable P hs)
      (Eventually.of_forall (energyDensity_nonneg P hs)), energyDensity_integral P hs]
  norm_num

theorem integral_tilted {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : ℝ) {s : ℂ} (hs : 0 < s.re) (f : PhaseSpace → E) :
    (∫ ω, f ω ∂tiltedMeasure P s) =
      ∫ ω, energyDensity P s ω • f ω ∂phaseMeasure := by
  rw [tiltedMeasure, integral_withDensity_eq_integral_toReal_smul
    (energyDensity_measurable P s).ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (energyDensity_nonneg P hs _)]

theorem setIntegral_tilted {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : ℝ) {s : ℂ} (hs : 0 < s.re) (f : PhaseSpace → E)
    {A : Set PhaseSpace} (hA : MeasurableSet A) :
    (∫ ω in A, f ω ∂tiltedMeasure P s) =
      ∫ ω in A, energyDensity P s ω • f ω ∂phaseMeasure := by
  rw [tiltedMeasure, setIntegral_withDensity_eq_setIntegral_toReal_smul
    (energyDensity_measurable P s).ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) f hA]
  simp only [ENNReal.toReal_ofReal (energyDensity_nonneg P hs _)]

theorem integrable_tilted_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : ℝ) {s : ℂ} (hs : 0 < s.re) (f : PhaseSpace → E) :
    Integrable f (tiltedMeasure P s) ↔
      Integrable (fun ω => energyDensity P s ω • f ω) phaseMeasure := by
  rw [tiltedMeasure, integrable_withDensity_iff_integrable_smul'
    (energyDensity_measurable P s).ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (energyDensity_nonneg P hs _)]

theorem tiltedMeasure_event (P : ℝ) {s : ℂ} (hs : 0 < s.re)
    {A : Set PhaseSpace} (hA : MeasurableSet A) :
    (tiltedMeasure P s).real A =
      (∫ ω in A, ‖eulerProduct P s ω‖^2 ∂phaseMeasure) / shiftedProduct P (2*s.re) := by
  letI := tiltedMeasure_probability P hs
  rw [← setIntegral_one_eq_measureReal, setIntegral_tilted P hs (fun _ => (1 : ℝ)) hA]
  simp only [smul_eq_mul, mul_one, energyDensity, integral_div]

theorem tiltedMeasure_absolutelyContinuous (P : ℝ) (s : ℂ) :
    tiltedMeasure P s ≪ phaseMeasure := withDensity_absolutelyContinuous _ _

end NField.Alignment.HarperTiltedMeasure

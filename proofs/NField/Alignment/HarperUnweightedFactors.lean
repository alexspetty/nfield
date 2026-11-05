/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperRestrictedLogMoment

/-!
# Positive and inverse critical Euler-factor moments under Haar measure

These are moments under the original phaseMeasure. Frequencies are
arbitrary deterministic real numbers. The positive second moment reuses
the proved exact local mass; the inverse second moment follows by
expanding the squared norm and using the vanishing first prime moment.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperUnweightedFactors
open MeasureTheory SteinhausMoment HarperEulerIntegral HarperEulerLogComparison
  HarperLocalExponentialMoment HarperTiltedFactors HarperTiltedNormalizer

def inverseEnergy (q : ℕ) (t : ℝ) (z : UnitAddCircle) : ℝ :=
  ‖1-fourier 1 z/(q : ℂ)^(linePoint (1/2) t)‖^2

theorem inverseEnergy_measurable (q : ℕ) (t : ℝ) : Measurable (inverseEnergy q t) :=
  (measurable_const.sub ((fourier 1).continuous.measurable.div_const _)).norm.pow_const 2

theorem norm_one_sub_sq (z : ℂ) : ‖1-z‖^2 = 1-2*z.re+‖z‖^2 := by
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
    Complex.one_re,Complex.one_im]
  ring

theorem inverse_factor_mean {q : ℕ} (hq : q.Prime) (t : ℝ) :
    (∫ ω, ‖1-primeTerm q t ω‖^2 ∂phaseMeasure) = 1+(q : ℝ)⁻¹ := by
  have hi : Integrable (primeTerm q t) phaseMeasure := by
    simpa only [pow_one] using primeTerm_pow_integrable q t 1
  have hm : (∫ ω, primeTerm q t ω ∂phaseMeasure) = 0 := by
    simpa only [pow_one] using primeTerm_pow_mean_zero hq t (show 0 < (1 : ℕ) by norm_num)
  have hir : Integrable (fun ω => (primeTerm q t ω).re) phaseMeasure := hi.re
  have hia : Integrable (fun ω => 1-2*(primeTerm q t ω).re) phaseMeasure :=
    (integrable_const (1 : ℝ)).sub (hir.const_mul (2 : ℝ))
  have hre : (∫ ω, (primeTerm q t ω).re ∂phaseMeasure) =
      (∫ ω, primeTerm q t ω ∂phaseMeasure).re := integral_re hi
  simp_rw [norm_one_sub_sq,primeTerm_norm_sq hq.ne_zero]
  rw [integral_add hia (integrable_const ((q : ℝ)⁻¹)),
    integral_sub (integrable_const (1 : ℝ)) (hir.const_mul (2 : ℝ)),integral_const_mul,hre,hm]
  simp

theorem positive_factor_mean {q : ℕ} (hq : q.Prime) (t : ℝ) :
    (∫ ω, ‖(1-primeTerm q t ω)⁻¹‖^2 ∂phaseMeasure) = (1-(q : ℝ)⁻¹)⁻¹ := by
  have he : (fun ω => ‖(1-primeTerm q t ω)⁻¹‖^2) =
      (fun ω => localEnergy q (linePoint (1/2) t) (ω q)) := by
    funext ω
    simp only [primeTerm,steinhaus_prime hq,localEnergy,phase]
  rw [he,localEnergy_phase_integral,
    localMass_eq hq (show 0 < (linePoint (1/2) t).re by norm_num [linePoint])]
  norm_num [linePoint,Real.rpow_neg_one]

theorem inverseEnergy_integral {q : ℕ} (hq : q.Prime) (t : ℝ) :
    (∫ z, inverseEnergy q t z ∂AddCircle.haarAddCircle) = 1+(q : ℝ)⁻¹ := by
  have h : (∫ ω, inverseEnergy q t (ω q) ∂phaseMeasure) =
      ∫ z, inverseEnergy q t z ∂AddCircle.haarAddCircle := by
    rw [← integral_map (measurable_pi_apply q).aemeasurable
      (inverseEnergy_measurable q t).aestronglyMeasurable,
      phaseMeasure,Measure.infinitePi_map_eval]
  rw [← h]
  simpa only [inverseEnergy,primeTerm,steinhaus_prime hq,phase] using inverse_factor_mean hq t

theorem prime_inverse_mass_bound {q : ℕ} (hq : q.Prime) :
    1+(q : ℝ)⁻¹ ≤ (1-(q : ℝ)⁻¹)⁻¹ := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have hr : 0 < (q : ℝ)⁻¹ := by positivity
  have hr1 : (q : ℝ)⁻¹ < 1 := (inv_lt_one₀ (by positivity)).mpr hq1
  rw [← one_div (1-(q : ℝ)⁻¹)]
  rw [le_div_iff₀ (by linarith : 0 < 1-(q : ℝ)⁻¹)]
  nlinarith [sq_nonneg ((q : ℝ)⁻¹)]

theorem prime_positive_mass_ge_one {q : ℕ} (hq : q.Prime) :
    1 ≤ (1-(q : ℝ)⁻¹)⁻¹ :=
  (le_add_of_nonneg_right (inv_nonneg.mpr (Nat.cast_nonneg q))).trans (prime_inverse_mass_bound hq)

end NField.Alignment.HarperUnweightedFactors

/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperTiltedLogBounds
import NField.Alignment.HarperTiltedCrossMoment

/-!
# Three local moments under the actual critical Euler-energy weighting

The weighted logarithm has mean cos(t log q)/q and second moment 1/(2q),
each with an explicit O(q^(-3/2)) remainder uniform in t. Its third
absolute moment is at most 27 q^(-3/2). These are estimates, not exact
Gaussian identities; the characteristic-function comparison is still a
separate proof obligation.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperTiltedLogMoments
open scoped BigOperators Topology ENNReal
open MeasureTheory Filter SteinhausMoment HarperTiltedFactors HarperTiltedMeasure
  HarperTiltedCoordinates HarperEulerIntegral HarperEulerLogComparison HarperLocalExponentialMoment
  HarperTiltedLogBounds HarperTiltedCrossMoment CollisionMertensInput

theorem weighted_primeLog_pow_integrable {q : ℕ} (hq : q.Prime) (t : ℝ) (k : ℕ) :
    Integrable (fun ω => criticalDensity q ω*(primeLog q t ω)^k) phaseMeasure := by
  apply Integrable.of_bound ((criticalDensity_measurable q).mul
    ((primeLog_measurable q t).pow_const k)).aestronglyMeasurable
      (16*(3*(q : ℝ)^(-(1/2 : ℝ)))^k)
  apply Eventually.of_forall
  intro ω
  change |criticalDensity q ω*(primeLog q t ω)^k| ≤ _
  rw [abs_mul, abs_pow, abs_of_nonneg (criticalDensity_bounds hq ω).1]
  exact mul_le_mul (criticalDensity_bounds hq ω).2
    (pow_le_pow_left₀ (abs_nonneg _) (primeLog_abs_bound hq t ω) k)
    (by positivity) (by norm_num)

theorem weighted_primeLog_abs_pow_integrable {q : ℕ} (hq : q.Prime) (t : ℝ) (k : ℕ) :
    Integrable (fun ω => criticalDensity q ω*|primeLog q t ω|^k) phaseMeasure := by
  have h := (weighted_primeLog_pow_integrable hq t k).abs
  simpa only [abs_mul, abs_pow, abs_of_nonneg (criticalDensity_bounds hq _).1] using h

theorem primeQuadratic_integrable (q : ℕ) (t : ℝ) :
    Integrable (fun ω => (primeTerm q t ω+(primeTerm q t ω)^2/2).re) phaseMeasure := by
  have hi : Integrable (primeTerm q t) phaseMeasure := by
    simpa only [pow_one] using primeTerm_pow_integrable q t 1
  exact (hi.add ((primeTerm_pow_integrable q t 2).div_const 2)).re

theorem primeQuadratic_mean {q : ℕ} (hq : q.Prime) (t : ℝ) :
    (∫ ω, (primeTerm q t ω+(primeTerm q t ω)^2/2).re ∂phaseMeasure) = 0 := by
  have h := localArgument_mean hq t
  unfold localArgument at h
  rw [integral_const_mul] at h
  linarith

theorem weighted_primeLog_mean {q : ℕ} (hq : q.Prime) (t : ℝ) :
    |(∫ ω, criticalDensity q ω*primeLog q t ω ∂phaseMeasure)-
      Real.cos (t*Real.log q)/q| ≤ 390*(q : ℝ)^(-(3/2 : ℝ)) := by
  have hi : Integrable (fun ω => criticalDensity q ω*primeLog q t ω) phaseMeasure := by
    simpa only [pow_one] using weighted_primeLog_pow_integrable hq t 1
  have hc : Integrable (fun ω => 2*(primeTerm q 0 ω).re*(primeTerm q t ω).re) phaseMeasure := by
    simpa only [mul_assoc] using (primeTerm_mixed_re_integrable hq.ne_zero t).const_mul 2
  have hm : (∫ ω, (primeTerm q t ω+(primeTerm q t ω)^2/2).re+
      2*(primeTerm q 0 ω).re*(primeTerm q t ω).re ∂phaseMeasure) =
      Real.cos (t*Real.log q)/q := by
    rw [integral_add (primeQuadratic_integrable q t) hc, primeQuadratic_mean hq t]
    simp_rw [mul_assoc]
    rw [integral_const_mul, primeTerm_mixed_re_mean hq t]
    ring
  have h := norm_integral_le_of_norm_le_const (μ := phaseMeasure)
    (f := fun ω => criticalDensity q ω*primeLog q t ω-
      ((primeTerm q t ω+(primeTerm q t ω)^2/2).re+
        2*(primeTerm q 0 ω).re*(primeTerm q t ω).re))
    (Eventually.of_forall (fun ω => primeLog_weighted_linear_error hq t ω))
  have his : Integrable (fun ω => (primeTerm q t ω+(primeTerm q t ω)^2/2).re+
      2*(primeTerm q 0 ω).re*(primeTerm q t ω).re) phaseMeasure :=
    (primeQuadratic_integrable q t).add hc
  rw [integral_sub hi his, hm,
    Real.norm_eq_abs, probReal_univ, mul_one] at h
  exact h

theorem weighted_primeLog_second_moment {q : ℕ} (hq : q.Prime) (t : ℝ) :
    |(∫ ω, criticalDensity q ω*(primeLog q t ω)^2 ∂phaseMeasure)-(q : ℝ)⁻¹/2| ≤
      512*(q : ℝ)^(-(3/2 : ℝ)) := by
  have h := norm_integral_le_of_norm_le_const (μ := phaseMeasure)
    (f := fun ω => criticalDensity q ω*(primeLog q t ω)^2-(primeTerm q t ω).re^2)
    (Eventually.of_forall (fun ω => primeLog_weighted_square_error hq t ω))
  rw [integral_sub (weighted_primeLog_pow_integrable hq t 2)
    (primeTerm_re_square_integrable hq.ne_zero t), primeTerm_re_square_mean hq t,
    Real.norm_eq_abs, probReal_univ, mul_one] at h
  exact h

theorem weighted_primeLog_third_absolute_moment {q : ℕ} (hq : q.Prime) (t : ℝ) :
    (∫ ω, criticalDensity q ω*|primeLog q t ω|^3 ∂phaseMeasure) ≤
      27*(q : ℝ)^(-(3/2 : ℝ)) := by
  have hi : Integrable (criticalDensity q) phaseMeasure := by
    apply Integrable.of_bound (criticalDensity_measurable q).aestronglyMeasurable 16
    exact Eventually.of_forall (fun ω => by
      rw [Real.norm_of_nonneg (criticalDensity_bounds hq ω).1]
      exact (criticalDensity_bounds hq ω).2)
  calc
    _ ≤ ∫ ω, criticalDensity q ω*(27*(q : ℝ)^(-(3/2 : ℝ))) ∂phaseMeasure := by
      apply integral_mono (weighted_primeLog_abs_pow_integrable hq t 3) (hi.mul_const _)
      intro ω
      apply mul_le_mul_of_nonneg_left _ (criticalDensity_bounds hq ω).1
      calc
        _ ≤ (3*(q : ℝ)^(-(1/2 : ℝ)))^3 :=
          pow_le_pow_left₀ (abs_nonneg _) (primeLog_abs_bound hq t ω) 3
        _ = _ := by
          rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg q)]
          norm_num
    _ = _ := by rw [integral_mul_const, criticalDensity_integral hq, one_mul]


theorem integral_critical_coordinate (P : ℝ) {q : ℕ} (hq : q ∈ primesUpTo P)
    (f : UnitAddCircle → ℝ) (hf : Measurable f) :
    (∫ ω, f (ω q) ∂tiltedMeasure P (linePoint (1/2) 0)) =
      ∫ ω, criticalDensity q ω*f (ω q) ∂phaseMeasure := by
  have hs : 0 < (linePoint (1/2) 0).re := by norm_num [linePoint]
  have hp := (primesUpTo_mem.mp hq).1
  calc
    _ = ∫ z, f z ∂coordinateLaw P (linePoint (1/2) 0) q := by
      rw [← integral_map (measurable_pi_apply q).aemeasurable hf.aestronglyMeasurable,
        coordinate_law P hs q]
    _ = ∫ z, localDensity q (linePoint (1/2) 0) z*f z ∂AddCircle.haarAddCircle := by
      unfold coordinateLaw coordinateDensity
      simp only [if_pos hq]
      rw [integral_withDensity_eq_integral_toReal_smul
        (localDensity_measurable q (linePoint (1/2) 0)).ennreal_ofReal
        (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
      simp only [ENNReal.toReal_ofReal (localDensity_pos hp hs _).le, smul_eq_mul]
    _ = _ := by
      change _ = ∫ ω, (localDensity q (linePoint (1/2) 0) (ω q))*f (ω q) ∂phaseMeasure
      have hmap : (∫ z, localDensity q (linePoint (1/2) 0) z*f z
          ∂phaseMeasure.map (fun ω => ω q)) =
          ∫ ω, localDensity q (linePoint (1/2) 0) (ω q)*f (ω q) ∂phaseMeasure :=
        integral_map (measurable_pi_apply q).aemeasurable
          ((localDensity_measurable q (linePoint (1/2) 0)).mul hf).aestronglyMeasurable
      rw [phaseMeasure, Measure.infinitePi_map_eval] at hmap
      exact hmap

theorem integral_tilted_primeLog (P : ℝ) {q : ℕ} (hq : q ∈ primesUpTo P) (t : ℝ)
    (g : ℝ → ℝ) (hg : Measurable g) :
    (∫ ω, g (primeLog q t ω) ∂tiltedMeasure P (linePoint (1/2) 0)) =
      ∫ ω, criticalDensity q ω*g (primeLog q t ω) ∂phaseMeasure := by
  let f : UnitAddCircle → ℝ := fun z => g (logFactor (fourier 1 z/(q : ℂ)^(linePoint (1/2) t)))
  have hf : Measurable f := hg.comp
    (((measurable_const.sub ((fourier 1).continuous.measurable.div_const _)).inv.norm).log)
  have he (ω : PhaseSpace) : f (ω q) = g (primeLog q t ω) := by
    simp only [f, primeLog, primeTerm, steinhaus_prime (primesUpTo_mem.mp hq).1]
    rfl
  have h := integral_critical_coordinate P hq f hf
  simpa only [he] using h


theorem tilted_primeLog_pow_integrable (P : ℝ) {q : ℕ} (hq : q.Prime) (t : ℝ) (k : ℕ) :
    Integrable (fun ω => (primeLog q t ω)^k) (tiltedMeasure P (linePoint (1/2) 0)) := by
  letI := tiltedMeasure_probability P (show 0 < (linePoint (1/2) 0).re by norm_num [linePoint])
  apply Integrable.of_bound ((primeLog_measurable q t).pow_const k).aestronglyMeasurable
    ((3*(q : ℝ)^(-(1/2 : ℝ)))^k)
  apply Eventually.of_forall
  intro ω
  change |primeLog q t ω^k| ≤ _
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (primeLog_abs_bound hq t ω) k

theorem tilted_primeLog_abs_pow_integrable (P : ℝ) {q : ℕ} (hq : q.Prime) (t : ℝ) (k : ℕ) :
    Integrable (fun ω => |primeLog q t ω|^k) (tiltedMeasure P (linePoint (1/2) 0)) := by
  simpa only [abs_pow] using (tilted_primeLog_pow_integrable P hq t k).abs

theorem tilted_primeLog_mean (P : ℝ) {q : ℕ} (hq : q ∈ primesUpTo P) (t : ℝ) :
    |(∫ ω, primeLog q t ω ∂tiltedMeasure P (linePoint (1/2) 0))-
      Real.cos (t*Real.log q)/q| ≤ 390*(q : ℝ)^(-(3/2 : ℝ)) := by
  have he := integral_tilted_primeLog P hq t id measurable_id
  simp only [id_eq] at he
  rw [he]
  exact weighted_primeLog_mean (primesUpTo_mem.mp hq).1 t

theorem tilted_primeLog_second_moment (P : ℝ) {q : ℕ} (hq : q ∈ primesUpTo P) (t : ℝ) :
    |(∫ ω, (primeLog q t ω)^2 ∂tiltedMeasure P (linePoint (1/2) 0))-(q : ℝ)⁻¹/2| ≤
      512*(q : ℝ)^(-(3/2 : ℝ)) := by
  rw [integral_tilted_primeLog P hq t (fun x => x^2) (measurable_id.pow_const 2)]
  exact weighted_primeLog_second_moment (primesUpTo_mem.mp hq).1 t

theorem tilted_primeLog_third_absolute_moment (P : ℝ) {q : ℕ} (hq : q ∈ primesUpTo P) (t : ℝ) :
    (∫ ω, |primeLog q t ω|^3 ∂tiltedMeasure P (linePoint (1/2) 0)) ≤
      27*(q : ℝ)^(-(3/2 : ℝ)) := by
  rw [integral_tilted_primeLog P hq t (fun x => |x|^3) (measurable_id.abs.pow_const 3)]
  exact weighted_primeLog_third_absolute_moment (primesUpTo_mem.mp hq).1 t

end NField.Alignment.HarperTiltedLogMoments

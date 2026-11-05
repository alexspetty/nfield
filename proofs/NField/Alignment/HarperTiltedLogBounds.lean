/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperTiltedNormalizer
import NField.Alignment.HarperLocalExponentialMoment

/-!
# Pointwise estimates for the actual weighted logarithmic factors

Explicit local normalization gives uniform first-order density bounds.
Together with the cubic logarithmic remainder these control the weighted
first, second and third moments at the critical line. This module supplies
the pointwise estimates; it does not assert a Gaussian comparison.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperTiltedLogBounds
open scoped BigOperators Topology
open MeasureTheory Filter SteinhausMoment HarperTiltedFactors HarperTiltedNormalizer
  HarperEulerIntegral HarperEulerLogComparison HarperLocalExponentialMoment

def kernelWeight (z : ℂ) : ℝ := (1-‖z‖^2)/‖1-z‖^2
def logFactor (z : ℂ) : ℝ := Real.log ‖(1-z)⁻¹‖
def criticalDensity (q : ℕ) (ω : PhaseSpace) : ℝ :=
  localDensity q (linePoint (1/2) 0) (ω q)
def primeLog (q : ℕ) (t : ℝ) (ω : PhaseSpace) : ℝ := logFactor (primeTerm q t ω)

theorem norm_one_sub_sq (z : ℂ) : ‖1-z‖^2 = 1-2*z.re+‖z‖^2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.one_re,
    Complex.sub_im, Complex.one_im]
  ring

theorem norm_one_sub_sq_lower {z : ℂ} (hz : ‖z‖ ≤ 3/4) :
    (1/16 : ℝ) ≤ ‖1-z‖^2 := by
  have h := norm_sub_norm_le (1 : ℂ) z
  rw [norm_one] at h
  nlinarith [norm_nonneg (1-z), sq_nonneg (‖1-z‖-1/4)]

theorem kernelWeight_nonneg {z : ℂ} (hz : ‖z‖ ≤ 3/4) : 0 ≤ kernelWeight z := by
  unfold kernelWeight
  apply div_nonneg _ (sq_nonneg _)
  nlinarith [norm_nonneg z]

theorem kernelWeight_bound {z : ℂ} (hz : ‖z‖ ≤ 3/4) : kernelWeight z ≤ 16 := by
  have hd := norm_one_sub_sq_lower hz
  rw [kernelWeight, div_le_iff₀ (by linarith : 0 < ‖1-z‖^2)]
  nlinarith [sq_nonneg ‖z‖]

theorem kernelWeight_sub_one {z : ℂ} (hz : ‖z‖ ≤ 3/4) :
    |kernelWeight z-1| ≤ 56*‖z‖ := by
  have hd := norm_one_sub_sq_lower hz
  have hn := norm_nonneg z
  have ha := abs_le.mp (Complex.abs_re_le_norm z)
  have hne : ‖1-z‖ ≠ 0 := by nlinarith
  have he : kernelWeight z-1 = (2*z.re-2*‖z‖^2)/‖1-z‖^2 := by
    rw [kernelWeight]
    field_simp [hne]
    rw [norm_one_sub_sq]
    ring
  rw [he, abs_div, abs_of_pos (by linarith : 0 < ‖1-z‖^2),
    div_le_iff₀ (by linarith : 0 < ‖1-z‖^2)]
  have hm := mul_le_mul_of_nonneg_left hd (show 0 ≤ 56*‖z‖ by positivity)
  apply abs_le.mpr
  constructor <;> nlinarith

theorem kernelWeight_linear_error {z : ℂ} (hz : ‖z‖ ≤ 3/4) :
    |kernelWeight z-1-2*z.re| ≤ 128*‖z‖^2 := by
  have hd := norm_one_sub_sq_lower hz
  have hn := norm_nonneg z
  have ha := abs_le.mp (Complex.abs_re_le_norm z)
  have ha2 : z.re^2 ≤ ‖z‖^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm z) 2
  have hr3 : ‖z‖^3 ≤ (3/4)*‖z‖^2 := by nlinarith [sq_nonneg ‖z‖]
  have haz := mul_le_mul_of_nonneg_right ha.2 (sq_nonneg ‖z‖)
  have haz' := mul_le_mul_of_nonneg_right ha.1 (sq_nonneg ‖z‖)
  have hne : ‖1-z‖ ≠ 0 := by nlinarith
  have he : kernelWeight z-1-2*z.re =
      (-2*‖z‖^2+4*z.re^2-2*z.re*‖z‖^2)/‖1-z‖^2 := by
    rw [kernelWeight]
    field_simp [hne]
    rw [norm_one_sub_sq]
    ring
  rw [he, abs_div, abs_of_pos (by linarith : 0 < ‖1-z‖^2),
    div_le_iff₀ (by linarith : 0 < ‖1-z‖^2)]
  have hm := mul_le_mul_of_nonneg_left hd (show 0 ≤ 128*‖z‖^2 by positivity)
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg z.re]

theorem logFactor_quadratic_error {z : ℂ} (hz : ‖z‖ ≤ 3/4) :
    |logFactor z-(z+z^2/2).re| ≤ 2*‖z‖^3 := by
  have h := (Complex.abs_re_le_norm
    (Complex.log (1-z)⁻¹-(z+z^2/2))).trans (local_log_quadratic_bound hz)
  simpa only [Complex.sub_re, Complex.log_re, logFactor] using h

theorem logFactor_linear_error {z : ℂ} (hz : ‖z‖ ≤ 3/4) :
    |logFactor z-z.re| ≤ 2*‖z‖^2 := by
  have hq := logFactor_quadratic_error hz
  have hb : |(z^2/2).re| ≤ ‖z‖^2/2 := by
    have h := Complex.abs_re_le_norm (z^2/2)
    simpa only [norm_div, norm_pow, Complex.norm_ofNat] using h
  have ht := abs_add_le (logFactor z-(z+z^2/2).re) (z^2/2).re
  have he : logFactor z-(z+z^2/2).re+(z^2/2).re = logFactor z-z.re := by
    rw [Complex.add_re]
    ring
  rw [he] at ht
  have hr3 : ‖z‖^3 ≤ (3/4)*‖z‖^2 := by nlinarith [sq_nonneg ‖z‖]
  linarith

theorem logFactor_abs_bound {z : ℂ} (hz : ‖z‖ ≤ 3/4) :
    |logFactor z| ≤ 3*‖z‖ := by
  have h := logFactor_linear_error hz
  have ht := abs_add_le (logFactor z-z.re) z.re
  rw [sub_add_cancel] at ht
  have ha := Complex.abs_re_le_norm z
  have hr2 : ‖z‖^2 ≤ (3/4)*‖z‖ := by nlinarith [norm_nonneg z]
  linarith [norm_nonneg z]

theorem logFactor_square_error {z : ℂ} (hz : ‖z‖ ≤ 3/4) :
    |(logFactor z)^2-z.re^2| ≤ 8*‖z‖^3 := by
  have hp : |logFactor z+z.re| ≤ 4*‖z‖ := by
    linarith [abs_add_le (logFactor z) z.re, logFactor_abs_bound hz,
      Complex.abs_re_le_norm z]
  calc
    _ = |(logFactor z-z.re)*(logFactor z+z.re)| := by congr 1; ring
    _ = |logFactor z-z.re| * |logFactor z+z.re| := abs_mul _ _
    _ ≤ (2*‖z‖^2)*(4*‖z‖) := mul_le_mul (logFactor_linear_error hz) hp
      (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem weighted_log_linear_error {a b : ℂ} (ha : ‖a‖ ≤ 3/4) (hab : ‖b‖ = ‖a‖) :
    |kernelWeight a*logFactor b-((b+b^2/2).re+2*a.re*b.re)| ≤ 390*‖a‖^3 := by
  have hb : ‖b‖ ≤ 3/4 := hab.trans_le ha
  have he : kernelWeight a*logFactor b-((b+b^2/2).re+2*a.re*b.re) =
      (kernelWeight a-1-2*a.re)*logFactor b+
        2*a.re*(logFactor b-b.re)+(logFactor b-(b+b^2/2).re) := by ring
  have h1 : |(kernelWeight a-1-2*a.re)*logFactor b| ≤ 384*‖a‖^3 := by
    rw [abs_mul]
    calc
      _ ≤ (128*‖a‖^2)*(3*‖b‖) := mul_le_mul (kernelWeight_linear_error ha)
        (logFactor_abs_bound hb) (abs_nonneg _) (by positivity)
      _ = _ := by rw [hab]; ring
  have h2 : |2*a.re*(logFactor b-b.re)| ≤ 4*‖a‖^3 := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ)<2)]
    calc
      _ ≤ (2*‖a‖)*(2*‖b‖^2) := mul_le_mul (by gcongr; exact Complex.abs_re_le_norm a)
        (logFactor_linear_error hb) (abs_nonneg _) (by positivity)
      _ = _ := by rw [hab]; ring
  have h3 := logFactor_quadratic_error hb
  rw [hab] at h3
  rw [he]
  linarith [abs_add_le ((kernelWeight a-1-2*a.re)*logFactor b)
    (2*a.re*(logFactor b-b.re)), abs_add_le
    ((kernelWeight a-1-2*a.re)*logFactor b+2*a.re*(logFactor b-b.re))
    (logFactor b-(b+b^2/2).re)]

theorem weighted_log_square_error {a b : ℂ} (ha : ‖a‖ ≤ 3/4) (hab : ‖b‖ = ‖a‖) :
    |kernelWeight a*(logFactor b)^2-b.re^2| ≤ 512*‖a‖^3 := by
  have hb : ‖b‖ ≤ 3/4 := hab.trans_le ha
  have he : kernelWeight a*(logFactor b)^2-b.re^2 =
      (kernelWeight a-1)*(logFactor b)^2+((logFactor b)^2-b.re^2) := by ring
  have h1 : |(kernelWeight a-1)*(logFactor b)^2| ≤ 504*‖a‖^3 := by
    rw [abs_mul, abs_pow]
    calc
      _ ≤ (56*‖a‖)*(3*‖b‖)^2 := mul_le_mul (kernelWeight_sub_one ha)
        (pow_le_pow_left₀ (abs_nonneg _) (logFactor_abs_bound hb) 2)
        (by positivity) (by positivity)
      _ = _ := by rw [hab]; ring
  have h2 := logFactor_square_error hb
  rw [hab] at h2
  rw [he]
  linarith [abs_add_le ((kernelWeight a-1)*(logFactor b)^2) ((logFactor b)^2-b.re^2)]

theorem criticalDensity_eq_kernelWeight {q : ℕ} (hq : q.Prime) (ω : PhaseSpace) :
    criticalDensity q ω = kernelWeight (primeTerm q 0 ω) := by
  rw [criticalDensity, localDensity_norm_form hq (by norm_num [linePoint])]
  rw [primeTerm, steinhaus_prime hq]
  rfl

theorem criticalDensity_measurable (q : ℕ) : Measurable (criticalDensity q) :=
  (localDensity_measurable q (linePoint (1/2) 0)).comp (measurable_pi_apply q)

theorem criticalDensity_integral {q : ℕ} (hq : q.Prime) :
    (∫ ω, criticalDensity q ω ∂phaseMeasure) = 1 := by
  rw [show criticalDensity q = fun ω => localDensity q (linePoint (1/2) 0) (ω q) from rfl,
    ← integral_map (measurable_pi_apply q).aemeasurable
      (localDensity_measurable q (linePoint (1/2) 0)).aestronglyMeasurable,
    phaseMeasure, Measure.infinitePi_map_eval]
  exact localDensity_integral hq (by norm_num [linePoint])

theorem criticalDensity_bounds {q : ℕ} (hq : q.Prime) (ω : PhaseSpace) :
    0 ≤ criticalDensity q ω ∧ criticalDensity q ω ≤ 16 := by
  rw [criticalDensity_eq_kernelWeight hq]
  exact ⟨kernelWeight_nonneg (primeTerm_norm_le hq 0 ω),
    kernelWeight_bound (primeTerm_norm_le hq 0 ω)⟩

theorem primeLog_measurable (q : ℕ) (t : ℝ) : Measurable (primeLog q t) :=
  ((measurable_const.sub (primeTerm_measurable q t)).inv.norm).log

theorem primeLog_abs_bound {q : ℕ} (hq : q.Prime) (t : ℝ) (ω : PhaseSpace) :
    |primeLog q t ω| ≤ 3*(q : ℝ)^(-(1/2 : ℝ)) := by
  exact (logFactor_abs_bound (primeTerm_norm_le hq t ω)).trans_eq
    (by rw [primeTerm_norm hq.ne_zero])

theorem primeLog_integrable {q : ℕ} (hq : q.Prime) (t : ℝ) :
    Integrable (primeLog q t) phaseMeasure := by
  apply Integrable.of_bound (primeLog_measurable q t).aestronglyMeasurable
    (3*(q : ℝ)^(-(1/2 : ℝ)))
  exact Eventually.of_forall (fun ω => by
    rw [Real.norm_eq_abs]
    exact primeLog_abs_bound hq t ω)

theorem primeLog_weighted_linear_error {q : ℕ} (hq : q.Prime) (t : ℝ) (ω : PhaseSpace) :
    |criticalDensity q ω*primeLog q t ω-
      ((primeTerm q t ω+(primeTerm q t ω)^2/2).re+
        2*(primeTerm q 0 ω).re*(primeTerm q t ω).re)| ≤ 390*(q : ℝ)^(-(3/2 : ℝ)) := by
  rw [criticalDensity_eq_kernelWeight hq]
  have h := weighted_log_linear_error (primeTerm_norm_le hq 0 ω)
    (show ‖primeTerm q t ω‖ = ‖primeTerm q 0 ω‖ by rw [primeTerm_norm hq.ne_zero,
      primeTerm_norm hq.ne_zero])
  rw [primeTerm_norm_cube hq.ne_zero] at h
  exact h

theorem primeLog_weighted_square_error {q : ℕ} (hq : q.Prime) (t : ℝ) (ω : PhaseSpace) :
    |criticalDensity q ω*(primeLog q t ω)^2-(primeTerm q t ω).re^2| ≤
      512*(q : ℝ)^(-(3/2 : ℝ)) := by
  rw [criticalDensity_eq_kernelWeight hq]
  have h := weighted_log_square_error (primeTerm_norm_le hq 0 ω)
    (show ‖primeTerm q t ω‖ = ‖primeTerm q 0 ω‖ by rw [primeTerm_norm hq.ne_zero,
      primeTerm_norm hq.ne_zero])
  rw [primeTerm_norm_cube hq.ne_zero] at h
  exact h

end NField.Alignment.HarperTiltedLogBounds

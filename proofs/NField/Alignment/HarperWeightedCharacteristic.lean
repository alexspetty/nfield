/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperGaussianFactor

/-!
# The actual local weighted characteristic-function comparison

The proved logarithmic moments give a quantitative comparison to the
leading Gaussian factor, uniform in frequency and prime, for |u|<=sqrt(q).
The error retains |u|+|u|^3, hence vanishes at zero. The probability law
and all moment inputs are the actual Euler-energy weighted law.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperWeightedCharacteristic
open scoped BigOperators Topology
open MeasureTheory Filter SteinhausMoment HarperTiltedMeasure HarperEulerIntegral
  HarperTiltedLogBounds HarperTiltedLogMoments HarperCharacteristicTaylor HarperGaussianFactor
  CollisionMertensInput

def localCharacteristic (P : ℝ) (q : ℕ) (t u : ℝ) : ℂ :=
  ∫ ω, phaseExponential u (primeLog q t ω) ∂tiltedMeasure P (linePoint (1/2) 0)
def comparisonConstant : ℝ := 646+27*Real.exp 3+Real.exp 2

theorem comparisonConstant_pos : 0 < comparisonConstant := by
  unfold comparisonConstant
  positivity

theorem localCharacteristic_zero (P : ℝ) (q : ℕ) (t : ℝ) :
    localCharacteristic P q t 0 = 1 := by
  letI := tiltedMeasure_probability P (show 0 < (linePoint (1/2) 0).re by norm_num [linePoint])
  unfold localCharacteristic
  simp only [phaseExponential, zero_mul, Complex.ofReal_zero, Complex.exp_zero,
    integral_const, probReal_univ, one_smul]

theorem localCharacteristic_norm_le_one (P : ℝ) (q : ℕ) (t u : ℝ) :
    ‖localCharacteristic P q t u‖ ≤ 1 := by
  letI := tiltedMeasure_probability P (show 0 < (linePoint (1/2) 0).re by norm_num [linePoint])
  have h := norm_integral_le_of_norm_le_const
    (μ := tiltedMeasure P (linePoint (1/2) 0))
    (f := fun ω => phaseExponential u (primeLog q t ω))
    (Eventually.of_forall (fun ω => (phaseExponential_norm u (primeLog q t ω)).le))
  simpa only [localCharacteristic, probReal_univ, mul_one] using h

theorem primeLog_phase_bound {q : ℕ} (hq : q.Prime) (t : ℝ) {u : ℝ}
    (hu : |u| ≤ Real.sqrt q) (ω : PhaseSpace) : |u*primeLog q t ω| ≤ 3 := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  calc
    _ = |u| *|primeLog q t ω| := abs_mul _ _
    _ ≤ Real.sqrt q*(3*(q : ℝ)^(-(1/2 : ℝ))) := mul_le_mul hu
      (primeLog_abs_bound hq t ω) (abs_nonneg _) (Real.sqrt_nonneg _)
    _ = 3*(Real.sqrt q*(q : ℝ)^(-(1/2 : ℝ))) := by ring
    _ = 3 := by rw [sqrt_mul_neg_half hq0]; ring

theorem localCharacteristic_quadratic_error (P : ℝ) {q : ℕ} (hq : q ∈ primesUpTo P)
    (t : ℝ) {u : ℝ} (hu : |u| ≤ Real.sqrt q) :
    ‖localCharacteristic P q t u-
      meanPhase u (∫ ω, primeLog q t ω ∂tiltedMeasure P (linePoint (1/2) 0))
        (∫ ω, (primeLog q t ω)^2 ∂tiltedMeasure P (linePoint (1/2) 0))‖ ≤
      27*Real.exp 3*|u|^3*(q : ℝ)^(-(3/2 : ℝ)) := by
  letI := tiltedMeasure_probability P (show 0 < (linePoint (1/2) 0).re by norm_num [linePoint])
  have hp := (primesUpTo_mem.mp hq).1
  have hi : Integrable (primeLog q t) (tiltedMeasure P (linePoint (1/2) 0)) := by
    simpa only [pow_one] using tilted_primeLog_pow_integrable P hp t 1
  have h := characteristic_quadratic_error (primeLog_measurable q t) hi
    (tilted_primeLog_pow_integrable P hp t 2) (tilted_primeLog_abs_pow_integrable P hp t 3)
    u 3 (primeLog_phase_bound hp t hu)
  calc
    _ ≤ |u|^3*Real.exp 3*(∫ ω, |primeLog q t ω|^3
        ∂tiltedMeasure P (linePoint (1/2) 0)) := h
    _ ≤ |u|^3*Real.exp 3*(27*(q : ℝ)^(-(3/2 : ℝ))) :=
      mul_le_mul_of_nonneg_left (tilted_primeLog_third_absolute_moment P hq t) (by positivity)
    _ = _ := by ring

theorem localCharacteristic_moment_error (P : ℝ) {q : ℕ} (hq : q ∈ primesUpTo P)
    (t u : ℝ) :
    ‖meanPhase u (∫ ω, primeLog q t ω ∂tiltedMeasure P (linePoint (1/2) 0))
        (∫ ω, (primeLog q t ω)^2 ∂tiltedMeasure P (linePoint (1/2) 0))-
      meanPhase u (Real.cos (t*Real.log q)/q) ((q : ℝ)⁻¹/2)‖ ≤
      (390*|u|+256*u^2)*(q : ℝ)^(-(3/2 : ℝ)) := by
  calc
    _ ≤ |u| *|(∫ ω, primeLog q t ω ∂tiltedMeasure P (linePoint (1/2) 0))-
        Real.cos (t*Real.log q)/q|+
      (u^2/2)*|(∫ ω, (primeLog q t ω)^2 ∂tiltedMeasure P (linePoint (1/2) 0))-
        (q : ℝ)⁻¹/2| := meanPhase_difference _ _ _ _ _
    _ ≤ |u| *(390*(q : ℝ)^(-(3/2 : ℝ)))+
        (u^2/2)*(512*(q : ℝ)^(-(3/2 : ℝ))) :=
      add_le_add (mul_le_mul_of_nonneg_left (tilted_primeLog_mean P hq t) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (tilted_primeLog_second_moment P hq t) (by positivity))
    _ = _ := by ring

theorem localCharacteristic_gaussian_error (P : ℝ) {q : ℕ} (hq : q ∈ primesUpTo P)
    (t : ℝ) {u : ℝ} (hu : |u| ≤ Real.sqrt q) :
    ‖localCharacteristic P q t u-gaussianFactor q (Real.cos (t*Real.log q)) u‖ ≤
      comparisonConstant*(|u|+|u|^3)*(q : ℝ)^(-(3/2 : ℝ)) := by
  have hp := (primesUpTo_mem.mp hq).1
  have hr : 0 ≤ (q : ℝ)^(-(3/2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg q) _
  let A := meanPhase u (∫ ω, primeLog q t ω ∂tiltedMeasure P (linePoint (1/2) 0))
    (∫ ω, (primeLog q t ω)^2 ∂tiltedMeasure P (linePoint (1/2) 0))
  let B := meanPhase u (Real.cos (t*Real.log q)/q) ((q : ℝ)⁻¹/2)
  have h1 : ‖localCharacteristic P q t u-A‖ ≤
      (27*Real.exp 3)*(|u|+|u|^3)*(q : ℝ)^(-(3/2 : ℝ)) := by
    apply (localCharacteristic_quadratic_error P hq t hu).trans
    gcongr
    exact le_add_of_nonneg_left (abs_nonneg u)
  have h2 : ‖A-B‖ ≤ 646*(|u|+|u|^3)*(q : ℝ)^(-(3/2 : ℝ)) := by
    apply (localCharacteristic_moment_error P hq t u).trans
    apply mul_le_mul_of_nonneg_right _ hr
    nlinarith [square_le_abs_add_cube u, pow_nonneg (abs_nonneg u) 3]
  have h3 : ‖B-gaussianFactor q (Real.cos (t*Real.log q)) u‖ ≤
      Real.exp 2*(|u|+|u|^3)*(q : ℝ)^(-(3/2 : ℝ)) := by
    rw [norm_sub_rev]
    exact gaussianFactor_error (by exact_mod_cast hp.one_lt.le) (Real.abs_cos_le_one _) hu
  calc
    _ ≤ ‖localCharacteristic P q t u-A‖+‖A-gaussianFactor q (Real.cos (t*Real.log q)) u‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖localCharacteristic P q t u-A‖+(‖A-B‖+‖B-gaussianFactor q (Real.cos (t*Real.log q)) u‖) :=
      add_le_add le_rfl (norm_sub_le_norm_sub_add_norm_sub _ _ _)
    _ ≤ (27*Real.exp 3)*(|u|+|u|^3)*(q : ℝ)^(-(3/2 : ℝ))+
        (646*(|u|+|u|^3)*(q : ℝ)^(-(3/2 : ℝ))+
          Real.exp 2*(|u|+|u|^3)*(q : ℝ)^(-(3/2 : ℝ))) := add_le_add h1 (add_le_add h2 h3)
    _ = _ := by unfold comparisonConstant; ring

end NField.Alignment.HarperWeightedCharacteristic

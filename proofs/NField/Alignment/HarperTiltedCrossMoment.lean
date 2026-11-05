/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperLocalExponentialMoment

/-!
# The exact frequency covariance of a prime term

Frequency changes rotate the same Haar circle coordinate. Its real-part
covariance is exactly cos(t log q)/(2q), giving the leading drift under
the energy weighting without assuming a Gaussian model.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperTiltedCrossMoment
open scoped BigOperators Topology ComplexConjugate
open MeasureTheory Filter SteinhausMoment HarperEulerIntegral HarperEulerLogComparison
  HarperLocalExponentialMoment

theorem primeTerm_frequency (q : ℕ) (hq : q ≠ 0) (t : ℝ) (ω : PhaseSpace) :
    primeTerm q t ω = primeTerm q 0 ω*Complex.exp (-(t*Real.log q : ℝ)*Complex.I) := by
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have hqR : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have he : Complex.log (q : ℂ)*linePoint (1/2) t =
      Complex.log (q : ℂ)*linePoint (1/2) 0+(t*Real.log q : ℝ)*Complex.I := by
    rw [show (q : ℂ) = ((q : ℝ) : ℂ) from rfl, ← Complex.ofReal_log hqR]
    unfold linePoint
    push_cast
    ring
  simp only [primeTerm, Complex.cpow_def_of_ne_zero hqC]
  rw [he, Complex.exp_add, div_mul_eq_div_div, div_eq_mul_inv,
    ← Complex.exp_neg]
  push_cast
  ring_nf

theorem primeTerm_mixed_re_integrable {q : ℕ} (hq : q ≠ 0) (t : ℝ) :
    Integrable (fun ω => (primeTerm q 0 ω).re*(primeTerm q t ω).re) phaseMeasure := by
  apply Integrable.of_bound ((primeTerm_measurable q 0).re.mul
    (primeTerm_measurable q t).re).aestronglyMeasurable ((q : ℝ)⁻¹)
  apply Eventually.of_forall
  intro ω
  change |(primeTerm q 0 ω).re*(primeTerm q t ω).re| ≤ (q : ℝ)⁻¹
  rw [abs_mul]
  calc
    _ ≤ ‖primeTerm q 0 ω‖*‖primeTerm q t ω‖ := mul_le_mul
      (Complex.abs_re_le_norm _) (Complex.abs_re_le_norm _) (abs_nonneg _) (norm_nonneg _)
    _ = _ := by
      rw [primeTerm_norm hq, primeTerm_norm hq, ← pow_two,
        ← Real.rpow_mul_natCast (Nat.cast_nonneg q)]
      norm_num [Real.rpow_neg_one]

theorem primeTerm_re_im_mean {q : ℕ} (hq : q.Prime) :
    (∫ ω, (primeTerm q 0 ω).re*(primeTerm q 0 ω).im ∂phaseMeasure) = 0 := by
  have he (ω : PhaseSpace) : (primeTerm q 0 ω).re*(primeTerm q 0 ω).im =
      ((primeTerm q 0 ω)^2).im/2 := by simp [pow_two, Complex.mul_im]; ring
  simp_rw [he]
  have him : (∫ ω, ((primeTerm q 0 ω)^2).im ∂phaseMeasure) =
      (∫ ω, (primeTerm q 0 ω)^2 ∂phaseMeasure).im :=
    integral_im (primeTerm_pow_integrable q 0 2)
  rw [integral_div, him,
    primeTerm_pow_mean_zero hq 0 (by norm_num : 0<2)]
  simp

theorem primeTerm_mixed_re_mean {q : ℕ} (hq : q.Prime) (t : ℝ) :
    (∫ ω, (primeTerm q 0 ω).re*(primeTerm q t ω).re ∂phaseMeasure) =
      Real.cos (t*Real.log q)/(2*q) := by
  have hi : Integrable (fun ω => (primeTerm q 0 ω).re*(primeTerm q 0 ω).im) phaseMeasure := by
    have he : (fun ω => (primeTerm q 0 ω).re*(primeTerm q 0 ω).im) =
        (fun ω => ((primeTerm q 0 ω)^2).im/2) := by
      funext ω
      simp [pow_two, Complex.mul_im]
      ring
    rw [he]
    exact (primeTerm_pow_integrable q 0 2).im.div_const 2
  have he (ω : PhaseSpace) : (primeTerm q 0 ω).re*(primeTerm q t ω).re =
      Real.cos (t*Real.log q)*(primeTerm q 0 ω).re^2+
        Real.sin (t*Real.log q)*((primeTerm q 0 ω).re*(primeTerm q 0 ω).im) := by
    rw [primeTerm_frequency q hq.ne_zero t]
    simp only [Complex.mul_re, Complex.exp_re, Complex.exp_im, Complex.mul_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
      zero_sub, add_zero, neg_zero, mul_one, Real.exp_zero,
      one_mul, Real.cos_neg, Real.sin_neg]
    ring
  simp_rw [he]
  rw [integral_add ((primeTerm_re_square_integrable hq.ne_zero 0).const_mul _)
    (hi.const_mul _), integral_const_mul, integral_const_mul,
    primeTerm_re_square_mean hq 0, primeTerm_re_im_mean hq]
  simp only [mul_zero, add_zero]
  ring

end NField.Alignment.HarperTiltedCrossMoment

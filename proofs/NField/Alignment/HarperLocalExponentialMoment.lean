/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperModerateSamples
import Mathlib.Analysis.Complex.Exponential

/-!
# The quadratic coefficient of a local exponential moment

The actual critical-line prime term has vanishing positive complex moments
and real-part variance 1/(2q). An explicit cubic Taylor majorant bounds the
11/5 exponential tilt of its prime-plus-prime-square real sum. The exact
leading coefficient is 121/100; all remaining local terms are bounded by
a fixed multiple of q^(-3/2), uniformly in the frequency. This module proves
the local expectation estimate and all integrability conditions directly.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperLocalExponentialMoment
open scoped BigOperators Topology
open MeasureTheory Filter Asymptotics SteinhausMoment HarperRandomEulerProduct HarperEulerIntegral
  HarperEulerLogComparison HarperModerateSamples CollisionMertensInput

def localArgument (q : ℕ) (t : ℝ) (ω : PhaseSpace) : ℝ :=
  (11/5 : ℝ)*(primeTerm q t ω+(primeTerm q t ω)^2/2).re
def localErrorConstant : ℝ := 10+125*Real.exp 4

theorem localErrorConstant_pos : 0 < localErrorConstant := by
  unfold localErrorConstant
  positivity

theorem exp_quadratic_remainder (x : ℝ) :
    |Real.exp x-(1+x+x^2/2)| ≤ |x|^3*Real.exp |x| := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (x : ℂ) 3
  have he : (Complex.exp (x : ℂ)-∑ m ∈ Finset.range 3, (x : ℂ)^m/(m.factorial : ℂ)) =
      ((Real.exp x-(1+x+x^2/2) : ℝ) : ℂ) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, Nat.factorial_zero,
      Nat.factorial_succ, Nat.cast_one, div_one, zero_add, pow_one]
    rw [← Complex.ofReal_exp]
    push_cast
    norm_num
  rw [he, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs] at h
  exact h

theorem quadratic_argument_bound {z : ℂ} (hz : ‖z‖ ≤ 3/4) :
    |(11/5 : ℝ)*(z+z^2/2).re| ≤ 5*‖z‖ := by
  have hb : |(z^2/2).re| ≤ ‖z‖^2/2 := by
    have h := Complex.abs_re_le_norm (z^2/2)
    simpa only [norm_div, norm_pow, Complex.norm_ofNat] using h
  have ha := Complex.abs_re_le_norm z
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ)<11/5), Complex.add_re]
  have h := abs_add_le z.re (z^2/2).re
  have hs : ‖z‖^2 ≤ ‖z‖ := by nlinarith [norm_nonneg z]
  nlinarith

theorem quadratic_square_bound {z : ℂ} (hz : ‖z‖ ≤ 3/4) :
    ((11/5 : ℝ)*(z+z^2/2).re)^2/2 ≤ (121/50 : ℝ)*z.re^2+10*‖z‖^3 := by
  have ha : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
  have hb : |(z^2/2).re| ≤ ‖z‖^2/2 := by
    have h := Complex.abs_re_le_norm (z^2/2)
    simpa only [norm_div, norm_pow, Complex.norm_ofNat] using h
  have hab : z.re*(z^2/2).re ≤ ‖z‖^3/2 := by
    calc
      _ ≤ |z.re*(z^2/2).re| := le_abs_self _
      _ = |z.re| * |(z^2/2).re| := abs_mul _ _
      _ ≤ ‖z‖*(‖z‖^2/2) := mul_le_mul ha hb (abs_nonneg _) (norm_nonneg _)
      _ = _ := by ring
  have hb2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
  rw [sq_abs] at hb2
  have hr4 : ‖z‖^4 ≤ ‖z‖^3 := by
    have h := mul_le_mul_of_nonneg_right (show ‖z‖ ≤ 1 by linarith) (pow_nonneg (norm_nonneg z) 3)
    nlinarith
  rw [Complex.add_re]
  nlinarith [pow_nonneg (norm_nonneg z) 3]

theorem local_exponential_point_bound {z : ℂ} (hz : ‖z‖ ≤ 3/4) :
    Real.exp ((11/5 : ℝ)*(z+z^2/2).re) ≤
      1+(11/5 : ℝ)*(z+z^2/2).re+(121/50 : ℝ)*z.re^2+localErrorConstant*‖z‖^3 := by
  have hx := quadratic_argument_bound hz
  have hx4 : |(11/5 : ℝ)*(z+z^2/2).re| ≤ 4 := by linarith
  have ht := (abs_le.mp (exp_quadratic_remainder ((11/5 : ℝ)*(z+z^2/2).re))).2
  have he : |(11/5 : ℝ)*(z+z^2/2).re|^3*Real.exp |(11/5 : ℝ)*(z+z^2/2).re| ≤
      125*Real.exp 4*‖z‖^3 := by
    calc
      _ ≤ (5*‖z‖)^3*Real.exp 4 :=
        mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hx 3) (Real.exp_le_exp.mpr hx4)
          (Real.exp_pos _).le (by positivity)
      _ = _ := by ring
  have hs := quadratic_square_bound hz
  unfold localErrorConstant
  linarith

theorem primeTerm_measurable (q : ℕ) (t : ℝ) : Measurable (primeTerm q t) :=
  (steinhaus_measurable q).div_const _

theorem primeTerm_pow_integrable (q : ℕ) (t : ℝ) (k : ℕ) :
    Integrable (fun ω => (primeTerm q t ω)^k) phaseMeasure := by
  have he : (fun ω => (primeTerm q t ω)^k) =
      (fun ω => steinhaus (q^k) ω/((q : ℂ)^(linePoint (1/2) t))^k) := by
    funext ω
    rw [primeTerm, div_pow, steinhaus_pow]
  rw [he]
  exact (steinhaus_integrable _).div_const _

theorem steinhaus_mean_zero {n : ℕ} (hn : n ≠ 0) (hn1 : n ≠ 1) :
    (∫ ω, steinhaus n ω ∂phaseMeasure) = 0 := by
  simpa only [steinhaus_one, star_one, mul_one, if_neg hn1] using
    steinhaus_orthogonality hn (by norm_num : (1 : ℕ)≠0)

theorem primeTerm_pow_mean_zero {q : ℕ} (hq : q.Prime) (t : ℝ) {k : ℕ} (hk : 0 < k) :
    (∫ ω, (primeTerm q t ω)^k ∂phaseMeasure) = 0 := by
  have he : (fun ω => (primeTerm q t ω)^k) =
      (fun ω => steinhaus (q^k) ω/((q : ℂ)^(linePoint (1/2) t))^k) := by
    funext ω
    rw [primeTerm, div_pow, steinhaus_pow]
  rw [he, integral_div, steinhaus_mean_zero (pow_ne_zero _ hq.ne_zero)
    (ne_of_gt (one_lt_pow₀ hq.one_lt hk.ne'))]
  simp

theorem primeTerm_norm_sq {q : ℕ} (hq : q ≠ 0) (t : ℝ) (ω : PhaseSpace) :
    ‖primeTerm q t ω‖^2 = (q : ℝ)⁻¹ := by
  rw [primeTerm_norm hq, ← Real.rpow_mul_natCast (Nat.cast_nonneg q)]
  norm_num [Real.rpow_neg_one]

theorem primeTerm_norm_cube {q : ℕ} (hq : q ≠ 0) (t : ℝ) (ω : PhaseSpace) :
    ‖primeTerm q t ω‖^3 = (q : ℝ)^(-(3/2 : ℝ)) := by
  rw [primeTerm_norm hq, ← Real.rpow_mul_natCast (Nat.cast_nonneg q)]
  norm_num

theorem primeTerm_re_square_identity {q : ℕ} (hq : q ≠ 0) (t : ℝ) (ω : PhaseSpace) :
    (primeTerm q t ω).re^2 = ((q : ℝ)⁻¹+((primeTerm q t ω)^2).re)/2 := by
  have h := primeTerm_norm_sq hq t ω
  rw [Complex.sq_norm, Complex.normSq_apply] at h
  simp only [pow_two, Complex.mul_re]
  nlinarith

theorem primeTerm_re_square_integrable {q : ℕ} (hq : q ≠ 0) (t : ℝ) :
    Integrable (fun ω => (primeTerm q t ω).re^2) phaseMeasure := by
  simp_rw [primeTerm_re_square_identity hq]
  exact ((integrable_const _).add (primeTerm_pow_integrable q t 2).re).div_const _

theorem primeTerm_re_square_mean {q : ℕ} (hq : q.Prime) (t : ℝ) :
    (∫ ω, (primeTerm q t ω).re^2 ∂phaseMeasure) = (q : ℝ)⁻¹/2 := by
  have hi : Integrable (fun ω => ((primeTerm q t ω)^2).re) phaseMeasure :=
    (primeTerm_pow_integrable q t 2).re
  have he : (∫ ω, ((primeTerm q t ω)^2).re ∂phaseMeasure) =
      (∫ ω, (primeTerm q t ω)^2 ∂phaseMeasure).re := integral_re (primeTerm_pow_integrable q t 2)
  simp_rw [primeTerm_re_square_identity hq.ne_zero]
  rw [integral_div, integral_add (integrable_const _) hi,
    he, primeTerm_pow_mean_zero hq t (by norm_num : 0<2)]
  simp

theorem localArgument_measurable (q : ℕ) (t : ℝ) : Measurable (localArgument q t) :=
  (Complex.continuous_re.measurable.comp ((primeTerm_measurable q t).add
    (((primeTerm_measurable q t).pow_const 2).div_const 2))).const_mul _

theorem localArgument_integrable (q : ℕ) (t : ℝ) : Integrable (localArgument q t) phaseMeasure := by
  have hi : Integrable (primeTerm q t) phaseMeasure := by simpa using primeTerm_pow_integrable q t 1
  exact (hi.add ((primeTerm_pow_integrable q t 2).div_const 2)).re.const_mul _

theorem localArgument_mean {q : ℕ} (hq : q.Prime) (t : ℝ) :
    (∫ ω, localArgument q t ω ∂phaseMeasure) = 0 := by
  have hi : Integrable (primeTerm q t) phaseMeasure := by simpa using primeTerm_pow_integrable q t 1
  have hm : (∫ ω, primeTerm q t ω ∂phaseMeasure) = 0 := by
    simpa only [pow_one] using primeTerm_pow_mean_zero hq t (by norm_num : 0<1)
  have hi2 : Integrable (fun ω => (primeTerm q t ω)^2/2) phaseMeasure :=
    (primeTerm_pow_integrable q t 2).div_const 2
  have he : (∫ ω, (primeTerm q t ω+(primeTerm q t ω)^2/2).re ∂phaseMeasure) =
      (∫ ω, primeTerm q t ω+(primeTerm q t ω)^2/2 ∂phaseMeasure).re := integral_re (hi.add hi2)
  unfold localArgument
  rw [integral_const_mul, he,
    integral_add hi hi2, integral_div,
    hm, primeTerm_pow_mean_zero hq t (by norm_num : 0<2)]
  simp

theorem localArgument_abs_le_four {q : ℕ} (hq : q.Prime) (t : ℝ) (ω : PhaseSpace) :
    |localArgument q t ω| ≤ 4 := by
  have h := quadratic_argument_bound (primeTerm_norm_le hq t ω)
  have hn := primeTerm_norm_le hq t ω
  change |(11/5 : ℝ)*(primeTerm q t ω+(primeTerm q t ω)^2/2).re| ≤ 4
  linarith

theorem localExponential_integrable {q : ℕ} (hq : q.Prime) (t : ℝ) :
    Integrable (fun ω => Real.exp (localArgument q t ω)) phaseMeasure := by
  apply Integrable.of_bound (Real.continuous_exp.measurable.comp
    (localArgument_measurable q t)).aestronglyMeasurable (Real.exp 4)
  apply Eventually.of_forall
  intro ω
  dsimp only [Function.comp_apply]
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_exp.mpr ((le_abs_self _).trans (localArgument_abs_le_four hq t ω))

theorem local_exponential_mean_bound {q : ℕ} (hq : q.Prime) (t : ℝ) :
    (∫ ω, Real.exp (localArgument q t ω) ∂phaseMeasure) ≤
      1+(121/100 : ℝ)*(q : ℝ)⁻¹+localErrorConstant*(q : ℝ)^(-(3/2 : ℝ)) := by
  have hi1 : Integrable (fun ω => 1+localArgument q t ω) phaseMeasure :=
    (integrable_const (1 : ℝ)).add (localArgument_integrable q t)
  have hi2 : Integrable (fun ω => (121/50 : ℝ)*(primeTerm q t ω).re^2) phaseMeasure :=
    (primeTerm_re_square_integrable hq.ne_zero t).const_mul (121/50 : ℝ)
  have hi : Integrable (fun ω => 1+localArgument q t ω+(121/50 : ℝ)*(primeTerm q t ω).re^2) phaseMeasure :=
    hi1.add hi2
  calc
    _ ≤ ∫ ω, 1+localArgument q t ω+(121/50 : ℝ)*(primeTerm q t ω).re^2+
        localErrorConstant*(q : ℝ)^(-(3/2 : ℝ)) ∂phaseMeasure := by
      apply integral_mono (localExponential_integrable hq t) (hi.add (integrable_const _))
      intro ω
      have h := local_exponential_point_bound (primeTerm_norm_le hq t ω)
      rw [primeTerm_norm_cube hq.ne_zero] at h
      exact h
    _ = _ := by
      rw [integral_add hi (integrable_const _),
        integral_add hi1 hi2,
        integral_add (integrable_const (1 : ℝ)) (localArgument_integrable q t),
        integral_const_mul, localArgument_mean hq t, primeTerm_re_square_mean hq t]
      simp only [integral_const, probReal_univ, one_smul, add_zero]
      ring

theorem local_exponential_mean_exp_bound {q : ℕ} (hq : q.Prime) (t : ℝ) :
    (∫ ω, Real.exp (localArgument q t ω) ∂phaseMeasure) ≤
      Real.exp ((121/100 : ℝ)*(q : ℝ)⁻¹+localErrorConstant*(q : ℝ)^(-(3/2 : ℝ))) := by
  have h := Real.add_one_le_exp ((121/100 : ℝ)*(q : ℝ)⁻¹+localErrorConstant*(q : ℝ)^(-(3/2 : ℝ)))
  have hb := local_exponential_mean_bound hq t
  linarith

end NField.Alignment.HarperLocalExponentialMoment

/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionPotentialMoments
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Quadratic growth of finite Lr norms

One fixed exponential moment of sqrt(abs(Y)) controls all finite powers.
The bound uses the actual measure-theoretic lpNorm and is uniform for
the continuous cutoffs as well as the limiting potential.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionMomentNormBounds

open scoped Classical ENNReal
open MeasureTheory ProfiniteRemainderMeasure CollisionRemainderDynamics
open CollisionPotentialHilbert CollisionPotentialConvergence CollisionPotentialMoments

theorem power_bound_by_root_exponential (x : ℝ) {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r) :
    |x|^r ≤ (2*r/t)^(2*r)*Real.exp (t*Real.sqrt |x|) := by
  have h := ProbabilityTheory.rpow_abs_le_mul_exp_abs (Real.sqrt |x|)
    (show 0 ≤ 2*r by linarith) ht.ne'
  rw [abs_root_rpow] at h
  simpa only [abs_of_pos ht,abs_of_nonneg (Real.sqrt_nonneg _)] using h

theorem small_power_bound {B r : ℝ} (hB : 0 ≤ B) (hr : 1 ≤ r) :
    B^(1/r) ≤ max B 1 := by
  have hr0 : 0 < r := by linarith
  have hi : 0 ≤ 1/r := by positivity
  have hi1 : 1/r ≤ 1 := (div_le_one hr0).mpr hr
  by_cases hB1 : 1 ≤ B
  · exact (Real.rpow_le_self_of_one_le hB1 hi1).trans (le_max_left _ _)
  · exact (Real.rpow_le_one hB (le_of_not_ge hB1) hi).trans (le_max_right _ _)

theorem lpNorm_bound_of_root_exponential {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (F : Ω → ℝ) (hF : AEStronglyMeasurable F μ)
    {t r B : ℝ} (ht : 0 < t) (hr : 1 ≤ r) (hB : 0 ≤ B)
    (hPow : Integrable (fun x => |F x|^r) μ)
    (hExp : Integrable (fun x => Real.exp (t*Real.sqrt |F x|)) μ)
    (hInt : (∫ x, Real.exp (t*Real.sqrt |F x|) ∂μ) ≤ B) :
    lpNorm F (ENNReal.ofReal r) μ ≤ ((4/t^2)*max B 1)*r^2 := by
  have hr0 : 0 < r := by linarith
  have ha : 0 ≤ 2*r/t := by positivity
  have hcoef : 0 ≤ (2*r/t)^(2*r) := Real.rpow_nonneg ha _
  have hpow := integral_mono hPow (hExp.const_mul ((2*r/t)^(2*r)))
    (fun x => power_bound_by_root_exponential (F x) ht hr0.le)
  rw [integral_const_mul] at hpow
  have hb : (∫ x, |F x|^r ∂μ) ≤ (2*r/t)^(2*r)*B :=
    hpow.trans (mul_le_mul_of_nonneg_left hInt hcoef)
  have he : (((2*r/t)^(2*r))*B)^(1/r)=(2*r/t)^2*B^(1/r) := by
    rw [Real.mul_rpow hcoef hB,← Real.rpow_mul ha]
    have hex : (2*r)*(1/r)=2 := by field_simp
    rw [hex,Real.rpow_two]
  calc
    _ = (∫ x, |F x|^r ∂μ)^(1/r) := by
      rw [lpNorm_eq_integral_norm_rpow_toReal (by simpa using hr0) ENNReal.ofReal_ne_top hF,
        ENNReal.toReal_ofReal hr0.le]
      simp only [Real.norm_eq_abs,one_div]
    _ ≤ (((2*r/t)^(2*r))*B)^(1/r) :=
      Real.rpow_le_rpow (integral_nonneg (fun x => Real.rpow_nonneg (abs_nonneg _) _)) hb (by positivity)
    _ = (2*r/t)^2*B^(1/r) := he
    _ ≤ (2*r/t)^2*max B 1 := mul_le_mul_of_nonneg_left (small_power_bound hB hr) (sq_nonneg _)
    _ = _ := by ring

theorem potential_quadratic_norm_bound : ∃ K : ℝ, 0 < K ∧ ∀ r : ℝ, 1 ≤ r →
    (lpNorm collisionPotential (ENNReal.ofReal r) phaseHaar ≤ K*r^2) ∧
    (∀ M : ℕ, lpNorm (potentialMap collisionWeight M) (ENNReal.ofReal r) phaseHaar ≤ K*r^2) := by
  let t : ℝ := Real.pi/2
  have ht : 0 < t := by dsimp [t]; positivity
  obtain ⟨B,hB,hY,hM⟩ := potential_exponential_moments (c := t) (by dsimp [t]; linarith [Real.pi_pos])
  have hmax : 0 < max B 1 := (by norm_num : (0 : ℝ) < 1).trans_le (le_max_right _ _)
  refine ⟨(4/t^2)*max B 1,by positivity,?_⟩
  intro r hr
  obtain ⟨hPowY,hPowM⟩ := potential_finite_moments (r := r) (by linarith)
  exact ⟨lpNorm_bound_of_root_exponential collisionPotential (Lp.aestronglyMeasurable collisionPotential)
    ht hr hB.le hPowY hY.1 hY.2,
    fun M => lpNorm_bound_of_root_exponential (potentialMap collisionWeight M)
      (potentialMap collisionWeight M).continuous.measurable.aestronglyMeasurable
      ht hr hB.le (hPowM M) (hM M).1 (hM M).2⟩

end NField.Alignment.CollisionMomentNormBounds

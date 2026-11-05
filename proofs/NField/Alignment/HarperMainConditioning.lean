/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperMainIntegral
import NField.Alignment.HarperSieveScales

/-!
# The main integral under the actual conditioning weights

The proved short-interval sieve bound controls the main average at the
manuscript parameters. Monotonicity and three-quarter homogeneity hold
for the actual nonnegative box weights, including zero-weight boxes.
The random conditional moment is reduced to the finite inverse integral,
with every scale condition discharged and the smoothing error retained.
The downstream HarperSpectralConditioning module supplies the actual
Dirichlet-series Parseval step. The random low-moment saving remains open.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperMainConditioning

open scoped BigOperators
open MeasureTheory SteinhausMoment HarperMainIntegral HarperRoughSmoothing
  HarperSmoothIntervals HarperSieveApplications
open Filter HarperRoundedCutoff HarperSieveScales HarperSmoothingConditioning
  HarperActualConditioning HarperWeightedConditioning HarperConditioningFrequencies

theorem inverse_endpoint {x : ℝ} (hx : 0 < x) :
    x/smoothCutoff x = x^(1-1/Real.log (Real.log x)) := by
  rw [smoothCutoff, Real.rpow_sub hx, Real.rpow_one]

theorem eventual_smoothRoughAverage_le_mainIntegral : ∀ᶠ x : ℝ in atTop,
    ∀ ω : PhaseSpace,
      smoothRoughAverage x (primeCutoff x) (smoothCutoff x) (smoothingScale x) (fun _ => 1) ω ≤
        (3/Real.log (primeCutoff x))*smoothMainIntegral x (primeCutoff x) (smoothCutoff x) ω := by
  filter_upwards [eventual_roughShortWeight_bound, eventual_cutoff_hierarchy,
    eventually_gt_atTop (0 : ℝ)] with x hb hh hx
  exact smoothRoughAverage_le_mainIntegral (Real.rpow_pos_of_pos hx _) hh.2.le (Real.exp_pos _) hb

theorem eventual_smoothRoughAverage_le_inverseIntegral : ∀ᶠ x : ℝ in atTop,
    ∀ ω : PhaseSpace,
      smoothRoughAverage x (primeCutoff x) (smoothCutoff x) (smoothingScale x) (fun _ => 1) ω ≤
        (3*x/Real.log (primeCutoff x))*smoothInverseIntegral x (primeCutoff x) (smoothCutoff x) ω := by
  filter_upwards [eventual_roughShortWeight_bound, eventual_cutoff_hierarchy,
    eventually_gt_atTop (0 : ℝ)] with x hb hh hx
  intro ω
  calc
    _ ≤ ((3/Real.log (primeCutoff x))*x)*
        smoothInverseIntegral x (primeCutoff x) (smoothCutoff x) ω :=
      smoothRoughAverage_le_inverseIntegral (Real.rpow_pos_of_pos hx _)
        hh.2.le (Real.exp_pos _) hb ω
    _ = _ := by ring

theorem boxMoment_mono {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (c1 c2 : Coefficients p) (i : Boxes p) {F G : PhaseSpace → ℝ}
    (hF : Integrable F phaseMeasure) (hG : Integrable G phaseMeasure) (hFG : ∀ ω, F ω ≤ G ω) :
    boxMoment p c1 c2 i F ≤ boxMoment p c1 c2 i G :=
  integral_mono (boxMoment_integrable hell c1 c2 i hF) (boxMoment_integrable hell c1 c2 i hG)
    (fun ω => mul_le_mul_of_nonneg_right (hFG ω) (smoothBox_nonneg hell c1 c2 i _))

theorem boxMoment_const_mul (p : ℕ) (c1 c2 : Coefficients p) (i : Boxes p)
    (C : ℝ) (F : PhaseSpace → ℝ) :
    boxMoment p c1 c2 i (fun ω => C*F ω) = C*boxMoment p c1 c2 i F := by
  unfold boxMoment
  simp_rw [mul_assoc]
  exact integral_const_mul _ _

theorem boxConditioning_mono {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (c1 c2 : Coefficients p) {F G : PhaseSpace → ℝ}
    (hF : Integrable F phaseMeasure) (hG : Integrable G phaseMeasure)
    (hF0 : ∀ ω, 0 ≤ F ω) (hFG : ∀ ω, F ω ≤ G ω) :
    boxConditioning p c1 c2 F ≤ boxConditioning p c1 c2 G := by
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (boxMoment_nonneg hell c1 c2 i hF0)
      (boxMoment_mono hell c1 c2 i hF hG hFG) (by norm_num : (0 : ℝ) ≤ 3/4))
    (Real.rpow_nonneg (randomWeight_nonneg hell c1 c2 i) _)

theorem boxConditioning_const_mul {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (c1 c2 : Coefficients p) {C : ℝ} (hC : 0 ≤ C) (F : PhaseSpace → ℝ)
    (hF : ∀ ω, 0 ≤ F ω) :
    boxConditioning p c1 c2 (fun ω => C*F ω) = C^(3/4 : ℝ)*boxConditioning p c1 c2 F := by
  unfold boxConditioning conditioningSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only
  rw [boxMoment_const_mul, Real.mul_rpow hC (boxMoment_nonneg hell c1 c2 i hF)]
  ring

theorem conditioning_le_inverseIntegral {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (c1 c2 : Coefficients p) {x P y X C : ℝ} (hy : 0 < y) (hyx : y ≤ x)
    (hX : 0 < X) (hC : 0 ≤ C)
    (hshort : ∀ t : ℝ, y ≤ t → roughShortWeight t P X ≤ C) :
    boxConditioning p c1 c2 (smoothRoughAverage x P y X (fun _ => 1)) ≤
      (C*x)^(3/4 : ℝ)*boxConditioning p c1 c2 (smoothInverseIntegral x P y) := by
  have hx : 0 ≤ x := hy.le.trans hyx
  have h := boxConditioning_mono hell c1 c2 (smoothRoughAverage_integrable hx hX P y _)
    ((smoothInverseIntegral_integrable hy hyx P).const_mul (C*x))
    (smoothRoughAverage_nonneg hX x P y _) (smoothRoughAverage_le_inverseIntegral hy hyx hX hshort)
  rwa [boxConditioning_const_mul hell c1 c2 (mul_nonneg hC hx) _
    (smoothInverseIntegral_nonneg hy hyx P)] at h

theorem eventual_conditioning_le_inverseIntegral : ∀ᶠ p : ℕ in atTop,
    ∀ c1 c2 : Coefficients p,
      boxConditioning p c1 c2
        (smoothRoughAverage ((p : ℝ)-1) (primeCutoff ((p : ℝ)-1))
          (smoothCutoff ((p : ℝ)-1)) (smoothingScale ((p : ℝ)-1)) (fun _ => 1)) ≤
      (3*((p : ℝ)-1)/Real.log (primeCutoff ((p : ℝ)-1)))^(3/4 : ℝ)*
        boxConditioning p c1 c2
          (smoothInverseIntegral ((p : ℝ)-1) (primeCutoff ((p : ℝ)-1))
            (smoothCutoff ((p : ℝ)-1))) := by
  filter_upwards [base_minus_one_tendsto.eventually eventual_roughShortWeight_bound,
    base_minus_one_tendsto.eventually eventual_cutoff_hierarchy,
    (cutoffLog_tendsto.comp base_minus_one_tendsto).eventually_gt_atTop 0,
    base_minus_one_tendsto.eventually_gt_atTop 0] with p hb hh hell hx
  intro c1 c2
  have hlog : 0 < Real.log (primeCutoff ((p : ℝ)-1)) := by rwa [log_primeCutoff]
  calc
    _ ≤ ((3/Real.log (primeCutoff ((p : ℝ)-1)))*((p : ℝ)-1))^(3/4 : ℝ)*
        boxConditioning p c1 c2
          (smoothInverseIntegral ((p : ℝ)-1) (primeCutoff ((p : ℝ)-1))
            (smoothCutoff ((p : ℝ)-1))) :=
      conditioning_le_inverseIntegral hell c1 c2 (Real.rpow_pos_of_pos hx _)
        hh.2.le (Real.exp_pos _) (div_nonneg (by norm_num) hlog.le) hb
    _ = _ := by rw [div_mul_eq_mul_div]

theorem eventual_actual_random_main_integral_with_error : ∀ᶠ p : ℕ in atTop,
    actualRandomConditioning p ≤ (2 : ℝ)^(3/4 : ℝ) *
      ((3*((p : ℝ)-1)/Real.log (primeCutoff ((p : ℝ)-1)))^(3/4 : ℝ)*
        boxConditioning p (firstCoefficient ((p : ℝ)-1)) (secondCoefficient ((p : ℝ)-1))
          (smoothInverseIntegral ((p : ℝ)-1) (primeCutoff ((p : ℝ)-1))
            (smoothCutoff ((p : ℝ)-1))) +
       (roughSmoothingError ((p : ℝ)-1) (primeCutoff ((p : ℝ)-1))
          (smoothCutoff ((p : ℝ)-1)) (smoothingScale ((p : ℝ)-1)))^(3/4 : ℝ)) := by
  filter_upwards [eventual_actual_random_smoothing, eventual_conditioning_le_inverseIntegral]
    with p hs hm
  exact hs.trans (mul_le_mul_of_nonneg_left (add_le_add (hm _ _) le_rfl)
    (Real.rpow_nonneg (by norm_num) _))

theorem eventual_actual_random_main_integral : ∀ᶠ p : ℕ in atTop,
    actualRandomConditioning p ≤ (2 : ℝ)^(3/4 : ℝ) *
      ((3*((p : ℝ)-1)/Real.log (primeCutoff ((p : ℝ)-1)))^(3/4 : ℝ)*
        boxConditioning p (firstCoefficient ((p : ℝ)-1)) (secondCoefficient ((p : ℝ)-1))
          (smoothInverseIntegral ((p : ℝ)-1) (primeCutoff ((p : ℝ)-1))
            (smoothCutoff ((p : ℝ)-1))) +
       (4*((p : ℝ)-1)/Real.log (primeCutoff ((p : ℝ)-1)))^(3/4 : ℝ)) := by
  filter_upwards [eventual_actual_random_smoothing_sieved, eventual_conditioning_le_inverseIntegral]
    with p hs hm
  exact hs.trans (mul_le_mul_of_nonneg_left (add_le_add (hm _ _) le_rfl)
    (Real.rpow_nonneg (by norm_num) _))

end NField.Alignment.HarperMainConditioning

/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperExtremeGrid

/-!
# A negligible extreme-sample error at the manuscript scale

The full central grid reduces to its moderate samples through the actual
box functional. The uniform extreme-grid expectation bound gives exponent
297/400 after the three-quarter power. With the literal x/log(P) coefficient,
the normalized exponent is -3/400. Thus the complete extreme contribution
is little-o of the manuscript target, including the actual rounded cutoff
and x=p-1. The actual random-conditioning consumer retains all four errors.
The moderate sharp-conditioning passage and central low-moment saving remain open.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperExtremeScales
open scoped BigOperators Topology
open MeasureTheory Filter Asymptotics SteinhausMoment HarperEulerDiscretization
  HarperEulerGridComparison HarperFrequencyScales HarperFrequencyTail HarperFrequencyIntervals
  HarperFrequencyConditioning HarperSmoothingConditioning HarperActualConditioning
  HarperConditioningFrequencies HarperRoundedCutoff HarperConditioningDecay HarperRoughSmoothing
  HarperExtremeGrid HarperDiscretizationScales

def moderateCentralConditioning (p : ℕ) (c1 c2 : Coefficients p) (P : ℝ) : ℝ :=
  ∑ v ∈ centralFrequencies (frequencyCutoff P),
    frequencyWeight (3/2) v*boxConditioning p c1 c2 (moderateGridEnergy P v)
def extremeFractionalError (P : ℝ) : ℝ :=
  ∑ v ∈ centralFrequencies (frequencyCutoff P), frequencyWeight (3/2) v*
    (∫ ω, extremeGridEnergy P v ω ∂phaseMeasure)^(3/4 : ℝ)
def extremeErrorContribution (x P : ℝ) : ℝ :=
  (48*x/(Real.pi*Real.log P))^(3/4 : ℝ)*extremeFractionalError P

theorem extremeFractionalError_nonneg {P : ℝ} (hD : 0 ≤ gridScale P) : 0 ≤ extremeFractionalError P :=
  Finset.sum_nonneg (fun v _ => mul_nonneg (frequencyWeight_nonneg _ _)
    (Real.rpow_nonneg (integral_nonneg (extremeGridEnergy_nonneg hD v)) _))

theorem discreteCentralConditioning_le_moderate {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (c1 c2 : Coefficients p) {P : ℝ} (hD : 0 ≤ gridScale P) :
    discreteCentralConditioning p c1 c2 P ≤
      moderateCentralConditioning p c1 c2 P+extremeFractionalError P := by
  unfold discreteCentralConditioning moderateCentralConditioning extremeFractionalError
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro v _
  exact (mul_le_mul_of_nonneg_left (discreteEnergy_conditioning_split hell c1 c2 hD v)
    (frequencyWeight_nonneg _ _)).trans_eq (mul_add _ _ _)

theorem eventual_actual_random_moderate_with_errors : ∀ᶠ p : ℕ in atTop,
    actualRandomConditioning p ≤ (2 : ℝ)^(3/4 : ℝ)*
      ((48*((p : ℝ)-1)/(Real.pi*Real.log (primeCutoff ((p : ℝ)-1))))^(3/4 : ℝ)*
        moderateCentralConditioning p (firstCoefficient ((p : ℝ)-1)) (secondCoefficient ((p : ℝ)-1))
          (primeCutoff ((p : ℝ)-1)) +
       extremeErrorContribution ((p : ℝ)-1) (primeCutoff ((p : ℝ)-1)) +
       gridErrorContribution ((p : ℝ)-1) (primeCutoff ((p : ℝ)-1)) +
       frequencyTailContribution ((p : ℝ)-1) (primeCutoff ((p : ℝ)-1)) +
       (roughSmoothingError ((p : ℝ)-1) (primeCutoff ((p : ℝ)-1))
         (smoothCutoff ((p : ℝ)-1)) (smoothingScale ((p : ℝ)-1)))^(3/4 : ℝ)) := by
  filter_upwards [eventual_actual_random_discrete_with_errors,
    (cutoffLog_tendsto.comp base_minus_one_tendsto).eventually_gt_atTop 0,
    base_minus_one_tendsto.eventually_gt_atTop 0] with p hm hell hx
  have hP : 0 < Real.log (primeCutoff ((p : ℝ)-1)) := by rwa [log_primeCutoff]
  have hD : 0 ≤ gridScale (primeCutoff ((p : ℝ)-1)) := Real.rpow_nonneg hP.le _
  have h := discreteCentralConditioning_le_moderate hell
    (firstCoefficient ((p : ℝ)-1)) (secondCoefficient ((p : ℝ)-1)) hD
  have hh := hm.trans (mul_le_mul_of_nonneg_left (add_le_add
    (add_le_add (add_le_add (mul_le_mul_of_nonneg_left h (by positivity)) le_rfl) le_rfl) le_rfl)
    (Real.rpow_nonneg (by norm_num) _))
  convert! hh using 1
  unfold extremeErrorContribution
  ring

theorem eventual_extremeFractionalError_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ P : ℝ in atTop,
    extremeFractionalError P ≤ C*(Real.log P)^(297/400 : ℝ) := by
  obtain ⟨C,hC,hb⟩ := eventual_extremeGridEnergy_bound
  let W := ∑' v : ℤ, frequencyWeight (3/2) v
  have hW : 0 ≤ W := tsum_nonneg (fun _ => frequencyWeight_nonneg _ _)
  refine ⟨C^(3/4 : ℝ)*W, by positivity, ?_⟩
  filter_upwards [hb, Real.tendsto_log_atTop.eventually_ge_atTop 0] with P hbound hP
  have hp (v : ℤ) : (∫ ω, extremeGridEnergy P v ω ∂phaseMeasure)^(3/4 : ℝ) ≤
      C^(3/4 : ℝ)*(Real.log P)^(297/400 : ℝ) := by
    have h := Real.rpow_le_rpow (integral_nonneg (extremeGridEnergy_nonneg (Real.rpow_nonneg hP _) v)) (hbound v)
      (by norm_num : (0 : ℝ) ≤ 3/4)
    rw [Real.mul_rpow hC.le (Real.rpow_nonneg hP _), ← Real.rpow_mul hP] at h
    norm_num at h
    exact h
  calc
    _ ≤ (C^(3/4 : ℝ)*(Real.log P)^(297/400 : ℝ))*
        ∑ v ∈ centralFrequencies (frequencyCutoff P), frequencyWeight (3/2) v := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun v _ => (mul_le_mul_of_nonneg_left (hp v)
        (frequencyWeight_nonneg _ _)).trans_eq (mul_comm _ _))
    _ ≤ (C^(3/4 : ℝ)*(Real.log P)^(297/400 : ℝ))*W :=
      mul_le_mul_of_nonneg_left
        ((frequencyWeight_summable (by norm_num : (1 : ℝ) < 3/2)).sum_le_tsum _
          (fun _ _ => frequencyWeight_nonneg _ _)) (by positivity)
    _ = _ := by ring

theorem extreme_scale_identity {x L : ℝ} (hx : 0 ≤ x) (hL : 0 < L) :
    (48*x/(Real.pi*L))^(3/4 : ℝ)*L^(297/400 : ℝ) =
      (48/Real.pi)^(3/4 : ℝ)*x^(3/4 : ℝ)*L^(-(3/400 : ℝ)) := by
  have he : 48*x/(Real.pi*L) = ((48/Real.pi)*x)*L^(-(1 : ℝ)) := by
    rw [Real.rpow_neg_one]
    ring
  rw [he, Real.mul_rpow (by positivity) (Real.rpow_nonneg hL.le _),
    Real.mul_rpow (by positivity) hx, ← Real.rpow_mul hL.le]
  rw [mul_assoc, ← Real.rpow_add hL]
  norm_num

theorem extremeErrorContribution_nonneg {x P : ℝ} (hx : 0 ≤ x) (hP : 0 < Real.log P) :
    0 ≤ extremeErrorContribution x P :=
  mul_nonneg (Real.rpow_nonneg (by positivity) _) (extremeFractionalError_nonneg (Real.rpow_nonneg hP.le _))

theorem extremeErrorContribution_isBigO :
    (fun x => extremeErrorContribution x (primeCutoff x)) =O[atTop]
      (fun x => x^(3/4 : ℝ)*(cutoffLog x)^(-(1/300 : ℝ))) := by
  obtain ⟨C,hC,hb⟩ := eventual_extremeFractionalError_bound
  apply IsBigO.of_bound (C*(48/Real.pi)^(3/4 : ℝ))
  filter_upwards [HarperSmoothDivisor.primeCutoff_tendsto.eventually hb, cutoffLog_tendsto.eventually_ge_atTop 1,
    eventually_gt_atTop (0 : ℝ)] with x hbound hL hx
  have hP : 0 < Real.log (primeCutoff x) := by rw [log_primeCutoff]; linarith
  rw [Real.norm_of_nonneg (extremeErrorContribution_nonneg hx.le hP),
    Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (48*x/(Real.pi*Real.log (primeCutoff x)))^(3/4 : ℝ)*
        (C*(Real.log (primeCutoff x))^(297/400 : ℝ)) :=
      mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg (by positivity) _)
    _ = (C*(48/Real.pi)^(3/4 : ℝ))*
        (x^(3/4 : ℝ)*(cutoffLog x)^(-(3/400 : ℝ))) := by
      rw [mul_left_comm _ C, extreme_scale_identity hx.le hP, log_primeCutoff]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)

theorem extremeErrorContribution_isLittleO :
    (fun x => extremeErrorContribution x (primeCutoff x)) =o[atTop] targetScale :=
  extremeErrorContribution_isBigO.trans_isLittleO
    ((isBigO_refl (fun x : ℝ => x^(3/4 : ℝ)) atTop).mul_isLittleO inverse_cutoff_power_isLittleO)

theorem prime_square_extremeErrorContribution_isLittleO :
    (fun p : ℕ => extremeErrorContribution ((p : ℝ)-1) (primeCutoff ((p : ℝ)-1))) =o[atTop]
      (fun p : ℕ => targetScale ((p : ℝ)-1)) :=
  extremeErrorContribution_isLittleO.comp_tendsto base_minus_one_tendsto

end NField.Alignment.HarperExtremeScales

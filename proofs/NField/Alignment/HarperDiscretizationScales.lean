/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperEulerGridComparison

/-!
# Discrete central conditioning and a negligible grid error

The actual random-conditioning consumer is reduced to its finite discrete
central sum, retaining all constants and the literal grid, frequency and
smoothing errors. The uniform grid mean-square bound gives exponent
147/200 after the fractional power. After normalization the logarithmic
power is -3/200, so the full weighted grid error is little-o of the target,
including the actual rounded cutoff and x=p-1. Strengthened conditioning
and the central low-moment saving remain open.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperDiscretizationScales
open scoped BigOperators Topology
open MeasureTheory Filter Asymptotics SteinhausMoment HarperEulerDiscretization
  HarperEulerGridComparison HarperFrequencyScales HarperFrequencyTail HarperFrequencyIntervals
  HarperFrequencyConditioning HarperSmoothingConditioning HarperActualConditioning
  HarperConditioningFrequencies HarperRoundedCutoff HarperConditioningDecay HarperRoughSmoothing

def discreteCentralConditioning (p : ℕ) (c1 c2 : Coefficients p) (P : ℝ) : ℝ :=
  ∑ v ∈ centralFrequencies (frequencyCutoff P),
    frequencyWeight (3/2) v*boxConditioning p c1 c2 (discreteEnergy P v)
def gridFractionalError (P : ℝ) : ℝ :=
  ∑ v ∈ centralFrequencies (frequencyCutoff P), frequencyWeight (3/2) v*
    (∫ ω, gridError P v ω ∂phaseMeasure)^(3/4 : ℝ)
def gridErrorContribution (x P : ℝ) : ℝ :=
  (48*x/(Real.pi*Real.log P))^(3/4 : ℝ)*gridFractionalError P

theorem gridFractionalError_nonneg (P : ℝ) : 0 ≤ gridFractionalError P :=
  Finset.sum_nonneg (fun v _ => mul_nonneg (frequencyWeight_nonneg _ _)
    (Real.rpow_nonneg (integral_nonneg (gridError_nonneg P v)) _))

theorem actual_centralConditioning_le_discrete {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (c1 c2 : Coefficients p) :
    centralConditioning p c1 c2 (primeCutoff ((p : ℝ)-1)) ≤ (2 : ℝ)^(3/4 : ℝ)*
      (discreteCentralConditioning p c1 c2 (primeCutoff ((p : ℝ)-1))+
        gridFractionalError (primeCutoff ((p : ℝ)-1))) := by
  unfold centralConditioning discreteCentralConditioning gridFractionalError
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  exact (mul_le_mul_of_nonneg_left (actual_unitEnergy_conditioning_le_discrete hell c1 c2 v)
    (frequencyWeight_nonneg _ _)).trans_eq (by ring)

theorem discretization_coefficient {x P : ℝ} (hx : 0 ≤ x) (hP : 0 < Real.log P) :
    (3*x/(2*Real.pi*Real.log P))^(3/4 : ℝ)*(16 : ℝ)^(3/4 : ℝ)*(2 : ℝ)^(3/4 : ℝ) =
      (48*x/(Real.pi*Real.log P))^(3/4 : ℝ) := by
  rw [← Real.mul_rpow (by positivity : 0 ≤ 3*x/(2*Real.pi*Real.log P)) (by norm_num),
    ← Real.mul_rpow (by positivity) (by norm_num)]
  congr 1
  field_simp
  ring

theorem eventual_actual_random_discrete_with_errors : ∀ᶠ p : ℕ in atTop,
    actualRandomConditioning p ≤ (2 : ℝ)^(3/4 : ℝ)*
      ((48*((p : ℝ)-1)/(Real.pi*Real.log (primeCutoff ((p : ℝ)-1))))^(3/4 : ℝ)*
        discreteCentralConditioning p (firstCoefficient ((p : ℝ)-1)) (secondCoefficient ((p : ℝ)-1))
          (primeCutoff ((p : ℝ)-1)) +
       gridErrorContribution ((p : ℝ)-1) (primeCutoff ((p : ℝ)-1)) +
       frequencyTailContribution ((p : ℝ)-1) (primeCutoff ((p : ℝ)-1)) +
       (roughSmoothingError ((p : ℝ)-1) (primeCutoff ((p : ℝ)-1))
         (smoothCutoff ((p : ℝ)-1)) (smoothingScale ((p : ℝ)-1)))^(3/4 : ℝ)) := by
  filter_upwards [eventual_actual_random_localized_with_error,
    (cutoffLog_tendsto.comp base_minus_one_tendsto).eventually_gt_atTop 0,
    base_minus_one_tendsto.eventually_gt_atTop 0] with p hm hell hx
  have hP : 0 < Real.log (primeCutoff ((p : ℝ)-1)) := by rwa [log_primeCutoff]
  have h := actual_centralConditioning_le_discrete hell
    (firstCoefficient ((p : ℝ)-1)) (secondCoefficient ((p : ℝ)-1))
  have hh := hm.trans (mul_le_mul_of_nonneg_left (add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left h (by positivity)) le_rfl) le_rfl)
    (Real.rpow_nonneg (by norm_num) _))
  dsimp only [gridErrorContribution]
  convert! hh using 1
  rw [← discretization_coefficient hx.le hP]
  ring

theorem eventual_gridFractionalError_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ P : ℝ in atTop,
    gridFractionalError P ≤ C*(Real.log P)^(147/200 : ℝ) := by
  obtain ⟨C,hC,hb⟩ := eventual_gridError_expectation_bound
  let W := ∑' v : ℤ, frequencyWeight (3/2) v
  have hW : 0 ≤ W := tsum_nonneg (fun _ => frequencyWeight_nonneg _ _)
  refine ⟨C^(3/4 : ℝ)*W, by positivity, ?_⟩
  filter_upwards [hb, Real.tendsto_log_atTop.eventually_ge_atTop 0] with P hbound hP
  have hp (v : ℤ) : (∫ ω, gridError P v ω ∂phaseMeasure)^(3/4 : ℝ) ≤
      C^(3/4 : ℝ)*(Real.log P)^(147/200 : ℝ) := by
    have h := Real.rpow_le_rpow (integral_nonneg (gridError_nonneg P v)) (hbound v)
      (by norm_num : (0 : ℝ) ≤ 3/4)
    rw [Real.mul_rpow hC.le (Real.rpow_nonneg hP _), ← Real.rpow_mul hP] at h
    norm_num at h
    exact h
  calc
    _ ≤ (C^(3/4 : ℝ)*(Real.log P)^(147/200 : ℝ))*
        ∑ v ∈ centralFrequencies (frequencyCutoff P), frequencyWeight (3/2) v := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun v _ => (mul_le_mul_of_nonneg_left (hp v)
        (frequencyWeight_nonneg _ _)).trans_eq (mul_comm _ _))
    _ ≤ (C^(3/4 : ℝ)*(Real.log P)^(147/200 : ℝ))*W :=
      mul_le_mul_of_nonneg_left
        ((frequencyWeight_summable (by norm_num : (1 : ℝ) < 3/2)).sum_le_tsum _
          (fun _ _ => frequencyWeight_nonneg _ _)) (by positivity)
    _ = _ := by ring

theorem discretization_scale_identity {x L : ℝ} (hx : 0 ≤ x) (hL : 0 < L) :
    (48*x/(Real.pi*L))^(3/4 : ℝ)*L^(147/200 : ℝ) =
      (48/Real.pi)^(3/4 : ℝ)*x^(3/4 : ℝ)*L^(-(3/200 : ℝ)) := by
  have he : 48*x/(Real.pi*L) = ((48/Real.pi)*x)*L^(-(1 : ℝ)) := by
    rw [Real.rpow_neg_one]
    ring
  rw [he, Real.mul_rpow (by positivity) (Real.rpow_nonneg hL.le _),
    Real.mul_rpow (by positivity) hx, ← Real.rpow_mul hL.le]
  rw [mul_assoc, ← Real.rpow_add hL]
  norm_num

theorem gridErrorContribution_nonneg {x P : ℝ} (hx : 0 ≤ x) (hP : 0 < Real.log P) :
    0 ≤ gridErrorContribution x P :=
  mul_nonneg (Real.rpow_nonneg (by positivity) _) (gridFractionalError_nonneg P)

theorem gridErrorContribution_isBigO :
    (fun x => gridErrorContribution x (primeCutoff x)) =O[atTop]
      (fun x => x^(3/4 : ℝ)*(cutoffLog x)^(-(1/300 : ℝ))) := by
  obtain ⟨C,hC,hb⟩ := eventual_gridFractionalError_bound
  apply IsBigO.of_bound (C*(48/Real.pi)^(3/4 : ℝ))
  filter_upwards [HarperSmoothDivisor.primeCutoff_tendsto.eventually hb, cutoffLog_tendsto.eventually_ge_atTop 1,
    eventually_gt_atTop (0 : ℝ)] with x hbound hL hx
  have hP : 0 < Real.log (primeCutoff x) := by rw [log_primeCutoff]; linarith
  rw [Real.norm_of_nonneg (gridErrorContribution_nonneg hx.le hP),
    Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (48*x/(Real.pi*Real.log (primeCutoff x)))^(3/4 : ℝ)*
        (C*(Real.log (primeCutoff x))^(147/200 : ℝ)) :=
      mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg (by positivity) _)
    _ = (C*(48/Real.pi)^(3/4 : ℝ))*
        (x^(3/4 : ℝ)*(cutoffLog x)^(-(3/200 : ℝ))) := by
      rw [mul_left_comm _ C, discretization_scale_identity hx.le hP, log_primeCutoff]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)

theorem gridErrorContribution_isLittleO :
    (fun x => gridErrorContribution x (primeCutoff x)) =o[atTop] targetScale :=
  gridErrorContribution_isBigO.trans_isLittleO
    ((isBigO_refl (fun x : ℝ => x^(3/4 : ℝ)) atTop).mul_isLittleO inverse_cutoff_power_isLittleO)

theorem prime_square_gridErrorContribution_isLittleO :
    (fun p : ℕ => gridErrorContribution ((p : ℝ)-1) (primeCutoff ((p : ℝ)-1))) =o[atTop]
      (fun p : ℕ => targetScale ((p : ℝ)-1)) :=
  gridErrorContribution_isLittleO.comp_tendsto base_minus_one_tendsto

end NField.Alignment.HarperDiscretizationScales

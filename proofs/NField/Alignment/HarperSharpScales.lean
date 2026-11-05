/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperSharpGrid

/-!
# Negligible moderate-grid rejection at the manuscript scale

The sharp retained grid bounds actual random conditioning up to five literal
errors. The complete rejected grid keeps the original labels, central weights,
rounded cutoff and smoothing scales. Its proved logarithmic bound implies a
negative power after normalization, so it is negligible at the target scale.
The remaining sharp central low-moment bound is not asserted here.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperSharpScales
open scoped BigOperators Topology
open MeasureTheory Filter Asymptotics SteinhausMoment HarperSharpGrid HarperExtremeScales
  HarperDiscretizationScales HarperFrequencyScales HarperFrequencyTail HarperFrequencyIntervals
  HarperSmoothingConditioning HarperActualConditioning HarperConditioningFrequencies
  HarperRoundedCutoff HarperConditioningDecay HarperRoughSmoothing HarperSieveScales

def sharpCentralConditioning (p : ℕ) : ℝ :=
  ∑ v ∈ centralFrequencies (frequencyCutoff (primeCutoff ((p : ℝ)-1))),
    frequencyWeight (3/2) v*sharpGridConditioning p v
def rejectionFractionalError (p : ℕ) : ℝ :=
  ∑ v ∈ centralFrequencies (frequencyCutoff (primeCutoff ((p : ℝ)-1))),
    frequencyWeight (3/2) v*(totalRejectedGridMoment p v)^(3/4 : ℝ)
def rejectionErrorContribution (p : ℕ) : ℝ :=
  (48*((p : ℝ)-1)/(Real.pi*Real.log (primeCutoff ((p : ℝ)-1))))^(3/4 : ℝ)*rejectionFractionalError p
def sharpMainTerm (p : ℕ) : ℝ :=
  (2 : ℝ)^(3/4 : ℝ)*(48*((p : ℝ)-1)/(Real.pi*Real.log (primeCutoff ((p : ℝ)-1))))^(3/4 : ℝ)*
    sharpCentralConditioning p
def completeSharpError (p : ℕ) : ℝ :=
  (2 : ℝ)^(3/4 : ℝ)*(rejectionErrorContribution p+
    extremeErrorContribution ((p : ℝ)-1) (primeCutoff ((p : ℝ)-1))+
    gridErrorContribution ((p : ℝ)-1) (primeCutoff ((p : ℝ)-1))+
    frequencyTailContribution ((p : ℝ)-1) (primeCutoff ((p : ℝ)-1))+
    (roughSmoothingError ((p : ℝ)-1) (primeCutoff ((p : ℝ)-1))
      (smoothCutoff ((p : ℝ)-1)) (smoothingScale ((p : ℝ)-1)))^(3/4 : ℝ))

theorem rejectionFractionalError_nonneg {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1)) :
    0 ≤ rejectionFractionalError p :=
  Finset.sum_nonneg (fun v _ => mul_nonneg (frequencyWeight_nonneg _ _)
    (Real.rpow_nonneg (totalRejectedGridMoment_nonneg hell v) _))

theorem moderateCentralConditioning_le_sharp {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1)) :
    moderateCentralConditioning p (firstCoefficient ((p : ℝ)-1)) (secondCoefficient ((p : ℝ)-1))
      (primeCutoff ((p : ℝ)-1)) ≤ sharpCentralConditioning p+rejectionFractionalError p := by
  unfold moderateCentralConditioning sharpCentralConditioning rejectionFractionalError
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro v hv
  exact (mul_le_mul_of_nonneg_left (moderateGrid_conditioning_le_sharp hell v hv)
    (frequencyWeight_nonneg _ _)).trans_eq (mul_add _ _ _)

theorem eventual_actual_random_sharp_with_errors : ∀ᶠ p : ℕ in atTop,
    actualRandomConditioning p ≤ sharpMainTerm p+completeSharpError p := by
  filter_upwards [eventual_actual_random_moderate_with_errors,
    (cutoffLog_tendsto.comp base_minus_one_tendsto).eventually_gt_atTop 0,
    base_minus_one_tendsto.eventually_gt_atTop 0] with p hm hell hx
  have hP : 0 < Real.log (primeCutoff ((p : ℝ)-1)) := by rwa [log_primeCutoff]
  have h := moderateCentralConditioning_le_sharp hell
  have hh := hm.trans (mul_le_mul_of_nonneg_left (add_le_add
    (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left h (by positivity)) le_rfl) le_rfl) le_rfl) le_rfl)
    (Real.rpow_nonneg (by norm_num) _))
  convert! hh using 1
  unfold sharpMainTerm completeSharpError rejectionErrorContribution
  ring

theorem eventual_rejectionFractionalError_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ p : ℕ in atTop,
    rejectionFractionalError p ≤ C*(cutoffLog ((p : ℝ)-1))^(21/40 : ℝ) := by
  obtain ⟨C,hC,hb⟩ := eventual_totalRejectedGridMoment_power_bound
  let W := ∑' v : ℤ, frequencyWeight (3/2) v
  have hW : 0 ≤ W := tsum_nonneg (fun _ => frequencyWeight_nonneg _ _)
  refine ⟨C^(3/4 : ℝ)*W,by positivity,?_⟩
  filter_upwards [hb,(cutoffLog_tendsto.comp base_minus_one_tendsto).eventually_gt_atTop 0] with p hbound hell
  dsimp only [Function.comp_apply] at hell
  have hp (v : ℤ) : (totalRejectedGridMoment p v)^(3/4 : ℝ) ≤
      C^(3/4 : ℝ)*(cutoffLog ((p : ℝ)-1))^(21/40 : ℝ) := by
    have h := Real.rpow_le_rpow (totalRejectedGridMoment_nonneg hell v) (hbound v)
      (by norm_num : (0 : ℝ) ≤ 3/4)
    rw [Real.mul_rpow hC.le (Real.rpow_nonneg hell.le _), ← Real.rpow_mul hell.le] at h
    norm_num at h
    exact h
  calc
    _ ≤ (C^(3/4 : ℝ)*(cutoffLog ((p : ℝ)-1))^(21/40 : ℝ))*
        ∑ v ∈ centralFrequencies (frequencyCutoff (primeCutoff ((p : ℝ)-1))), frequencyWeight (3/2) v := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun v _ => (mul_le_mul_of_nonneg_left (hp v)
        (frequencyWeight_nonneg _ _)).trans_eq (mul_comm _ _))
    _ ≤ (C^(3/4 : ℝ)*(cutoffLog ((p : ℝ)-1))^(21/40 : ℝ))*W :=
      mul_le_mul_of_nonneg_left
        ((frequencyWeight_summable (by norm_num : (1 : ℝ) < 3/2)).sum_le_tsum _
          (fun _ _ => frequencyWeight_nonneg _ _)) (by positivity)
    _ = _ := by ring

theorem rejection_scale_identity {x L : ℝ} (hx : 0 ≤ x) (hL : 0 < L) :
    (48*x/(Real.pi*L))^(3/4 : ℝ)*L^(21/40 : ℝ) =
      (48/Real.pi)^(3/4 : ℝ)*x^(3/4 : ℝ)*L^(-(9/40 : ℝ)) := by
  have he : 48*x/(Real.pi*L) = ((48/Real.pi)*x)*L^(-(1 : ℝ)) := by
    rw [Real.rpow_neg_one]
    ring
  rw [he,Real.mul_rpow (by positivity) (Real.rpow_nonneg hL.le _),
    Real.mul_rpow (by positivity) hx,← Real.rpow_mul hL.le]
  rw [mul_assoc,← Real.rpow_add hL]
  norm_num

theorem rejectionErrorContribution_nonneg {p : ℕ} (hx : 0 ≤ (p : ℝ)-1)
    (hell : 0 < cutoffLog ((p : ℝ)-1)) : 0 ≤ rejectionErrorContribution p := by
  have hP : 0 < Real.log (primeCutoff ((p : ℝ)-1)) := by rwa [log_primeCutoff]
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (rejectionFractionalError_nonneg hell)

theorem rejectionErrorContribution_isBigO :
    rejectionErrorContribution =O[atTop]
      (fun p : ℕ => ((p : ℝ)-1)^(3/4 : ℝ)*(cutoffLog ((p : ℝ)-1))^(-(1/300 : ℝ))) := by
  obtain ⟨C,hC,hb⟩ := eventual_rejectionFractionalError_bound
  apply IsBigO.of_bound (C*(48/Real.pi)^(3/4 : ℝ))
  filter_upwards [hb,(cutoffLog_tendsto.comp base_minus_one_tendsto).eventually_ge_atTop 1,
    base_minus_one_tendsto.eventually_gt_atTop 0] with p hbound hL hx
  dsimp only [Function.comp_apply] at hL
  have hell : 0 < cutoffLog ((p : ℝ)-1) := lt_of_lt_of_le zero_lt_one hL
  have hP : 0 < Real.log (primeCutoff ((p : ℝ)-1)) := by rwa [log_primeCutoff]
  rw [Real.norm_of_nonneg (rejectionErrorContribution_nonneg hx.le hell),
    Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (48*((p : ℝ)-1)/(Real.pi*Real.log (primeCutoff ((p : ℝ)-1))))^(3/4 : ℝ)*
        (C*(cutoffLog ((p : ℝ)-1))^(21/40 : ℝ)) :=
      mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg (by positivity) _)
    _ = (C*(48/Real.pi)^(3/4 : ℝ))*
        (((p : ℝ)-1)^(3/4 : ℝ)*(cutoffLog ((p : ℝ)-1))^(-(9/40 : ℝ))) := by
      rw [log_primeCutoff,mul_left_comm _ C,rejection_scale_identity hx.le hell]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)

theorem rejectionErrorContribution_isLittleO :
    rejectionErrorContribution =o[atTop] (fun p : ℕ => targetScale ((p : ℝ)-1)) :=
  rejectionErrorContribution_isBigO.trans_isLittleO
    ((isBigO_refl (fun p : ℕ => ((p : ℝ)-1)^(3/4 : ℝ)) atTop).mul_isLittleO
      (inverse_cutoff_power_isLittleO.comp_tendsto base_minus_one_tendsto))

theorem completeSharpError_isLittleO :
    completeSharpError =o[atTop] (fun p : ℕ => targetScale ((p : ℝ)-1)) :=
  ((((rejectionErrorContribution_isLittleO.add prime_square_extremeErrorContribution_isLittleO).add
    prime_square_gridErrorContribution_isLittleO).add prime_square_frequencyTailContribution_isLittleO).add
    prime_square_roughSmoothingError_fractional_isLittleO).const_mul_left ((2 : ℝ)^(3/4 : ℝ))

theorem eventual_actual_random_sharp {epsilon : ℝ} (he : 0 < epsilon) : ∀ᶠ p : ℕ in atTop,
    actualRandomConditioning p ≤ sharpMainTerm p+epsilon*targetScale ((p : ℝ)-1) := by
  filter_upwards [eventual_actual_random_sharp_with_errors,completeSharpError_isLittleO.bound he,
    base_minus_one_tendsto.eventually_gt_atTop 0,
    ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp base_minus_one_tendsto).eventually_gt_atTop 0]
    with p hm hb hx hu
  dsimp only [Function.comp_apply] at hx hu
  have htarget : 0 ≤ targetScale ((p : ℝ)-1) := by unfold targetScale; positivity
  rw [Real.norm_of_nonneg htarget] at hb
  have herror : completeSharpError p ≤ epsilon*targetScale ((p : ℝ)-1) := (le_abs_self _).trans hb
  exact hm.trans (add_le_add le_rfl herror)

end NField.Alignment.HarperSharpScales

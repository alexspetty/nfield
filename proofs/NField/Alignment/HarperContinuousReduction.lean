/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperReverseGrid

/-!
# The actual main term reduced to the continuous unit fractional moment

The summable original frequency weights give one finite universal mass.
The reverse grid comparison retains the complete original weighted grid
error; its established decay makes this additional contribution negligible
at the exact rounded manuscript scale. The random-conditioning consumer
therefore reduces to the continuous unit-window moment. The critical
low-moment saving for that actual moment remains unproved.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperContinuousReduction
open scoped BigOperators Topology
open MeasureTheory Filter Asymptotics SteinhausMoment HarperReverseGrid
  HarperUnconditioning HarperUnconditioningScales HarperSharpProfile
  HarperDiscretizationScales HarperEulerDiscretization HarperFrequencyIntervals
  HarperFrequencyTail HarperConditioningFrequencies HarperRoundedCutoff HarperConditioningDecay

def frequencyMass : ℝ := ∑' v : ℤ, frequencyWeight (3/2) v
def continuousMainTerm (p : ℕ) : ℝ :=
  ((2 : ℝ)^(3/4 : ℝ))^2*(48*((p : ℝ)-1)/(Real.pi*Real.log (primeCutoff ((p : ℝ)-1))))^(3/4 : ℝ)*
    (profileConstant^(3/4 : ℝ))^2*(2*frequencyMass*unitFractionalMoment (primeCutoff ((p : ℝ)-1)))
def reverseGridContribution (p : ℕ) : ℝ :=
  ((2 : ℝ)^(3/4 : ℝ))^2*(profileConstant^(3/4 : ℝ))^2*
    gridErrorContribution ((p : ℝ)-1) (primeCutoff ((p : ℝ)-1))
def continuousError (p : ℕ) : ℝ := reverseGridContribution p+unconditionalError p

theorem frequencyMass_nonneg : 0 ≤ frequencyMass :=
  tsum_nonneg (fun _ => frequencyWeight_nonneg _ _)

theorem central_weight_sum_le (P : ℝ) :
    (∑ v ∈ centralFrequencies (frequencyCutoff P), frequencyWeight (3/2) v) ≤ frequencyMass :=
  (frequencyWeight_summable (by norm_num : (1 : ℝ) < 3/2)).sum_le_tsum _
    (fun _ _ => frequencyWeight_nonneg _ _)

theorem unconditionalCentralMoment_le_unit {p : ℕ}
    (hD : 1 ≤ gridScale (primeCutoff ((p : ℝ)-1))) :
    unconditionalCentralMoment p ≤ (2 : ℝ)^(3/4 : ℝ)*
      (2*frequencyMass*unitFractionalMoment (primeCutoff ((p : ℝ)-1))+
        gridFractionalError (primeCutoff ((p : ℝ)-1))) := by
  calc
    _ ≤ ∑ v ∈ centralFrequencies (frequencyCutoff (primeCutoff ((p : ℝ)-1))),
        frequencyWeight (3/2) v*((2 : ℝ)^(3/4 : ℝ)*
          (2*unitFractionalMoment (primeCutoff ((p : ℝ)-1))+
            (∫ ω, gridError (primeCutoff ((p : ℝ)-1)) v ω ∂phaseMeasure)^(3/4 : ℝ))) :=
      Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left (unconditionalGridMoment_le_unit hD v)
        (frequencyWeight_nonneg _ _))
    _ = (2 : ℝ)^(3/4 : ℝ)*
        (2*(∑ v ∈ centralFrequencies (frequencyCutoff (primeCutoff ((p : ℝ)-1))), frequencyWeight (3/2) v)*
          unitFractionalMoment (primeCutoff ((p : ℝ)-1))+
            gridFractionalError (primeCutoff ((p : ℝ)-1))) := by
      unfold gridFractionalError
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      congr 1
      · rw [← Finset.sum_mul]
        ring
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (central_weight_sum_le _) (by norm_num))
        (unitFractionalMoment_nonneg _)) le_rfl) (by positivity)

theorem unconditionalMainTerm_le_continuous {p : ℕ} (hx : 0 ≤ (p : ℝ)-1)
    (hL : 1 ≤ cutoffLog ((p : ℝ)-1)) :
    unconditionalMainTerm p ≤ continuousMainTerm p+reverseGridContribution p := by
  have hP : 0 < Real.log (primeCutoff ((p : ℝ)-1)) := by rw [log_primeCutoff]; linarith
  have hD : 1 ≤ gridScale (primeCutoff ((p : ℝ)-1)) := by
    rw [gridScale, log_primeCutoff]
    exact Real.one_le_rpow hL (by norm_num)
  have h := mul_le_mul_of_nonneg_left (unconditionalCentralMoment_le_unit hD)
    (show 0 ≤ (2 : ℝ)^(3/4 : ℝ)*
      (48*((p : ℝ)-1)/(Real.pi*Real.log (primeCutoff ((p : ℝ)-1))))^(3/4 : ℝ)*
        (profileConstant^(3/4 : ℝ))^2 by positivity)
  convert! h using 1
  unfold continuousMainTerm reverseGridContribution gridErrorContribution
  ring

theorem reverseGridContribution_isLittleO :
    reverseGridContribution =o[atTop] (fun p : ℕ => targetScale ((p : ℝ)-1)) :=
  prime_square_gridErrorContribution_isLittleO.const_mul_left
    (((2 : ℝ)^(3/4 : ℝ))^2*(profileConstant^(3/4 : ℝ))^2)

theorem continuousError_isLittleO :
    continuousError =o[atTop] (fun p : ℕ => targetScale ((p : ℝ)-1)) :=
  reverseGridContribution_isLittleO.add unconditionalError_isLittleO

theorem eventual_actual_random_continuous_with_errors : ∀ᶠ p : ℕ in atTop,
    actualRandomConditioning p ≤ continuousMainTerm p+continuousError p := by
  filter_upwards [eventual_actual_random_unconditional_with_errors,
    (cutoffLog_tendsto.comp base_minus_one_tendsto).eventually_ge_atTop 1,
    base_minus_one_tendsto.eventually_gt_atTop 0] with p hm hL hx
  have h := unconditionalMainTerm_le_continuous hx.le hL
  unfold continuousError
  linarith

theorem eventual_actual_random_continuous {epsilon : ℝ} (he : 0 < epsilon) : ∀ᶠ p : ℕ in atTop,
    actualRandomConditioning p ≤ continuousMainTerm p+epsilon*targetScale ((p : ℝ)-1) := by
  filter_upwards [eventual_actual_random_continuous_with_errors, continuousError_isLittleO.bound he,
    base_minus_one_tendsto.eventually_gt_atTop 0,
    ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp base_minus_one_tendsto).eventually_gt_atTop 0]
    with p hm hb hx hu
  dsimp only [Function.comp_apply] at hx hu
  have htarget : 0 ≤ targetScale ((p : ℝ)-1) := by unfold targetScale; positivity
  rw [Real.norm_of_nonneg htarget] at hb
  have herror : continuousError p ≤ epsilon*targetScale ((p : ℝ)-1) := (le_abs_self _).trans hb
  exact hm.trans (add_le_add le_rfl herror)

end NField.Alignment.HarperContinuousReduction

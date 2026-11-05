/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperUnconditioning

/-!
# Removing conditioning at the exact manuscript scale

The complete label-profile correction has a proved logarithmic majorant.
A coarser power bound gives a negative normalized exponent, so the literal
correction and the full sum of all six errors are negligible. Actual random
conditioning is reduced to the original unconditional fractional grid
moment. Its low-moment saving remains a separate unproved obligation.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperUnconditioningScales
open scoped BigOperators Topology
open MeasureTheory Filter Asymptotics SteinhausMoment HarperSharpGrid HarperSharpScales HarperSharpProfile
  HarperProfileGrid HarperUnconditioning HarperActualSharpConditioning HarperParameterBounds
  HarperEulerDiscretization HarperFrequencyTail HarperFrequencyIntervals HarperFrequencyScales
  HarperConditioningFrequencies HarperRoundedCutoff HarperConditioningDecay

def unconditionalCentralMoment (p : ℕ) : ℝ :=
  ∑ v ∈ centralFrequencies (frequencyCutoff (primeCutoff ((p : ℝ)-1))),
    frequencyWeight (3/2) v*unconditionalGridMoment (primeCutoff ((p : ℝ)-1)) v
def profileFractionalError (p : ℕ) : ℝ :=
  profileConstant^(3/4 : ℝ)*
    (∑ v ∈ centralFrequencies (frequencyCutoff (primeCutoff ((p : ℝ)-1))), frequencyWeight (3/2) v)*
    (profileRejectionBound p)^(3/4 : ℝ)
def unconditionalMainTerm (p : ℕ) : ℝ :=
  (2 : ℝ)^(3/4 : ℝ)*(48*((p : ℝ)-1)/(Real.pi*Real.log (primeCutoff ((p : ℝ)-1))))^(3/4 : ℝ)*
    (profileConstant^(3/4 : ℝ))^2*unconditionalCentralMoment p
def profileErrorContribution (p : ℕ) : ℝ :=
  (2 : ℝ)^(3/4 : ℝ)*(48*((p : ℝ)-1)/(Real.pi*Real.log (primeCutoff ((p : ℝ)-1))))^(3/4 : ℝ)*
    profileFractionalError p
def unconditionalError (p : ℕ) : ℝ := profileErrorContribution p+completeSharpError p

theorem sharpCentralConditioning_bound {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (hD : 1 ≤ gridScale (primeCutoff ((p : ℝ)-1))) :
    sharpCentralConditioning p ≤ (profileConstant^(3/4 : ℝ))^2*unconditionalCentralMoment p+
      profileFractionalError p := by
  calc
    _ ≤ ∑ v ∈ centralFrequencies (frequencyCutoff (primeCutoff ((p : ℝ)-1))),
        frequencyWeight (3/2) v*(profileConstant^(3/4 : ℝ)*
          (profileConstant^(3/4 : ℝ)*unconditionalGridMoment (primeCutoff ((p : ℝ)-1)) v+
            (profileRejectionBound p)^(3/4 : ℝ))) :=
      Finset.sum_le_sum (fun v hv => mul_le_mul_of_nonneg_left (sharpGridConditioning_bound hell hD v hv)
        (frequencyWeight_nonneg _ _))
    _ = _ := by
      unfold unconditionalCentralMoment profileFractionalError
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      simp_rw [← mul_assoc]
      rw [← Finset.sum_mul]
      rw [Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro v _
        ring
      · rw [← Finset.sum_mul]
        ring

theorem eventual_actual_random_unconditional_with_errors : ∀ᶠ p : ℕ in atTop,
    actualRandomConditioning p ≤ unconditionalMainTerm p+unconditionalError p := by
  filter_upwards [eventual_actual_random_sharp_with_errors,
    (cutoffLog_tendsto.comp base_minus_one_tendsto).eventually_ge_atTop 1,
    base_minus_one_tendsto.eventually_gt_atTop 0] with p hm hL hx
  have hell : 0 < cutoffLog ((p : ℝ)-1) := lt_of_lt_of_le zero_lt_one hL
  have hD : 1 ≤ gridScale (primeCutoff ((p : ℝ)-1)) := by
    rw [gridScale,log_primeCutoff]
    exact Real.one_le_rpow hL (by norm_num)
  have hP : 0 < Real.log (primeCutoff ((p : ℝ)-1)) := by rwa [log_primeCutoff]
  have h := mul_le_mul_of_nonneg_left (sharpCentralConditioning_bound hell hD)
    (show 0 ≤ (2 : ℝ)^(3/4 : ℝ)*(48*((p : ℝ)-1)/(Real.pi*Real.log (primeCutoff ((p : ℝ)-1))))^(3/4 : ℝ) by positivity)
  have hh := hm.trans (add_le_add h le_rfl)
  convert! hh using 1
  unfold unconditionalMainTerm unconditionalError profileErrorContribution
  ring

theorem eventual_profileRejectionBound_log_bound : ∃ C : ℝ, 0 < C ∧ ∀ᶠ p : ℕ in atTop,
    profileRejectionBound p ≤ C*Real.log (cutoffLog ((p : ℝ)-1))*(cutoffLog ((p : ℝ)-1))^(9/10 : ℝ) := by
  refine ⟨16*profileConstant, mul_pos (by norm_num) profileConstant_pos, ?_⟩
  filter_upwards [(cutoffLog_tendsto.comp base_minus_one_tendsto).eventually_gt_atTop 0,
    (Real.tendsto_log_atTop.comp (cutoffLog_tendsto.comp base_minus_one_tendsto)).eventually_ge_atTop 1]
    with p hell hlog
  dsimp only [Function.comp_apply] at hell hlog
  have hJ : 2*(rangeCount (cutoffLog ((p : ℝ)-1)) : ℝ)+2 ≤ 8*Real.log (cutoffLog ((p : ℝ)-1)) := by
    have h := (rangeCount_bounds hell hlog).2.2.1
    linarith
  have he : profileRejectionBound p =
      2*profileConstant*(2*(rangeCount (cutoffLog ((p : ℝ)-1)) : ℝ)+2)*
        (cutoffLog ((p : ℝ)-1))^(9/10 : ℝ) := by
    unfold profileRejectionBound rejectionFactor precision
    calc
      _ = (2*profileConstant*(2*(rangeCount (cutoffLog ((p : ℝ)-1)) : ℝ)+2))*
          ((cutoffLog ((p : ℝ)-1))^(-(13/10 : ℝ))*(cutoffLog ((p : ℝ)-1))^(11/5 : ℝ)) := by ring
      _ = _ := by rw [← Real.rpow_add hell]; norm_num
  rw [he]
  calc
    _ ≤ 2*profileConstant*(8*Real.log (cutoffLog ((p : ℝ)-1)))*(cutoffLog ((p : ℝ)-1))^(9/10 : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hJ (mul_nonneg (by norm_num) profileConstant_pos.le))
        (Real.rpow_nonneg hell.le _)
    _ = _ := by ring

theorem eventual_profileRejectionBound_power_bound : ∃ C : ℝ, 0 < C ∧ ∀ᶠ p : ℕ in atTop,
    profileRejectionBound p ≤ C*(cutoffLog ((p : ℝ)-1))^(19/20 : ℝ) := by
  obtain ⟨C,hC,hb⟩ := eventual_profileRejectionBound_log_bound
  refine ⟨C,hC,?_⟩
  have hsmall := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1/20)).bound
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hb,(cutoffLog_tendsto.comp base_minus_one_tendsto).eventually hsmall,
    (cutoffLog_tendsto.comp base_minus_one_tendsto).eventually_ge_atTop 1] with p hbound hs hL
  dsimp only [Function.comp_apply] at hs hL
  have hell : 0 < cutoffLog ((p : ℝ)-1) := lt_of_lt_of_le zero_lt_one hL
  rw [Real.norm_of_nonneg (Real.log_nonneg hL), Real.norm_of_nonneg (Real.rpow_nonneg hell.le _), one_mul] at hs
  calc
    _ ≤ C*Real.log (cutoffLog ((p : ℝ)-1))*(cutoffLog ((p : ℝ)-1))^(9/10 : ℝ) := hbound
    _ ≤ C*(cutoffLog ((p : ℝ)-1))^(1/20 : ℝ)*(cutoffLog ((p : ℝ)-1))^(9/10 : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs hC.le) (Real.rpow_nonneg hell.le _)
    _ = _ := by rw [mul_assoc, ← Real.rpow_add hell]; norm_num

theorem profileFractionalError_nonneg {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1)) :
    0 ≤ profileFractionalError p := by
  unfold profileFractionalError
  exact mul_nonneg (mul_nonneg (Real.rpow_nonneg profileConstant_pos.le _)
    (Finset.sum_nonneg (fun v _ => frequencyWeight_nonneg _ v)))
    (Real.rpow_nonneg (profileRejectionBound_nonneg hell) _)

theorem eventual_profileFractionalError_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ p : ℕ in atTop,
    profileFractionalError p ≤ C*(cutoffLog ((p : ℝ)-1))^(57/80 : ℝ) := by
  obtain ⟨C,hC,hb⟩ := eventual_profileRejectionBound_power_bound
  let W := ∑' v : ℤ, frequencyWeight (3/2) v
  have hW : 0 ≤ W := tsum_nonneg (fun _ => frequencyWeight_nonneg _ _)
  have hA := profileConstant_pos
  refine ⟨profileConstant^(3/4 : ℝ)*W*C^(3/4 : ℝ),by positivity,?_⟩
  filter_upwards [hb,(cutoffLog_tendsto.comp base_minus_one_tendsto).eventually_gt_atTop 0] with p hbound hell
  dsimp only [Function.comp_apply] at hell
  have hpow := Real.rpow_le_rpow (profileRejectionBound_nonneg hell) hbound
    (by norm_num : (0 : ℝ) ≤ 3/4)
  rw [Real.mul_rpow hC.le (Real.rpow_nonneg hell.le _), ← Real.rpow_mul hell.le] at hpow
  norm_num at hpow
  have hsum : (∑ v ∈ centralFrequencies (frequencyCutoff (primeCutoff ((p : ℝ)-1))), frequencyWeight (3/2) v) ≤ W :=
    (frequencyWeight_summable (by norm_num : (1 : ℝ) < 3/2)).sum_le_tsum _ (fun _ _ => frequencyWeight_nonneg _ _)
  unfold profileFractionalError
  calc
    _ ≤ (profileConstant^(3/4 : ℝ)*W)*(C^(3/4 : ℝ)*(cutoffLog ((p : ℝ)-1))^(57/80 : ℝ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg profileConstant_pos.le _)) hpow
        (Real.rpow_nonneg (profileRejectionBound_nonneg hell) _) (by positivity)
    _ = _ := by ring

theorem profile_scale_identity {x L : ℝ} (hx : 0 ≤ x) (hL : 0 < L) :
    (48*x/(Real.pi*L))^(3/4 : ℝ)*L^(57/80 : ℝ) =
      (48/Real.pi)^(3/4 : ℝ)*x^(3/4 : ℝ)*L^(-(3/80 : ℝ)) := by
  have he : 48*x/(Real.pi*L) = ((48/Real.pi)*x)*L^(-(1 : ℝ)) := by
    rw [Real.rpow_neg_one]
    ring
  rw [he,Real.mul_rpow (by positivity) (Real.rpow_nonneg hL.le _),
    Real.mul_rpow (by positivity) hx,← Real.rpow_mul hL.le]
  rw [mul_assoc,← Real.rpow_add hL]
  norm_num

theorem profileErrorContribution_nonneg {p : ℕ} (hx : 0 ≤ (p : ℝ)-1)
    (hell : 0 < cutoffLog ((p : ℝ)-1)) : 0 ≤ profileErrorContribution p := by
  have hP : 0 < Real.log (primeCutoff ((p : ℝ)-1)) := by rwa [log_primeCutoff]
  unfold profileErrorContribution
  exact mul_nonneg (by positivity) (profileFractionalError_nonneg hell)

theorem profileErrorContribution_isBigO :
    profileErrorContribution =O[atTop]
      (fun p : ℕ => ((p : ℝ)-1)^(3/4 : ℝ)*(cutoffLog ((p : ℝ)-1))^(-(1/300 : ℝ))) := by
  obtain ⟨C,hC,hb⟩ := eventual_profileFractionalError_bound
  apply IsBigO.of_bound ((2 : ℝ)^(3/4 : ℝ)*C*(48/Real.pi)^(3/4 : ℝ))
  filter_upwards [hb,(cutoffLog_tendsto.comp base_minus_one_tendsto).eventually_ge_atTop 1,
    base_minus_one_tendsto.eventually_gt_atTop 0] with p hbound hL hx
  dsimp only [Function.comp_apply] at hL
  have hell : 0 < cutoffLog ((p : ℝ)-1) := lt_of_lt_of_le zero_lt_one hL
  have hP : 0 < Real.log (primeCutoff ((p : ℝ)-1)) := by rwa [log_primeCutoff]
  rw [Real.norm_of_nonneg (profileErrorContribution_nonneg hx.le hell), Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (2 : ℝ)^(3/4 : ℝ)*(48*((p : ℝ)-1)/(Real.pi*Real.log (primeCutoff ((p : ℝ)-1))))^(3/4 : ℝ)*
        (C*(cutoffLog ((p : ℝ)-1))^(57/80 : ℝ)) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = ((2 : ℝ)^(3/4 : ℝ)*C*(48/Real.pi)^(3/4 : ℝ))*
        (((p : ℝ)-1)^(3/4 : ℝ)*(cutoffLog ((p : ℝ)-1))^(-(3/80 : ℝ))) := by
      rw [log_primeCutoff]
      calc
        _ = ((2 : ℝ)^(3/4 : ℝ)*C)*((48*((p : ℝ)-1)/(Real.pi*cutoffLog ((p : ℝ)-1)))^(3/4 : ℝ)*
            (cutoffLog ((p : ℝ)-1))^(57/80 : ℝ)) := by ring
        _ = _ := by rw [profile_scale_identity hx.le hell]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)

theorem profileErrorContribution_isLittleO :
    profileErrorContribution =o[atTop] (fun p : ℕ => targetScale ((p : ℝ)-1)) :=
  profileErrorContribution_isBigO.trans_isLittleO
    ((isBigO_refl (fun p : ℕ => ((p : ℝ)-1)^(3/4 : ℝ)) atTop).mul_isLittleO
      (inverse_cutoff_power_isLittleO.comp_tendsto base_minus_one_tendsto))

theorem unconditionalError_isLittleO :
    unconditionalError =o[atTop] (fun p : ℕ => targetScale ((p : ℝ)-1)) :=
  profileErrorContribution_isLittleO.add completeSharpError_isLittleO

theorem eventual_actual_random_unconditional {epsilon : ℝ} (he : 0 < epsilon) : ∀ᶠ p : ℕ in atTop,
    actualRandomConditioning p ≤ unconditionalMainTerm p+epsilon*targetScale ((p : ℝ)-1) := by
  filter_upwards [eventual_actual_random_unconditional_with_errors,unconditionalError_isLittleO.bound he,
    base_minus_one_tendsto.eventually_gt_atTop 0,
    ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp base_minus_one_tendsto).eventually_gt_atTop 0]
    with p hm hb hx hu
  dsimp only [Function.comp_apply] at hx hu
  have htarget : 0 ≤ targetScale ((p : ℝ)-1) := by unfold targetScale; positivity
  rw [Real.norm_of_nonneg htarget] at hb
  have herror : unconditionalError p ≤ epsilon*targetScale ((p : ℝ)-1) := (le_abs_self _).trans hb
  exact hm.trans (add_le_add le_rfl herror)

end NField.Alignment.HarperUnconditioningScales

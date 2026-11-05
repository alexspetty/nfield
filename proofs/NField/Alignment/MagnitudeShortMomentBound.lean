/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperLowMomentApplication
import NField.Alignment.MagnitudeLogarithmicScale
import NField.Alignment.MagnitudeCubicLimits

/-!
# The unconditional short-sum estimate at prime-square modulus

This proves Proposition 11 for the literal normalized primitive odd character
family. The critical Euler-product input is proved, not supplied as a
hypothesis. The two intermediate full-character estimates in display 075
are recorded separately, with a constant independent of the prime base.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.MagnitudeShortMomentBound
open scoped BigOperators Topology
open Filter Asymptotics SpectralRepulsion CollisionCharacterStructure
  PrimeSquareMagnitudeFamily HarperRoundedCutoff HarperConditioningDecay
  HarperLowMomentScales HarperLowMomentApplication MagnitudeLogarithmicScale
  MagnitudeContinuousFractionalTransfer MagnitudeCubicLimits

theorem eventual_full_character_intermediate_bound : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ p : ℕ in atTop, ∀ [NeZero (p^2)], p.Prime →
    uniformAverage (fun χ : Character (p^2) =>
      ‖∑ n ∈ Finset.Icc 1 (p-1), χ (n : ZMod (p^2))‖^(3/2 : ℝ)) ≤
      C*intermediateScale ((p : ℝ)-1) := by
  obtain ⟨C,hC,hb⟩ := eventual_continuous_main_bound
  refine ⟨2*C+2,by positivity,?_⟩
  filter_upwards [hb,base_minus_one_tendsto.eventually eventual_scale_comparison,
    eventual_actual_character_continuous_reduction (by norm_num : (0 : ℝ) < 1)] with p hm hs hc
  intro _ hp
  have h := hc hp
  nlinarith [hs.2]

theorem eventual_full_character_target_bound : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ p : ℕ in atTop, ∀ [NeZero (p^2)], p.Prime →
    uniformAverage (fun χ : Character (p^2) =>
      ‖∑ n ∈ Finset.Icc 1 (p-1), χ (n : ZMod (p^2))‖^(3/2 : ℝ)) ≤
      C*targetScale ((p : ℝ)-1) := by
  obtain ⟨C,hC,hb⟩ := eventual_full_character_intermediate_bound
  refine ⟨C*16,by positivity,?_⟩
  filter_upwards [hb,base_minus_one_tendsto.eventually eventual_scale_comparison] with p hp hs
  intro _ hprime
  exact (hp hprime).trans (by nlinarith [mul_le_mul_of_nonneg_left hs.1 hC.le])

theorem eventual_short_moment_bound : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ p : ℕ in atTop, ∀ [NeZero p] [NeZero (p^2)], p.Prime → p ≠ 2 →
    uniformAverage (fun χ : PrimitiveOddFamily p => (shortMagnitude p χ)^(3/2 : ℝ)) ≤
      C*(Real.log (Real.log (p : ℝ)))^(-(3/8 : ℝ)) := by
  obtain ⟨C,hC,hb⟩ := eventual_continuous_target_bound
  refine ⟨(6*C+1)*2,by positivity,?_⟩
  filter_upwards [hb,
    (tendsto_natCast_atTop_atTop : Tendsto (fun p : ℕ => (p : ℝ)) atTop atTop).eventually
      eventual_normalized_target_bound,
    eventual_normalized_continuous_reduction (by norm_num : (0 : ℝ) < 1)] with p hm hs hc
  intro _ _ hp ho
  calc
    _ ≤ (6*HarperContinuousReduction.continuousMainTerm p+1*targetScale ((p : ℝ)-1))/(p : ℝ)^(3/4 : ℝ) := hc hp ho
    _ ≤ (6*C+1)*(targetScale ((p : ℝ)-1)/(p : ℝ)^(3/4 : ℝ)) := by
      rw [← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hs (show 0 ≤ 6*C+1 by positivity)]

/-- The exact Big-O statement of Proposition 11 along the nontrivial filter
of all growing odd primes. -/
theorem short_moment_isBigO :
    (fun p : OddPrimeBase => uniformAverage (fun χ : PrimitiveOddFamily p.val =>
      (shortMagnitude p.val χ)^(3/2 : ℝ))) =O[oddPrimeAtTop]
    (fun p : OddPrimeBase => (Real.log (Real.log (p.val : ℝ)))^(-(3/8 : ℝ))) := by
  obtain ⟨C,hC,hb⟩ := eventual_short_moment_bound
  apply IsBigO.of_bound C
  filter_upwards [Filter.tendsto_comap.eventually hb,
    (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp base_tendsto_atTop)).eventually_ge_atTop 0]
    with p hp hl
  dsimp only [Function.comp_apply] at hl
  have hnonneg : 0 ≤ uniformAverage (fun χ : PrimitiveOddFamily p.val =>
      (shortMagnitude p.val χ)^(3/2 : ℝ)) := by
    unfold uniformAverage
    exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun χ _ =>
      Real.rpow_nonneg (short_magnitude_nonneg _ χ) _))
  rw [Real.norm_of_nonneg hnonneg, Real.norm_of_nonneg (Real.rpow_nonneg hl _)]
  exact hp p.property.1 p.property.2

/-- The actual fractional moment tends to zero, with no analytic input left. -/
theorem short_moment_tendsto_zero :
    Tendsto (fun p : OddPrimeBase => uniformAverage (fun χ : PrimitiveOddFamily p.val =>
      (shortMagnitude p.val χ)^(3/2 : ℝ))) oddPrimeAtTop (𝓝 0) :=
  short_moment_isBigO.trans_tendsto
    ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3/8)).comp
      (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp base_tendsto_atTop)))

end NField.Alignment.MagnitudeShortMomentBound

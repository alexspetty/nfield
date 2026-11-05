/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperLowMomentScales
import NField.Alignment.MagnitudeContinuousFractionalTransfer

/-!
# Applying the unconditional critical moment to the actual character reduction

The logarithm in the continuous main term cancels the numerator of the
critical moment estimate. Both printed full-character bounds retain the
rounded cutoff and the original full-character average.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperLowMomentApplication
open scoped BigOperators
open Filter HarperLowMomentScales HarperRoundedCutoff HarperConditioningDecay
  HarperCriticalLowMoment HarperContinuousReduction HarperSharpProfile
  MagnitudeContinuousFractionalTransfer SpectralRepulsion CollisionCharacterStructure
  PrimeSquareMagnitudeFamily

theorem logarithm_cancellation {x L d : ℝ} (hx : 0 ≤ x) (hL : 0 < L)
    (hd : 0 < d) :
    (48*x/(Real.pi*L))^(3/4 : ℝ)*(L/d)^(3/4 : ℝ) =
      (48/Real.pi)^(3/4 : ℝ)*(x/d)^(3/4 : ℝ) := by
  rw [← Real.mul_rpow (by positivity) (by positivity),
    ← Real.mul_rpow (by positivity) (by positivity)]
  congr 1
  field_simp

theorem eventual_continuous_main_bound : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ p : ℕ in atTop, continuousMainTerm p ≤ C*intermediateScale ((p : ℝ)-1) := by
  obtain ⟨K,hK,hbound⟩ := critical_low_moment
  let C : ℝ := ((2 : ℝ)^(3/4 : ℝ))^2*(profileConstant^(3/4 : ℝ))^2*
    (2*frequencyMass*K)*(48/Real.pi)^(3/4 : ℝ)
  have hfm := frequencyMass_nonneg
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C+1,by positivity,?_⟩
  filter_upwards [base_minus_one_tendsto.eventually (primeCutoff_tendsto.eventually hbound),
    base_minus_one_tendsto.eventually (cutoffLog_tendsto.eventually_gt_atTop 0),
    eventually_ge_atTop (1 : ℕ)] with p hb hl hp
  have hx : 0 ≤ (p : ℝ)-1 := by
    have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hL : 0 < Real.log (primeCutoff ((p : ℝ)-1)) := by rwa [log_primeCutoff]
  have hcancel := logarithm_cancellation hx hL
    (show 0 < 1+(1/4 : ℝ)*Real.sqrt (Real.log (Real.log (primeCutoff ((p : ℝ)-1)))) by positivity)
  calc
    continuousMainTerm p ≤
        ((2 : ℝ)^(3/4 : ℝ))^2*(48*((p : ℝ)-1)/(Real.pi*Real.log (primeCutoff ((p : ℝ)-1))))^(3/4 : ℝ)*
        (profileConstant^(3/4 : ℝ))^2*(2*frequencyMass*
          (K*(Real.log (primeCutoff ((p : ℝ)-1))/(1+(1/4)*Real.sqrt
            (Real.log (Real.log (primeCutoff ((p : ℝ)-1))))))^(3/4 : ℝ))) := by
      unfold continuousMainTerm
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left hb (by positivity)
    _ = C*intermediateScale ((p : ℝ)-1) := by
      dsimp only [C,intermediateScale]
      calc
        _ = (((2 : ℝ)^(3/4 : ℝ))^2*(profileConstant^(3/4 : ℝ))^2*(2*frequencyMass*K))*
          ((48*((p : ℝ)-1)/(Real.pi*Real.log (primeCutoff ((p : ℝ)-1))))^(3/4 : ℝ)*
          (Real.log (primeCutoff ((p : ℝ)-1))/(1+(1/4)*Real.sqrt
            (Real.log (Real.log (primeCutoff ((p : ℝ)-1))))))^(3/4 : ℝ)) := by ring
        _ = _ := by rw [hcancel]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by unfold intermediateScale; positivity)

theorem eventual_continuous_target_bound : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ p : ℕ in atTop, continuousMainTerm p ≤ C*targetScale ((p : ℝ)-1) := by
  obtain ⟨C,hC,hb⟩ := eventual_continuous_main_bound
  refine ⟨C*16,by positivity,?_⟩
  filter_upwards [hb,base_minus_one_tendsto.eventually eventual_scale_comparison] with p hp hs
  exact hp.trans (by nlinarith [mul_le_mul_of_nonneg_left hs.1 hC.le])

end NField.Alignment.HarperLowMomentApplication

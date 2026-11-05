/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperFrequencyTail
import NField.Alignment.HarperSpectralConditioning

/-!
# Localization at the manuscript parameters and negligible frequency tail

The actual random conditioning is reduced to the finite central-frequency
sum plus the literal frequency and smoothing errors. The exact second
moment, proved Mertens bound and log(P)^(-1/300) tail estimate make the
frequency error little-o of the manuscript target scale. The rounded
cutoff asymptotic is used explicitly, and the result is transported to
x=p-1. The central conditional low-moment estimate remains open.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperFrequencyScales

open scoped BigOperators Topology
open MeasureTheory Filter Asymptotics SteinhausMoment HarperEulerIntegral HarperFrequencyIntervals
  HarperFrequencyConditioning HarperFrequencyTail HarperSmoothingConditioning HarperActualConditioning
  HarperWeightedConditioning HarperConditioningFrequencies HarperRoundedCutoff HarperSpectralConditioning
  HarperConditioningDecay HarperSmoothDivisor HarperRoughSmoothing HarperMainConditioning
  CollisionMertensInput

def centralConditioning (p : ℕ) (c1 c2 : Coefficients p) (P : ℝ) : ℝ :=
  ∑ v ∈ centralFrequencies (frequencyCutoff P),
    frequencyWeight (3/2) v * boxConditioning p c1 c2 (unitEnergy P v)

def frequencyTailContribution (x P : ℝ) : ℝ :=
  (24*x*inversePrimeProduct P/(Real.pi*Real.log P))^(3/4 : ℝ)*frequencyTail (frequencyCutoff P)

theorem frequencyTailContribution_nonneg {x P : ℝ} (hx : 0 ≤ x) (hP : 0 < Real.log P) :
    0 ≤ frequencyTailContribution x P := by
  unfold frequencyTailContribution
  have := inversePrimeProduct_pos P
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (frequencyTail_nonneg _)

theorem frequency_coefficient {x P : ℝ} (hx : 0 ≤ x) (hP : 0 < Real.log P) :
    (3*x/(2*Real.pi*Real.log P))^(3/4 : ℝ)*(16 : ℝ)^(3/4 : ℝ)*
      (inversePrimeProduct P)^(3/4 : ℝ) =
    (24*x*inversePrimeProduct P/(Real.pi*Real.log P))^(3/4 : ℝ) := by
  rw [← Real.mul_rpow (by positivity : 0 ≤ 3*x/(2*Real.pi*Real.log P)) (by norm_num),
    ← Real.mul_rpow (by positivity) (inversePrimeProduct_pos P).le]
  congr 1
  field_simp
  ring

theorem eventual_actual_random_localized_with_error : ∀ᶠ p : ℕ in atTop,
    actualRandomConditioning p ≤ (2 : ℝ)^(3/4 : ℝ)*
      ((3*((p : ℝ)-1)/(2*Real.pi*Real.log (primeCutoff ((p : ℝ)-1))))^(3/4 : ℝ)*
        (16 : ℝ)^(3/4 : ℝ)*
          centralConditioning p (firstCoefficient ((p : ℝ)-1)) (secondCoefficient ((p : ℝ)-1))
            (primeCutoff ((p : ℝ)-1)) +
       frequencyTailContribution ((p : ℝ)-1) (primeCutoff ((p : ℝ)-1)) +
       (roughSmoothingError ((p : ℝ)-1) (primeCutoff ((p : ℝ)-1))
         (smoothCutoff ((p : ℝ)-1)) (smoothingScale ((p : ℝ)-1)))^(3/4 : ℝ)) := by
  filter_upwards [eventual_actual_random_spectral_with_error,
    (cutoffLog_tendsto.comp base_minus_one_tendsto).eventually_gt_atTop 0,
    base_minus_one_tendsto.eventually_gt_atTop 0] with p hm hell hx
  have hP : 0 < Real.log (primeCutoff ((p : ℝ)-1)) := by rwa [log_primeCutoff]
  have h := spectral_conditioning_split hell (firstCoefficient ((p : ℝ)-1))
    (secondCoefficient ((p : ℝ)-1)) (primeCutoff ((p : ℝ)-1)) (frequencyCutoff (primeCutoff ((p : ℝ)-1)))
  have hh := hm.trans (mul_le_mul_of_nonneg_left (add_le_add
    (mul_le_mul_of_nonneg_left h (Real.rpow_nonneg (by positivity) _)) le_rfl)
    (Real.rpow_nonneg (by norm_num) _))
  dsimp only [centralConditioning, frequencyTailContribution]
  convert! hh using 1
  rw [← frequency_coefficient hx.le hP]
  ring

theorem inverse_cutoff_power_isLittleO :
    (fun x : ℝ => (cutoffLog x)^(-(1/300 : ℝ))) =o[atTop]
      (fun x => (Real.log (Real.log x))^(-(3/8 : ℝ))) := by
  have h0 : ∀ᶠ t : ℝ in atTop, (Real.log t)^(3/8 : ℝ) = 0 → t^(1/1800 : ℝ) = 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    exact fun h => False.elim ((Real.rpow_pos_of_pos (Real.log_pos ht) _).ne' h)
  have h := (isLittleO_log_rpow_rpow_atTop (3/8 : ℝ)
    (by norm_num : (0 : ℝ) < 1/1800)).inv_rev h0
  have hl : (fun t : ℝ => t^(-(1/1800 : ℝ))) =o[atTop]
      (fun t => (Real.log t)^(-(3/8 : ℝ))) := by
    apply h.congr'
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact (Real.rpow_neg ht _).symm
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      exact (Real.rpow_neg (Real.log_nonneg ht) _).symm
  have he := (Asymptotics.IsEquivalent.rpow cutoffLog_nonneg
    cutoffLog_asymptotic.symm (r := -(1/300 : ℝ))).symm.isBigO
  have hb : (fun x : ℝ => (cutoffLog x)^(-(1/300 : ℝ))) =O[atTop]
      (fun x => (Real.log x)^(-(1/1800 : ℝ))) := by
    apply he.congr' Filter.EventuallyEq.rfl
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    change ((Real.log x)^(1/6 : ℝ))^(-(1/300 : ℝ)) = _
    rw [← Real.rpow_mul (Real.log_nonneg hx)]
    norm_num
  exact hb.trans_isLittleO (hl.comp_tendsto Real.tendsto_log_atTop)


theorem frequencyTailContribution_bound {x P C : ℝ} (hx : 0 ≤ x)
    (hP : 0 < Real.log P) (hC : 0 < C) (hb : inversePrimeProduct P ≤ C*Real.log P) :
    frequencyTailContribution x P ≤ ((24*C/Real.pi)^(3/4 : ℝ)*tailConstant)*
      (x^(3/4 : ℝ)*(Real.log P)^(-(1/300 : ℝ))) := by
  have hprod := inversePrimeProduct_pos P
  have ha : 24*x*inversePrimeProduct P/(Real.pi*Real.log P) ≤ (24*C/Real.pi)*x := by
    apply (div_le_iff₀ (mul_pos Real.pi_pos hP)).mpr
    calc
      _ ≤ (24*x)*(C*Real.log P) := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by field_simp
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ 24*x*inversePrimeProduct P/(Real.pi*Real.log P))
    ha (by norm_num : (0 : ℝ) ≤ 3/4)
  calc
    _ ≤ ((24*C/Real.pi)*x)^(3/4 : ℝ)*((Real.log P)^(-(1/300 : ℝ))*tailConstant) :=
      mul_le_mul hpow (cutoff_tail_bound hP) (frequencyTail_nonneg _)
        (Real.rpow_nonneg (by positivity) _)
    _ = _ := by rw [Real.mul_rpow (by positivity) hx]; ring

theorem frequencyTailContribution_isBigO :
    (fun x => frequencyTailContribution x (primeCutoff x)) =O[atTop]
      (fun x => x^(3/4 : ℝ)*(cutoffLog x)^(-(1/300 : ℝ))) := by
  obtain ⟨C, hC, hb⟩ := inversePrimeProduct_isBigO_log.exists_pos
  apply IsBigO.of_bound ((24*C/Real.pi)^(3/4 : ℝ)*tailConstant)
  filter_upwards [primeCutoff_tendsto.eventually hb.bound, cutoffLog_tendsto.eventually_gt_atTop 0,
    eventually_gt_atTop (0 : ℝ)] with x hbound hell hx
  have hP : 0 < Real.log (primeCutoff x) := by rwa [log_primeCutoff]
  have hprod := inversePrimeProduct_pos (primeCutoff x)
  rw [Real.norm_of_nonneg hprod.le, Real.norm_of_nonneg hP.le] at hbound
  rw [Real.norm_of_nonneg (frequencyTailContribution_nonneg hx.le hP), Real.norm_of_nonneg (by positivity)]
  simpa only [log_primeCutoff] using frequencyTailContribution_bound hx.le hP hC hbound

theorem frequencyTailContribution_isLittleO :
    (fun x => frequencyTailContribution x (primeCutoff x)) =o[atTop] targetScale :=
  frequencyTailContribution_isBigO.trans_isLittleO
    ((isBigO_refl (fun x : ℝ => x^(3/4 : ℝ)) atTop).mul_isLittleO inverse_cutoff_power_isLittleO)

theorem prime_square_frequencyTailContribution_isLittleO :
    (fun p : ℕ => frequencyTailContribution ((p : ℝ)-1) (primeCutoff ((p : ℝ)-1))) =o[atTop]
      (fun p : ℕ => targetScale ((p : ℝ)-1)) :=
  frequencyTailContribution_isLittleO.comp_tendsto base_minus_one_tendsto

end NField.Alignment.HarperFrequencyScales

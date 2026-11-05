/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.MagnitudeShortMomentBound
import NField.Alignment.MagnitudeFiniteDisplayCorrespondence

/-!
# Actual short-magnitude mean rate and variance limit

The unconditional short-moment theorem gives the printed quarter-power
rate after the exact two-thirds power composition. The sample remains
the full primitive odd family along all growing odd primes.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.MagnitudeShortMeanRate
open scoped Topology
open Filter Asymptotics SpectralRepulsion FiniteMagnitudeDecorrelation
  PrimeSquareMagnitudeFamily MagnitudeCubicLimits MagnitudeShortMomentBound

theorem powered_short_moment_bound : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ p : OddPrimeBase in oddPrimeAtTop,
      magnitudeMoment (3/2) (shortMagnitude p.val)^(2/3 : ℝ) ≤
        C*(Real.log (Real.log (p.val : ℝ)))^(-(1/4 : ℝ)) := by
  obtain ⟨C,hC,hb⟩ := eventual_short_moment_bound
  refine ⟨C^(2/3 : ℝ),by positivity,?_⟩
  filter_upwards [Filter.tendsto_comap.eventually hb,
    (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp base_tendsto_atTop)).eventually_ge_atTop 0]
    with p hp hl
  dsimp only [Function.comp_apply] at hl
  have h := Real.rpow_le_rpow
    (moment_nonneg (3/2) (shortMagnitude p.val) (short_magnitude_nonneg p.val))
    (hp p.property.1 p.property.2) (by norm_num : (0 : ℝ) ≤ 2/3)
  rw [Real.mul_rpow hC.le (Real.rpow_nonneg hl _), ← Real.rpow_mul hl] at h
  norm_num only [show (-(3/8 : ℝ))*(2/3)= -(1/4) by norm_num] at h
  exact h

theorem powered_short_moment_isBigO :
    (fun p : OddPrimeBase => magnitudeMoment (3/2) (shortMagnitude p.val)^(2/3 : ℝ))
      =O[oddPrimeAtTop] (fun p => (Real.log (Real.log (p.val : ℝ)))^(-(1/4 : ℝ))) := by
  obtain ⟨C,hC,hb⟩ := powered_short_moment_bound
  apply IsBigO.of_bound C
  filter_upwards [hb,
    (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp base_tendsto_atTop)).eventually_ge_atTop 0]
    with p hp hl
  dsimp only [Function.comp_apply] at hl
  rw [Real.norm_of_nonneg (Real.rpow_nonneg
    (moment_nonneg _ _ (short_magnitude_nonneg p.val)) _),
    Real.norm_of_nonneg (Real.rpow_nonneg hl _)]
  exact hp

theorem short_mean_bound (p : OddPrimeBase) :
    uniformAverage (shortMagnitude p.val) ≤
      magnitudeMoment (3/2) (shortMagnitude p.val)^(2/3 : ℝ) := by
  letI := family_nonempty p.property.1 p.property.2
  exact mean_le_fractional_moment _ (short_magnitude_nonneg p.val)

theorem short_mean_isBigO :
    (fun p : OddPrimeBase => uniformAverage (shortMagnitude p.val)) =O[oddPrimeAtTop]
      (fun p => (Real.log (Real.log (p.val : ℝ)))^(-(1/4 : ℝ))) := by
  apply IsBigO.trans _ powered_short_moment_isBigO
  apply IsBigO.of_bound'
  exact Filter.Eventually.of_forall fun p => by
    rw [Real.norm_of_nonneg (average_nonneg (short_magnitude_nonneg p.val)),
      Real.norm_of_nonneg (Real.rpow_nonneg (moment_nonneg _ _ (short_magnitude_nonneg p.val)) _)]
    exact short_mean_bound p

theorem short_mean_tendsto_zero :
    Tendsto (fun p : OddPrimeBase => uniformAverage (shortMagnitude p.val))
      oddPrimeAtTop (𝓝 0) :=
  short_mean_isBigO.trans_tendsto
    ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/4)).comp
      (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp base_tendsto_atTop)))

theorem short_variance_tendsto_one :
    Tendsto (fun p : OddPrimeBase => uniformVariance (shortMagnitude p.val))
      oddPrimeAtTop (𝓝 1) := by
  have h : Tendsto (fun p : OddPrimeBase => 1-(uniformAverage (shortMagnitude p.val))^2)
      oddPrimeAtTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (short_mean_tendsto_zero.pow 2)
  apply h.congr'
  exact Filter.Eventually.of_forall fun p => by
    letI := family_nonempty p.property.1 p.property.2
    dsimp only
    rw [variance_eq_second_sub_square,short_magnitude_second_moment p.property.1 p.property.2]

theorem eventual_short_variance_positive : ∀ᶠ p : OddPrimeBase in oddPrimeAtTop,
    0 < uniformVariance (shortMagnitude p.val) :=
  short_variance_tendsto_one.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))

end NField.Alignment.MagnitudeShortMeanRate

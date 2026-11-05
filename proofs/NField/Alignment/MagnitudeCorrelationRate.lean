/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.MagnitudeShortMeanRate

/-!
# The unconditional quantitative magnitude correlation theorem

Both variances are eventually positive. The actual finite correlation
inequality, proved uniform third L-moment and proved short-moment rate
give the exact logarithmic exponent -1/4, without any analytic input.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.MagnitudeCorrelationRate
open scoped Topology
open Filter Asymptotics SpectralRepulsion FiniteMagnitudeDecorrelation
  PrimeSquareMagnitudeFamily MagnitudeCubicLimits MagnitudeShortMomentBound
  MagnitudeShortMeanRate MagnitudeFiniteDisplayCorrespondence MagnitudeLMomentBound
  MagnitudeMomentArithmetic

theorem eventual_variances_positive : ∀ᶠ p : OddPrimeBase in oddPrimeAtTop,
    0 < uniformVariance (shortMagnitude p.val) ∧
    0 < uniformVariance (lMagnitude p.val) := by
  filter_upwards [eventual_short_variance_positive,
    Filter.tendsto_comap.eventually (eventually_ge_atTop (5 : ℕ))] with p hs hp
  exact ⟨hs,lt_of_lt_of_le (by positivity : (0 : ℝ) < Real.pi^2/100)
    (l_magnitude_variance_floor p.property.1 hp)⟩

theorem eventual_correlation_moment_bound : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ p : OddPrimeBase in oddPrimeAtTop,
      |familyCorrelation p.val| ≤ C*magnitudeMoment (3/2) (shortMagnitude p.val)^(2/3 : ℝ) := by
  obtain ⟨M4,M,hM4,hM,hthird⟩ := uniform_l_fourth_and_third_moments
  let v : ℝ := Real.pi^2/100
  let C : ℝ := (M^(1/3 : ℝ)+Real.sqrt (Real.pi^2/6))/Real.sqrt (v/2)
  have hv : 0 < v := by dsimp [v]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hH : Tendsto (fun p : OddPrimeBase => magnitudeMoment (3/2) (shortMagnitude p.val))
      oddPrimeAtTop (𝓝 0) := short_moment_tendsto_zero
  have hfour := hH.rpow_const_nhds_zero (by norm_num : (0 : ℝ) < 4/3)
  refine ⟨C,hC,?_⟩
  filter_upwards [hH.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hfour.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2)),
    Filter.tendsto_comap.eventually (eventually_ge_atTop (5 : ℕ))] with p hs hf hp
  have hH0 := moment_nonneg (3/2) (shortMagnitude p.val) (short_magnitude_nonneg p.val)
  have hpow0 := Real.rpow_nonneg hH0 (2/3 : ℝ)
  have h := family_fractional_correlation_bound p.property.1 p.property.2 hv
    (hthird p.val p.property.1 p.property.2).2 (l_magnitude_variance_floor p.property.1 hp) hs
  have hd : Real.sqrt (v/2) ≤
      Real.sqrt (v*(1-magnitudeMoment (3/2) (shortMagnitude p.val)^(4/3 : ℝ))) := by
    apply Real.sqrt_le_sqrt
    nlinarith
  have hd0 : 0 < Real.sqrt (v/2) := by positivity
  have hmarg := Real.sqrt_le_sqrt (marginal_upper (p.val : ℝ))
  calc
    _ ≤ ((M^(1/3 : ℝ)+Real.sqrt (marginalL p.val))*
        magnitudeMoment (3/2) (shortMagnitude p.val)^(2/3 : ℝ))/
        Real.sqrt (v*(1-magnitudeMoment (3/2) (shortMagnitude p.val)^(4/3 : ℝ))) := h
    _ ≤ ((M^(1/3 : ℝ)+Real.sqrt (marginalL p.val))*
        magnitudeMoment (3/2) (shortMagnitude p.val)^(2/3 : ℝ))/Real.sqrt (v/2) :=
      div_le_div_of_nonneg_left (by positivity) hd0 hd
    _ ≤ ((M^(1/3 : ℝ)+Real.sqrt (Real.pi^2/6))*
        magnitudeMoment (3/2) (shortMagnitude p.val)^(2/3 : ℝ))/Real.sqrt (v/2) := by
      apply div_le_div_of_nonneg_right _ hd0.le
      exact mul_le_mul_of_nonneg_right (add_le_add le_rfl hmarg) hpow0
    _ = _ := by dsimp [C]; ring

theorem eventual_correlation_rate : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ p : OddPrimeBase in oddPrimeAtTop,
      |familyCorrelation p.val| ≤ C*(Real.log (Real.log (p.val : ℝ)))^(-(1/4 : ℝ)) := by
  obtain ⟨C,hC,hb⟩ := eventual_correlation_moment_bound
  obtain ⟨D,hD,hd⟩ := powered_short_moment_bound
  refine ⟨C*D,by positivity,?_⟩
  filter_upwards [hb,hd] with p hp hq
  exact hp.trans (by nlinarith [mul_le_mul_of_nonneg_left hq hC.le])

theorem correlation_isBigO :
    (fun p : OddPrimeBase => familyCorrelation p.val) =O[oddPrimeAtTop]
      (fun p => (Real.log (Real.log (p.val : ℝ)))^(-(1/4 : ℝ))) := by
  obtain ⟨C,hC,hb⟩ := eventual_correlation_rate
  apply IsBigO.of_bound C
  filter_upwards [hb,
    (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp base_tendsto_atTop)).eventually_ge_atTop 0]
    with p hp hl
  dsimp only [Function.comp_apply] at hl
  rw [Real.norm_eq_abs,Real.norm_of_nonneg (Real.rpow_nonneg hl _)]
  exact hp

theorem correlation_tendsto_zero :
    Tendsto (fun p : OddPrimeBase => familyCorrelation p.val) oddPrimeAtTop (𝓝 0) :=
  correlation_isBigO.trans_tendsto
    ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/4)).comp
      (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp base_tendsto_atTop)))

/-- All clauses of Theorem 1, including the eventual definedness of Pearson
correlation rather than only a limit of a totalized quotient. -/
theorem magnitude_correlation_theorem :
    (∀ᶠ p : OddPrimeBase in oddPrimeAtTop,
      0 < uniformVariance (shortMagnitude p.val) ∧ 0 < uniformVariance (lMagnitude p.val)) ∧
    (fun p : OddPrimeBase => familyCorrelation p.val) =O[oddPrimeAtTop]
      (fun p => (Real.log (Real.log (p.val : ℝ)))^(-(1/4 : ℝ))) ∧
    Tendsto (fun p : OddPrimeBase => familyCorrelation p.val) oddPrimeAtTop (𝓝 0) :=
  ⟨eventual_variances_positive,correlation_isBigO,correlation_tendsto_zero⟩

/-- All three decay inputs in display 038 are now proved for the actual
family, with fixed positive constants and the full odd-prime filter. -/
theorem actual_decay_inputs : ∃ M v : ℝ, 0 < M ∧ 0 < v ∧
    (fun p : OddPrimeBase => magnitudeMoment (3/2) (shortMagnitude p.val))
      =o[oddPrimeAtTop] (fun _ => (1 : ℝ)) ∧
    ∀ᶠ p : OddPrimeBase in oddPrimeAtTop,
      uniformAverage (fun χ : PrimitiveOddFamily p.val => lMagnitude p.val χ^3) ≤ M ∧
      v ≤ uniformVariance (lMagnitude p.val) := by
  obtain ⟨M4,M,hM4,hM,hb⟩ := uniform_l_fourth_and_third_moments
  refine ⟨M,Real.pi^2/100,hM,by positivity,
    (isLittleO_one_iff ℝ).2 short_moment_tendsto_zero,?_⟩
  filter_upwards [Filter.tendsto_comap.eventually (eventually_ge_atTop (5 : ℕ))] with p hp
  exact ⟨(hb p.val p.property.1 p.property.2).2,l_magnitude_variance_floor p.property.1 hp⟩

end NField.Alignment.MagnitudeCorrelationRate

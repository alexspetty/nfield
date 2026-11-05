/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperRestrictedMoment

/-!
# Restricted moments with the proved logarithmic normalizer

The existing Mertens product bound removes the exact prime-product
normalizer from the restricted estimate. One fixed block offset and one
constant work for all sufficiently large x, all a >= 1, and all q in
[0,1]. No exceptional-event estimate is assumed or concluded.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperRestrictedLogMoment
open Filter MeasureTheory Set SteinhausMoment HarperPrimeBlocks HarperFrequencyIntervals
  HarperCriticalGoodEvent HarperGoodEventCutoff HarperRestrictedMoment
  CollisionMertensInput HarperSmoothCount HarperSmoothDivisor

theorem sourceCutoff_tendsto : Tendsto sourceCutoff atTop atTop :=
  tendsto_rpow_atTop (by positivity : (0 : ℝ) < 1/Real.exp 1)

theorem restricted_energy_log :
    ∃ B : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, ∀ a : ℝ, 1 ≤ a →
      (∫ ω in sourceGoodEvent x (terminalBlock B x) a,
        unitEnergy (sourceCutoff x) 0 ω ∂phaseMeasure) ≤
      C*Real.log (sourceCutoff x)*min 1 (a/Real.sqrt (Real.log (Real.log x))) := by
  obtain ⟨B,C,hC,hbound⟩ := restricted_energy_fixed_offset
  obtain ⟨D,hD,hprod⟩ := inversePrimeProduct_isBigO_log.exists_pos
  refine ⟨B,C*D,mul_pos hC hD,?_⟩
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (2*((B : ℝ)+2)),
    sourceCutoff_tendsto.eventually hprod.bound,
    sourceCutoff_tendsto.eventually_ge_atTop (1 : ℝ)] with x hx hlarge hprod hxP
  intro a ha
  have hp : inversePrimeProduct (sourceCutoff x) ≤ D*Real.log (sourceCutoff x) := by
    simpa only [Real.norm_eq_abs,abs_of_pos (inversePrimeProduct_pos _),
      abs_of_nonneg (Real.log_nonneg hxP)] using hprod
  apply (hbound x hx hlarge a ha).trans
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hC.le)
    (show 0 ≤ min 1 (a/Real.sqrt (Real.log (Real.log x))) by
      apply le_min (by norm_num)
      exact div_nonneg (by linarith) (Real.sqrt_nonneg _))
  simpa only [mul_assoc] using hm

theorem restricted_fractional_log :
    ∃ B : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, ∀ a : ℝ, 1 ≤ a →
      ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      (∫ ω, ((sourceGoodEvent x (terminalBlock B x) a).indicator
        (unitEnergy (sourceCutoff x) 0) ω)^q ∂phaseMeasure) ≤
      (C*Real.log (sourceCutoff x)*min 1 (a/Real.sqrt (Real.log (Real.log x))))^q := by
  obtain ⟨B,C,hC,hbound⟩ := restricted_energy_log
  refine ⟨B,C,hC,?_⟩
  filter_upwards [hbound] with x hx
  intro a ha q hq0 hq1
  have hG := sourceGoodEvent_measurable x (terminalBlock B x) a
  have hi := (unitEnergy_integrable (sourceCutoff x) 0).indicator hG
  have hf : ∀ ω, 0 ≤ (sourceGoodEvent x (terminalBlock B x) a).indicator
      (unitEnergy (sourceCutoff x) 0) ω := Set.indicator_nonneg (fun ω _ => unitEnergy_nonneg _ _ ω)
  apply (nonnegative_fractional_jensen hi hf hq0 hq1).trans
  apply Real.rpow_le_rpow (integral_nonneg hf) _ hq0
  rw [integral_indicator hG]
  exact hx a ha

end NField.Alignment.HarperRestrictedLogMoment

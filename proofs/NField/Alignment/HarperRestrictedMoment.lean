/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperGoodEventCutoff
import NField.Alignment.HarperReverseGrid

/-!
# Restricted critical moments at the actual source cutoff

One fixed natural offset selects the terminal block. The checked barrier
and energy identity give the full restricted first-moment saving, with
the exact reciprocal-prime normalizer. Probability Jensen extends it
uniformly to every exponent in [0,1]. Exceptional-event estimates and
the unconditional moment recursion are separate obligations.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperRestrictedMoment
open scoped BigOperators
open MeasureTheory Set SteinhausMoment HarperPrimeBlocks HarperFrequencyIntervals
  HarperCriticalGoodEvent HarperGoodAllowance HarperGoodEventCutoff HarperRestrictedEnergy
  HarperSourceBarrierBound CollisionMertensInput

theorem restricted_energy_fixed_offset :
    ∃ B : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 < x →
      2*((B : ℝ)+2) ≤ Real.log (Real.log x) → ∀ a : ℝ, 1 ≤ a →
      (∫ ω in sourceGoodEvent x (terminalBlock B x) a,
        unitEnergy (sourceCutoff x) 0 ω ∂phaseMeasure) ≤
      C*inversePrimeProduct (sourceCutoff x)*min 1 (a/Real.sqrt (Real.log (Real.log x))) := by
  obtain ⟨X₀,hX₀⟩ := actual_restricted_unitEnergy
  obtain ⟨B,hB⟩ := exists_nat_ge X₀
  let C : ℝ := 2*sourceBarrierConstant 11*(3*(B : ℝ)+9)
  have hS := sourceBarrierConstant_ge_two (show (0 : ℝ) ≤ 11 by norm_num)
  have hB0 := Nat.cast_nonneg (α := ℝ) B
  have hC : 1 ≤ C := by dsimp [C]; nlinarith
  refine ⟨B,C,by linarith,fun x hx hlarge a ha => ?_⟩
  have hfloor := terminalBlock_large_condition hlarge
  have h := hX₀ x hx (terminalBlock B x) (terminalBlock_threshold hB hx hfloor) a (by linarith)
  have hamp := terminal_pathAmplitude hx hfloor ha
  have hlength := terminalBlock_length hlarge
  have hs : 0 < Real.sqrt (Real.log (Real.log x)) := Real.sqrt_pos.mpr (by linarith)
  have hn : 0 < Real.sqrt ((terminalBlock B x+1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hP := inversePrimeProduct_pos (sourceCutoff x)
  by_cases hr : a/Real.sqrt (Real.log (Real.log x)) ≤ 1
  · rw [min_eq_right hr]
    calc
      _ ≤ _ := h
      _ ≤ inversePrimeProduct (sourceCutoff x)*sourceBarrierConstant 11*
          (pathAmplitude x (terminalBlock B x) a/Real.sqrt ((terminalBlock B x+1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (mul_nonneg hP.le (by linarith))
      _ ≤ inversePrimeProduct (sourceCutoff x)*sourceBarrierConstant 11*
          (((3*(B : ℝ)+9)*a)/Real.sqrt ((terminalBlock B x+1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hamp hn.le)
          (mul_nonneg hP.le (by linarith))
      _ ≤ _ := by
        rw [← mul_div_assoc,← mul_div_assoc]
        apply (div_le_div_iff₀ hn hs).mpr
        have hm := mul_le_mul_of_nonneg_left hlength
          (show 0 ≤ inversePrimeProduct (sourceCutoff x)*sourceBarrierConstant 11*((3*(B : ℝ)+9)*a) by
            apply mul_nonneg (mul_nonneg hP.le (by linarith))
            apply mul_nonneg <;> linarith)
        dsimp [C]
        nlinarith
  · rw [min_eq_left (le_of_not_ge hr),mul_one]
    have hu : (∫ ω in sourceGoodEvent x (terminalBlock B x) a,
        unitEnergy (sourceCutoff x) 0 ω ∂phaseMeasure) ≤ inversePrimeProduct (sourceCutoff x) := by
      rw [← unitEnergy_mean (sourceCutoff x) 0]
      exact setIntegral_le_integral (unitEnergy_integrable _ _) (ae_of_all _ (unitEnergy_nonneg _ _))
    exact hu.trans (by nlinarith)

theorem nonnegative_fractional_integrable {f : PhaseSpace → ℝ}
    (hi : Integrable f phaseMeasure) (hf : ∀ ω, 0 ≤ f ω)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Integrable (fun ω => (f ω)^q) phaseMeasure := by
  have h := integrable_norm_rpow_of_le hi.aestronglyMeasurable hq0
    (by norm_num : (0 : ℝ) ≤ 1) hq1 (by simpa only [Real.rpow_one] using hi.norm)
  simpa only [Real.norm_of_nonneg (hf _)] using h

theorem nonnegative_fractional_jensen {f : PhaseSpace → ℝ}
    (hi : Integrable f phaseMeasure) (hf : ∀ ω, 0 ≤ f ω)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∫ ω, (f ω)^q ∂phaseMeasure) ≤ (∫ ω, f ω ∂phaseMeasure)^q := by
  exact (Real.concaveOn_rpow hq0 hq1).le_map_integral
    (Real.continuous_rpow_const hq0).continuousOn isClosed_Ici
    (ae_of_all _ hf) hi (nonnegative_fractional_integrable hi hf hq0 hq1)

theorem restricted_fractional_fixed_offset :
    ∃ B : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 < x →
      2*((B : ℝ)+2) ≤ Real.log (Real.log x) → ∀ a : ℝ, 1 ≤ a →
      ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      (∫ ω, ((sourceGoodEvent x (terminalBlock B x) a).indicator
        (unitEnergy (sourceCutoff x) 0) ω)^q ∂phaseMeasure) ≤
      (C*inversePrimeProduct (sourceCutoff x)*min 1 (a/Real.sqrt (Real.log (Real.log x))))^q := by
  obtain ⟨B,C,hC,hbound⟩ := restricted_energy_fixed_offset
  refine ⟨B,C,hC,fun x hx hlarge a ha q hq0 hq1 => ?_⟩
  have hG := sourceGoodEvent_measurable x (terminalBlock B x) a
  have hi := (unitEnergy_integrable (sourceCutoff x) 0).indicator hG
  have hf : ∀ ω, 0 ≤ (sourceGoodEvent x (terminalBlock B x) a).indicator
      (unitEnergy (sourceCutoff x) 0) ω := Set.indicator_nonneg (fun ω _ => unitEnergy_nonneg _ _ ω)
  apply (nonnegative_fractional_jensen hi hf hq0 hq1).trans
  apply Real.rpow_le_rpow (integral_nonneg hf) _ hq0
  rw [integral_indicator hG]
  exact hbound x hx hlarge a ha

end NField.Alignment.HarperRestrictedMoment

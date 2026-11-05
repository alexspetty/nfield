/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperExceptionalEvent

/-!
# One actual good event for both energy saving and failure decay

The terminal offset is chosen above both proved thresholds. The energy
and failure estimates therefore refer to exactly the same event, with
constants fixed before x, amplitude and fractional exponent.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperJointGoodEvent
open scoped BigOperators
open Filter MeasureTheory Set SteinhausMoment HarperPrimeBlocks HarperFrequencyIntervals
  HarperCriticalGoodEvent HarperGoodAllowance HarperGoodEventCutoff HarperRestrictedEnergy
  HarperSourceBarrierBound CollisionMertensInput HarperExceptionalEvent
  HarperRestrictedMoment HarperRestrictedLogMoment HarperSmoothDivisor

theorem restricted_energy_all_large_offsets :
    ∃ B₀ : ℕ, ∀ B : ℕ, B₀ ≤ B → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 < x →
      2*((B : ℝ)+2) ≤ Real.log (Real.log x) → ∀ a : ℝ, 1 ≤ a →
      (∫ ω in sourceGoodEvent x (terminalBlock B x) a,
        unitEnergy (sourceCutoff x) 0 ω ∂phaseMeasure) ≤
      C*inversePrimeProduct (sourceCutoff x)*min 1 (a/Real.sqrt (Real.log (Real.log x))) := by
  obtain ⟨X₀,hX₀⟩ := actual_restricted_unitEnergy
  obtain ⟨B₀,hB₀⟩ := exists_nat_ge X₀
  refine ⟨B₀,fun B hBB => ?_⟩
  have hB : X₀ ≤ (B : ℝ) := hB₀.trans (by exact_mod_cast hBB)
  let C : ℝ := 2*sourceBarrierConstant 11*(3*(B : ℝ)+9)
  have hS := sourceBarrierConstant_ge_two (show (0 : ℝ) ≤ 11 by norm_num)
  have hB0 := Nat.cast_nonneg (α := ℝ) B
  have hC : 1 ≤ C := by dsimp [C]; nlinarith
  refine ⟨C,by linarith,fun x hx hlarge a ha => ?_⟩
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


theorem joint_good_event_bounds :
    ∃ B : ℕ, ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ᶠ x : ℝ in atTop, ∀ a : ℝ, 1 ≤ a →
      (∫ ω in sourceGoodEvent x (terminalBlock B x) a,
        unitEnergy (sourceCutoff x) 0 ω ∂phaseMeasure) ≤
          C*Real.log (sourceCutoff x)*min 1 (a/Real.sqrt (Real.log (Real.log x))) ∧
      phaseMeasure.real (sourceGoodEvent x (terminalBlock B x) a)ᶜ ≤ D*Real.exp (-2*a) := by
  obtain ⟨B₀,henergy⟩ := restricted_energy_all_large_offsets
  obtain ⟨X₀,D,hD,hfailure⟩ := source_failure_exponential
  obtain ⟨B,hB⟩ := exists_nat_ge (max (B₀ : ℝ) X₀)
  have hBB : B₀ ≤ B := by exact_mod_cast (le_max_left _ _).trans hB
  have hBX : X₀ ≤ (B : ℝ) := (le_max_right _ _).trans hB
  obtain ⟨C,hC,hbound⟩ := henergy B hBB
  obtain ⟨K,hK,hprod⟩ := inversePrimeProduct_isBigO_log.exists_pos
  refine ⟨B,C*K,D,mul_pos hC hK,hD,?_⟩
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (2*((B : ℝ)+2)),
    sourceCutoff_tendsto.eventually hprod.bound,
    sourceCutoff_tendsto.eventually_ge_atTop (1 : ℝ)] with x hx hlarge hprod hxP
  intro a ha
  constructor
  · have hp : inversePrimeProduct (sourceCutoff x) ≤ K*Real.log (sourceCutoff x) := by
      simpa only [Real.norm_eq_abs,abs_of_pos (inversePrimeProduct_pos _),
        abs_of_nonneg (Real.log_nonneg hxP)] using hprod
    apply (hbound x hx hlarge a ha).trans
    have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hC.le)
      (show 0 ≤ min 1 (a/Real.sqrt (Real.log (Real.log x))) by
        apply le_min (by norm_num)
        exact div_nonneg (by linarith) (Real.sqrt_nonneg _))
    simpa only [mul_assoc] using hm
  · exact hfailure x hx (terminalBlock B x)
      (terminalBlock_threshold hBX hx (terminalBlock_large_condition hlarge)) a

theorem joint_fractional_good_event_bounds :
    ∃ B : ℕ, ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ᶠ x : ℝ in atTop, ∀ a : ℝ, 1 ≤ a →
      ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      (∫ ω, ((sourceGoodEvent x (terminalBlock B x) a).indicator
        (unitEnergy (sourceCutoff x) 0) ω)^q ∂phaseMeasure) ≤
          (C*Real.log (sourceCutoff x)*min 1 (a/Real.sqrt (Real.log (Real.log x))))^q ∧
      phaseMeasure.real (sourceGoodEvent x (terminalBlock B x) a)ᶜ ≤ D*Real.exp (-2*a) := by
  obtain ⟨B,C,D,hC,hD,hbound⟩ := joint_good_event_bounds
  refine ⟨B,C,D,hC,hD,?_⟩
  filter_upwards [hbound] with x hx
  intro a ha q hq0 hq1
  refine ⟨?_,(hx a ha).2⟩
  have hG := sourceGoodEvent_measurable x (terminalBlock B x) a
  have hi := (unitEnergy_integrable (sourceCutoff x) 0).indicator hG
  have hf : ∀ ω, 0 ≤ (sourceGoodEvent x (terminalBlock B x) a).indicator
      (unitEnergy (sourceCutoff x) 0) ω := Set.indicator_nonneg (fun ω _ => unitEnergy_nonneg _ _ ω)
  apply (nonnegative_fractional_jensen hi hf hq0 hq1).trans
  apply Real.rpow_le_rpow (integral_nonneg hf) _ hq0
  rw [integral_indicator hG]
  exact (hx a ha).1

end NField.Alignment.HarperJointGoodEvent

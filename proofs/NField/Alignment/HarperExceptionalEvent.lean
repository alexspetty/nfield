/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperExceptionalScaleSum

/-!
# Exponential failure probability for the actual critical good event

The literal per-code tails, finite frequency count and inverse-cube scale
sum discharge every probability input in the earlier union bound.
All constants are independent of the source amplitude and path length.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperExceptionalEvent
open scoped BigOperators
open MeasureTheory Filter SteinhausMoment HarperPrimeBlocks HarperFrequencyMesh
  HarperCriticalGoodEvent HarperGoodEventUnion HarperGoodAllowance HarperGoodEventCutoff
  HarperSuffixLogTail HarperExceptionalScaleSum

theorem source_failure_exponential :
    ∃ X₀ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 < x → ∀ M : ℕ,
      X₀ ≤ blockUpper x M → ∀ a : ℝ,
      phaseMeasure.real (sourceGoodEvent x M a)ᶜ ≤ C*Real.exp (-2*a) := by
  obtain ⟨X₀,C,hC,htail⟩ := suffix_source_tail
  refine ⟨max X₀ (Real.exp (Real.exp 2)),5*C*scaleTailConstant,by
    exact mul_pos (by positivity) scaleTailConstant_pos,fun x hx M hM a => ?_⟩
  have hLM : Real.exp 2 ≤ logScale x M := by
    have h := Real.log_le_log (Real.exp_pos (Real.exp 2)) ((le_max_right _ _).trans hM)
    simpa only [Real.log_exp,logScale] using h
  have hc : 1 ≤ terminalLogScale x M := by
    have h := Real.log_le_log (Real.exp_pos 2) hLM
    rw [Real.log_exp] at h
    exact (by norm_num : (1 : ℝ) ≤ 2).trans h
  let p : ℕ → ℝ := fun j => C*Real.exp (-2*a)/(logScale x j*(Real.log (logScale x j))^4)
  have hp : ∀ j ≤ M, 0 ≤ p j := by
    intro j hj
    have hL : 0 < logScale x j := (Real.exp_pos 2).trans_le (hLM.trans (logScale_antitone hx hj))
    dsimp [p]
    positivity
  have h := goodEvent_failure_card_bound hx M hLM (sourceAllowance x a) p phaseMeasure hp
    (fun j _ _ => htail x hx M ((le_max_left _ _).trans hM) j.val (by omega) a _)
  change phaseMeasure.real (sourceGoodEvent x M a)ᶜ ≤ _ at h
  apply h.trans
  calc
    _ ≤ ∑ j : Fin (M+1), 5*(C*Real.exp (-2*a))/(Real.log (logScale x j.val))^3 := by
      apply Finset.sum_le_sum
      intro j _
      exact code_weight_tail_bound (hLM.trans (logScale_antitone hx (by omega))) (by positivity)
    _ = (5*C*Real.exp (-2*a)) * ∑ j : Fin (M+1), 1/(Real.log (logScale x j.val))^3 := by
      simp only [Finset.mul_sum,div_eq_mul_inv,one_mul,mul_assoc]
    _ ≤ (5*C*Real.exp (-2*a))*scaleTailConstant :=
      mul_le_mul_of_nonneg_left (inverse_cube_scale_sum hx M hc) (by positivity)
    _ = _ := by ring

theorem source_failure_fixed_offset :
    ∃ B : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 < x →
      2*((B : ℝ)+2) ≤ Real.log (Real.log x) → ∀ a : ℝ,
      phaseMeasure.real (sourceGoodEvent x (terminalBlock B x) a)ᶜ ≤ C*Real.exp (-2*a) := by
  obtain ⟨X₀,C,hC,hbound⟩ := source_failure_exponential
  obtain ⟨B,hB⟩ := exists_nat_ge X₀
  refine ⟨B,C,hC,fun x hx hlarge a => ?_⟩
  exact hbound x hx (terminalBlock B x)
    (terminalBlock_threshold hB hx (terminalBlock_large_condition hlarge)) a

theorem source_failure_eventually :
    ∃ B : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, ∀ a : ℝ,
      phaseMeasure.real (sourceGoodEvent x (terminalBlock B x) a)ᶜ ≤ C*Real.exp (-2*a) := by
  obtain ⟨B,C,hC,hbound⟩ := source_failure_fixed_offset
  refine ⟨B,C,hC,?_⟩
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (2*((B : ℝ)+2))]
    with x hx hlarge
  exact hbound x hx hlarge

end NField.Alignment.HarperExceptionalEvent

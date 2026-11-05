/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperEulerLogComparison

/-!
# Moderate Euler-product samples and the remaining extreme moment

The exact logarithmic comparison places every moderate sample inside the
actual partition range eventually, uniformly over all conditioning indices.
The moderate and extreme energies split the literal sample square; their
measurability and integrability are proved. An exact Markov-type bound
reduces the extreme energy to the 11/5 Euler-product moment with the
required logarithmic powers. The downstream `HarperEulerFractionalMoment`
module proves the logarithmic moment estimate; this module supplies its
exact extreme-energy consumer.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperModerateSamples
open scoped BigOperators Topology Classical
open MeasureTheory Filter Asymptotics SteinhausMoment HarperRandomEulerProduct HarperEulerIntegral
  HarperEulerSecondMoment HarperEulerLogComparison HarperConditioningFrequencies
  HarperRoundedCutoff HarperPrimeTaylorComparison HarperParameterBounds HarperSmoothDivisor

def moderateSample (P t : ℝ) (ω : PhaseSpace) : Prop :=
  (Real.log P)^(-(11/10 : ℝ)) < ‖eulerProduct P (linePoint (1/2) t) ω‖ ∧
    ‖eulerProduct P (linePoint (1/2) t) ω‖ < (Real.log P)^(11/10 : ℝ)
def moderateEnergy (P t : ℝ) (ω : PhaseSpace) : ℝ :=
  if moderateSample P t ω then ‖eulerProduct P (linePoint (1/2) t) ω‖^2 else 0
def extremeEnergy (P t : ℝ) (ω : PhaseSpace) : ℝ :=
  if moderateSample P t ω then 0 else ‖eulerProduct P (linePoint (1/2) t) ω‖^2

theorem moderateSample_measurableSet (P t : ℝ) : MeasurableSet {ω | moderateSample P t ω} :=
  (measurableSet_lt measurable_const (eulerProduct_measurable P _).norm).inter
    (measurableSet_lt (eulerProduct_measurable P _).norm measurable_const)

theorem moderateEnergy_integrable (P t : ℝ) : Integrable (moderateEnergy P t) phaseMeasure :=
  (eulerProduct_norm_sq_integrable P (by norm_num [linePoint_re])).indicator (moderateSample_measurableSet P t)

theorem extremeEnergy_integrable (P t : ℝ) : Integrable (extremeEnergy P t) phaseMeasure := by
  have h := (eulerProduct_norm_sq_integrable P (s := linePoint (1/2) t)
    (by norm_num [linePoint_re])).indicator
    (moderateSample_measurableSet P t).compl
  convert! h using 1
  funext ω
  simp only [Set.indicator_apply, Set.mem_compl_iff, Set.mem_setOf_eq, extremeEnergy]
  split_ifs <;> rfl

theorem moderateEnergy_nonneg (P t : ℝ) (ω : PhaseSpace) : 0 ≤ moderateEnergy P t ω := by
  unfold moderateEnergy
  split_ifs <;> positivity

theorem extremeEnergy_nonneg (P t : ℝ) (ω : PhaseSpace) : 0 ≤ extremeEnergy P t ω := by
  unfold extremeEnergy
  split_ifs <;> positivity

theorem moderate_extreme_split (P t : ℝ) (ω : PhaseSpace) :
    moderateEnergy P t ω+extremeEnergy P t ω = ‖eulerProduct P (linePoint (1/2) t) ω‖^2 := by
  unfold moderateEnergy extremeEnergy
  split_ifs <;> simp

theorem moderate_log_bound {P : ℝ} (hP : 0 < Real.log P) (t : ℝ) (ω : PhaseSpace)
    (h : moderateSample P t ω) :
    |Real.log ‖eulerProduct P (linePoint (1/2) t) ω‖| ≤ (11/10 : ℝ)*Real.log (Real.log P) := by
  have hn := norm_pos_iff.mpr (eulerProduct_critical_ne_zero P t ω)
  have hlo := Real.log_le_log (Real.rpow_pos_of_pos hP (-(11/10 : ℝ))) h.1.le
  have hhi := Real.log_le_log hn h.2.le
  rw [Real.log_rpow hP] at hlo hhi
  exact abs_le.mpr ⟨by linarith, hhi⟩

theorem moderate_prime_sum_bound {P : ℝ} (hP : 0 < Real.log P) (t : ℝ) (ω : PhaseSpace)
    (h : moderateSample P t ω) :
    |quadraticPrimeSum P t ω| ≤ (11/10 : ℝ)*Real.log (Real.log P)+logRemainderConstant := by
  have he := log_eulerProduct_quadratic_bound P t ω
  have hl := moderate_log_bound hP t ω h
  calc
    _ ≤ |Real.log ‖eulerProduct P (linePoint (1/2) t) ω‖|+
        |quadraticPrimeSum P t ω-Real.log ‖eulerProduct P (linePoint (1/2) t) ω‖| := by
      simpa only [add_sub_cancel] using abs_add_le
        (Real.log ‖eulerProduct P (linePoint (1/2) t) ω‖)
        (quadraticPrimeSum P t ω-Real.log ‖eulerProduct P (linePoint (1/2) t) ω‖)
    _ ≤ _ := add_le_add hl (by rwa [abs_sub_comm])

theorem eventual_moderate_prime_sum_range : ∀ᶠ P : ℝ in atTop,
    ∀ t : ℝ, ∀ ω : PhaseSpace, moderateSample P t ω →
      |quadraticPrimeSum P t ω| ≤ (rangeCount (Real.log P) : ℝ) := by
  filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 0,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (10*logRemainderConstant)]
    with P hP hlog hlarge
  intro t ω h
  have hb := moderate_prime_sum_bound hP t ω h
  have hr := (rangeCount_bounds hP hlog).2.1
  dsimp only [Function.comp_apply] at hlarge
  linarith

theorem eventual_actual_moderate_primeArgument_range : ∀ᶠ x : ℝ in atTop,
    ∀ i : Fin (factorCount x), ∀ ω : PhaseSpace, moderateSample (primeCutoff x) (frequency x i) ω →
      |primeArgument (primeCutoff x) (firstCoefficient x i) (secondCoefficient x i)
        (fun n => steinhaus n ω)| ≤ (rangeCount (cutoffLog x) : ℝ) := by
  filter_upwards [primeCutoff_tendsto.eventually eventual_moderate_prime_sum_range] with x h
  intro i ω hmod
  simpa only [log_primeCutoff, quadraticPrimeSum_eq_primeArgument] using h (frequency x i) ω hmod

theorem norm_rpow_integrable (P t : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    Integrable (fun ω => ‖eulerProduct P (linePoint (1/2) t) ω‖^r) phaseMeasure := by
  apply Integrable.of_bound ((eulerProduct_measurable P _).norm.pow_const r).aestronglyMeasurable
    ((HarperSmoothCount.shiftedProduct P (1/2))^r)
  apply Filter.Eventually.of_forall
  intro ω
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  have h := eulerProduct_norm_le P (s := linePoint (1/2) t) (by norm_num [linePoint_re]) ω
  rw [linePoint_re] at h
  exact Real.rpow_le_rpow (norm_nonneg _) h hr


theorem moderateEnergy_le_square (P t : ℝ) (ω : PhaseSpace) :
    moderateEnergy P t ω ≤ ‖eulerProduct P (linePoint (1/2) t) ω‖^2 := by
  unfold moderateEnergy
  split_ifs
  · exact le_rfl
  · exact sq_nonneg _

theorem moderateEnergy_size_bound {P : ℝ} (hP : 0 < Real.log P) (t : ℝ) (ω : PhaseSpace) :
    moderateEnergy P t ω ≤ (Real.log P)^(11/5 : ℝ) := by
  unfold moderateEnergy
  split_ifs with h
  · have hh := pow_le_pow_left₀ (norm_nonneg _) h.2.le 2
    rw [← Real.rpow_mul_natCast hP.le] at hh
    norm_num at hh
    exact hh
  · exact Real.rpow_nonneg hP.le _

theorem extreme_scalar_bound {L a : ℝ} (hL : 0 < L) (ha : 0 ≤ a) :
    (if L^(-(11/10 : ℝ)) < a ∧ a < L^(11/10 : ℝ) then 0 else a^2) ≤
      L^(-(11/50 : ℝ))*a^(11/5 : ℝ)+L^(-(11/5 : ℝ)) := by
  split_ifs with h
  · positivity
  · have hh : a ≤ L^(-(11/10 : ℝ)) ∨ L^(11/10 : ℝ) ≤ a := by
      by_cases hlo : L^(-(11/10 : ℝ)) < a
      · exact Or.inr (le_of_not_gt (fun hhi => h ⟨hlo,hhi⟩))
      · exact Or.inl (le_of_not_gt hlo)
    rcases hh with hlo | hhi
    · have hb := pow_le_pow_left₀ ha hlo 2
      rw [← Real.rpow_mul_natCast hL.le] at hb
      norm_num at hb
      exact hb.trans (le_add_of_nonneg_left (by positivity))
    · have hap : 0 < a := (Real.rpow_pos_of_pos hL _).trans_le hhi
      have hp := Real.rpow_le_rpow (Real.rpow_nonneg hL.le _) hhi
        (by norm_num : (0 : ℝ) ≤ 1/5)
      rw [← Real.rpow_mul hL.le] at hp
      norm_num at hp
      have hf : 1 ≤ L^(-(11/50 : ℝ))*a^(1/5 : ℝ) := by
        calc
          _ = L^(-(11/50 : ℝ))*L^(11/50 : ℝ) := by rw [← Real.rpow_add hL]; norm_num
          _ ≤ _ := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hL.le _)
      have he : a^2*(L^(-(11/50 : ℝ))*a^(1/5 : ℝ)) = L^(-(11/50 : ℝ))*a^(11/5 : ℝ) := by
        rw [mul_left_comm, ← Real.rpow_natCast a 2, ← Real.rpow_add hap]
        norm_num
      calc
        _ ≤ a^2*(L^(-(11/50 : ℝ))*a^(1/5 : ℝ)) := by nlinarith [sq_nonneg a]
        _ = _ := he
        _ ≤ _ := le_add_of_nonneg_right (Real.rpow_nonneg hL.le _)

theorem extremeEnergy_point_bound {P : ℝ} (hP : 0 < Real.log P) (t : ℝ) (ω : PhaseSpace) :
    extremeEnergy P t ω ≤ (Real.log P)^(-(11/50 : ℝ))*
      ‖eulerProduct P (linePoint (1/2) t) ω‖^(11/5 : ℝ)+(Real.log P)^(-(11/5 : ℝ)) := by
  have h := extreme_scalar_bound hP (norm_nonneg (eulerProduct P (linePoint (1/2) t) ω))
  unfold extremeEnergy
  by_cases hm : moderateSample P t ω
  · rw [if_pos hm]
    positivity
  · rw [if_neg hm]
    have hn : ¬((Real.log P)^(-(11/10 : ℝ)) < ‖eulerProduct P (linePoint (1/2) t) ω‖ ∧
        ‖eulerProduct P (linePoint (1/2) t) ω‖ < (Real.log P)^(11/10 : ℝ)) := hm
    rwa [if_neg hn] at h

theorem extremeEnergy_expectation_bound {P : ℝ} (hP : 0 < Real.log P) (t : ℝ) :
    (∫ ω, extremeEnergy P t ω ∂phaseMeasure) ≤ (Real.log P)^(-(11/50 : ℝ))*
      (∫ ω, ‖eulerProduct P (linePoint (1/2) t) ω‖^(11/5 : ℝ) ∂phaseMeasure)+
        (Real.log P)^(-(11/5 : ℝ)) := by
  have hi := norm_rpow_integrable P t (by norm_num : (0 : ℝ) ≤ 11/5)
  calc
    _ ≤ ∫ ω, (Real.log P)^(-(11/50 : ℝ))*‖eulerProduct P (linePoint (1/2) t) ω‖^(11/5 : ℝ)+
        (Real.log P)^(-(11/5 : ℝ)) ∂phaseMeasure :=
      integral_mono (extremeEnergy_integrable P t) ((hi.const_mul _).add (integrable_const _))
        (extremeEnergy_point_bound hP t)
    _ = _ := by rw [integral_add (hi.const_mul _) (integrable_const _), integral_const_mul]; simp

end NField.Alignment.HarperModerateSamples

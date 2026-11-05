/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperEulerFractionalMoment

/-!
# Removing extreme amplitudes from the actual finite grid

The moderate and extreme grid energies split the literal discrete energy
exactly. The grid cardinality and normalization preserve the uniform
O(log(P)^(99/100)) extreme expectation bound. Fractional subadditivity and
weighted Holder pass this error through the full box functional, retaining
zero-weight boxes and every actual grid sample.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperExtremeGrid
open scoped BigOperators Topology
open MeasureTheory Filter Asymptotics SteinhausMoment HarperModerateSamples HarperEulerFractionalMoment
  HarperEulerGridComparison HarperEulerDiscretization HarperSmoothingConditioning HarperActualConditioning
  HarperRoughSmoothing HarperWeightedConditioning HarperRoundedCutoff

def moderateGridEnergy (P v : ℝ) (ω : PhaseSpace) : ℝ :=
  (∑ k ∈ gridCenters (gridScale P), moderateEnergy P (v+(k : ℝ)/gridScale P) ω)/gridScale P
def extremeGridEnergy (P v : ℝ) (ω : PhaseSpace) : ℝ :=
  (∑ k ∈ gridCenters (gridScale P), extremeEnergy P (v+(k : ℝ)/gridScale P) ω)/gridScale P

theorem moderateGridEnergy_integrable (P v : ℝ) : Integrable (moderateGridEnergy P v) phaseMeasure :=
  (integrable_finsetSum _ (fun _ _ => moderateEnergy_integrable P _)).div_const _

theorem extremeGridEnergy_integrable (P v : ℝ) : Integrable (extremeGridEnergy P v) phaseMeasure :=
  (integrable_finsetSum _ (fun _ _ => extremeEnergy_integrable P _)).div_const _

theorem moderateGridEnergy_nonneg {P : ℝ} (hD : 0 ≤ gridScale P) (v : ℝ) (ω : PhaseSpace) :
    0 ≤ moderateGridEnergy P v ω :=
  div_nonneg (Finset.sum_nonneg (fun _ _ => moderateEnergy_nonneg P _ ω)) hD

theorem extremeGridEnergy_nonneg {P : ℝ} (hD : 0 ≤ gridScale P) (v : ℝ) (ω : PhaseSpace) :
    0 ≤ extremeGridEnergy P v ω :=
  div_nonneg (Finset.sum_nonneg (fun _ _ => extremeEnergy_nonneg P _ ω)) hD

theorem moderate_extreme_grid_split (P v : ℝ) (ω : PhaseSpace) :
    moderateGridEnergy P v ω+extremeGridEnergy P v ω = discreteEnergy P v ω := by
  unfold moderateGridEnergy extremeGridEnergy discreteEnergy
  rw [← add_div, ← Finset.sum_add_distrib]
  simp only [moderate_extreme_split]

theorem extremeGridEnergy_expectation_bound (P v : ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hD : 1 ≤ gridScale P) (hb : ∀ t : ℝ, (∫ ω, extremeEnergy P t ω ∂phaseMeasure) ≤ B) :
    (∫ ω, extremeGridEnergy P v ω ∂phaseMeasure) ≤ 2*B := by
  have hD0 : 0 < gridScale P := lt_of_lt_of_le zero_lt_one hD
  unfold extremeGridEnergy
  rw [integral_div, integral_finsetSum _ (fun k _ => extremeEnergy_integrable P _)]
  calc
    _ ≤ (∑ _k ∈ gridCenters (gridScale P), B)/gridScale P :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun k _ => hb _)) hD0.le
    _ = ((gridCenters (gridScale P)).card : ℝ)/gridScale P*B := by simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      ((div_le_iff₀ hD0).mpr (gridCenters_card_bound hD)) hB

theorem eventual_extremeGridEnergy_bound : ∃ C : ℝ, 0 < C ∧ ∀ᶠ P : ℝ in atTop,
    ∀ v : ℝ, (∫ ω, extremeGridEnergy P v ω ∂phaseMeasure) ≤ C*(Real.log P)^(99/100 : ℝ) := by
  obtain ⟨C,hC,hb⟩ := eventual_extremeEnergy_bound
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [hb,Real.tendsto_log_atTop.eventually_ge_atTop 1] with P hbound hP
  intro v
  have hD : 1 ≤ gridScale P := Real.one_le_rpow hP (by norm_num)
  have h := extremeGridEnergy_expectation_bound P v
    (show 0 ≤ C*(Real.log P)^(99/100 : ℝ) by positivity) hD hbound
  convert h using 1
  ring

theorem conditioning_add_bound {ι : Type*} [Fintype ι] (w a b c : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hc : ∀ i, 0 ≤ c i)
    (hsum : ∑ i, w i = 1) (hbound : ∀ i, a i ≤ b i+c i) :
    conditioningSum Finset.univ w a ≤ conditioningSum Finset.univ w b+(∑ i, c i)^(3/4 : ℝ) := by
  have hpoint (i : ι) : (w i)^(1/4 : ℝ)*(a i)^(3/4 : ℝ) ≤
      (w i)^(1/4 : ℝ)*(b i)^(3/4 : ℝ)+(w i)^(1/4 : ℝ)*(c i)^(3/4 : ℝ) := by
    have hpow := (Real.rpow_le_rpow (ha i) (hbound i) (by norm_num : (0 : ℝ) ≤ 3/4)).trans
      (Real.rpow_add_le_add_rpow (hb i) (hc i) (by norm_num) (by norm_num))
    exact (mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg (hw i) _)).trans_eq (mul_add _ _ _)
  have hholder := weighted_holder Finset.univ w c (fun i _ => hw i) (fun i _ => hc i)
  rw [hsum, Real.one_rpow, one_mul] at hholder
  calc
    _ ≤ conditioningSum Finset.univ w b+conditioningSum Finset.univ w c := by
      unfold conditioningSum
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum (fun i _ => hpoint i)
    _ ≤ _ := add_le_add le_rfl hholder

theorem boxMoment_add {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1)) (c1 c2 : Coefficients p)
    (i : Boxes p) {F G : PhaseSpace → ℝ} (hF : Integrable F phaseMeasure) (hG : Integrable G phaseMeasure) :
    boxMoment p c1 c2 i (fun ω => F ω+G ω) = boxMoment p c1 c2 i F+boxMoment p c1 c2 i G := by
  unfold boxMoment
  simp only [add_mul]
  exact integral_add (boxMoment_integrable hell c1 c2 i hF) (boxMoment_integrable hell c1 c2 i hG)

theorem boxConditioning_add_bound {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1)) (c1 c2 : Coefficients p)
    {F G : PhaseSpace → ℝ} (hF : Integrable F phaseMeasure) (hG : Integrable G phaseMeasure)
    (hF0 : ∀ ω, 0 ≤ F ω) (hG0 : ∀ ω, 0 ≤ G ω) :
    boxConditioning p c1 c2 (fun ω => F ω+G ω) ≤
      boxConditioning p c1 c2 F+(∫ ω, G ω ∂phaseMeasure)^(3/4 : ℝ) := by
  have h := conditioning_add_bound (randomWeight p c1 c2)
    (fun i => boxMoment p c1 c2 i (fun ω => F ω+G ω))
    (fun i => boxMoment p c1 c2 i F) (fun i => boxMoment p c1 c2 i G)
    (randomWeight_nonneg hell c1 c2)
    (fun i => boxMoment_nonneg hell c1 c2 i (fun ω => add_nonneg (hF0 ω) (hG0 ω)))
    (fun i => boxMoment_nonneg hell c1 c2 i hF0) (fun i => boxMoment_nonneg hell c1 c2 i hG0)
    (randomWeight_sum hell c1 c2) (fun i => (boxMoment_add hell c1 c2 i hF hG).le)
  rwa [boxMoment_sum hell c1 c2 hG] at h

theorem discreteEnergy_conditioning_split {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (c1 c2 : Coefficients p) {P : ℝ} (hD : 0 ≤ gridScale P) (v : ℝ) :
    boxConditioning p c1 c2 (discreteEnergy P v) ≤
      boxConditioning p c1 c2 (moderateGridEnergy P v)+
        (∫ ω, extremeGridEnergy P v ω ∂phaseMeasure)^(3/4 : ℝ) := by
  have he : discreteEnergy P v = (fun ω => moderateGridEnergy P v ω+extremeGridEnergy P v ω) := by
    funext ω
    exact (moderate_extreme_grid_split P v ω).symm
  rw [he]
  exact boxConditioning_add_bound hell c1 c2 (moderateGridEnergy_integrable P v)
    (extremeGridEnergy_integrable P v) (moderateGridEnergy_nonneg hD v) (extremeGridEnergy_nonneg hD v)

end NField.Alignment.HarperExtremeGrid

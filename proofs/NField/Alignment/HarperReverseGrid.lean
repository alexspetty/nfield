/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperPhaseShift
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# The actual discrete fractional moment compared with a unit integral

Every original grid cell, including the boundary cells, is retained in
the reverse squared-triangle comparison. The cells fit inside a length-two
interval. Splitting it into adjacent unit windows and using actual Haar
shift invariance gives a bound by the continuous unit fractional moment
and the existing grid-error expectation. Probability Jensen is proved
with integrability and nonnegativity, not assumed as a moment estimate.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperReverseGrid
open scoped BigOperators Topology
open MeasureTheory Filter SteinhausMoment HarperRandomEulerProduct HarperEulerIntegral
  HarperEulerSecondMoment HarperEulerIncrement HarperEulerDiscretization
  HarperEulerGridComparison HarperFrequencyIntervals HarperUnconditioning HarperPhaseShift

def unitFractionalMoment (P : ℝ) : ℝ :=
  ∫ ω, (unitEnergy P 0 ω)^(3/4 : ℝ) ∂phaseMeasure

theorem sample_le_shifted_and_increment (P u t : ℝ) (ω : PhaseSpace) :
    verticalEnergy P (1/2) (u,ω) ≤
      2*verticalEnergy P (1/2) (u+t,ω)+2*incrementEnergy P u t ω := by
  let a := eulerProduct P (linePoint (1/2) (u+t)) ω
  let b := eulerProduct P (linePoint (1/2) u) ω
  change ‖b‖^2 ≤ 2*‖a‖^2+2*‖a-b‖^2
  have hn : ‖b‖ ≤ ‖a‖+‖a-b‖ := by
    simpa only [sub_sub_cancel] using norm_sub_le a (a-b)
  have hs := pow_le_pow_left₀ (norm_nonneg b) hn 2
  nlinarith [sq_nonneg (‖a‖-‖a-b‖)]

theorem sample_div_le_gridCell (P v : ℝ) {D : ℝ} (hD : 0 < D) (k : ℤ) (ω : PhaseSpace) :
    verticalEnergy P (1/2) (v+(k : ℝ)/D,ω)/D ≤
      2*(∫ s in gridCell D v k, verticalEnergy P (1/2) (s,ω))+
        2*cellError P (v+(k : ℝ)/D) (1/(2*D)) ω := by
  have hh : -(1/(2*D)) ≤ 1/(2*D) := by
    have : 0 ≤ 1/(2*D) := by positivity
    linarith
  have hi := shiftedEnergy_integrable P (v+(k : ℝ)/D) (1/(2*D)) ω
  have he := incrementEnergy_integrable_line P (v+(k : ℝ)/D) (1/(2*D)) ω
  rw [gridCell_integral_eq P v hD]
  calc
    _ = ∫ _t in Set.Ioc (-(1/(2*D))) (1/(2*D)),
        verticalEnergy P (1/2) (v+(k : ℝ)/D,ω) := by
      rw [integral_const, measureReal_restrict_apply_univ, Real.volume_real_Ioc_of_le hh]
      simp only [smul_eq_mul]
      ring
    _ ≤ ∫ t in Set.Ioc (-(1/(2*D))) (1/(2*D)),
        2*verticalEnergy P (1/2) (v+(k : ℝ)/D+t,ω)+
          2*incrementEnergy P (v+(k : ℝ)/D) t ω :=
      integral_mono (integrable_const _) ((hi.const_mul 2).add (he.const_mul 2))
        (fun t => sample_le_shifted_and_increment P _ t ω)
    _ = _ := by
      rw [integral_add (hi.const_mul 2) (he.const_mul 2)]
      simp only [integral_const_mul, cellError]

theorem gridCell_subset_double {D : ℝ} (hD : 1 ≤ D) (v : ℝ) {k : ℤ}
    (hk : k ∈ gridCenters D) : gridCell D v k ⊆ Set.Ioc (v-1) (v+1) := by
  have hD0 : 0 < D := by linarith
  have hkb := abs_le.mp ((gridCenters_mem D k).mp hk)
  have hlo : -1 ≤ ((k : ℝ)-1/2)/D := (le_div_iff₀ hD0).mpr (by linarith [hkb.1])
  have hhi : ((k : ℝ)+1/2)/D ≤ 1 := (div_le_iff₀ hD0).mpr (by linarith [hkb.2])
  intro t ht
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

theorem discreteEnergy_le_double_interval {P : ℝ} (hD : 1 ≤ gridScale P) (v : ℝ) (ω : PhaseSpace) :
    discreteEnergy P v ω ≤
      2*intervalEnergy P (1/2) (v-1) (v+1) ω+2*gridError P v ω := by
  have hD0 : 0 < gridScale P := by linarith
  have hi : ∀ k ∈ gridCenters (gridScale P),
      IntegrableOn (fun t => verticalEnergy P (1/2) (t,ω)) (gridCell (gridScale P) v k) :=
    fun k _ => verticalEnergy_integrable_line P _ _ ω
  have hu : (∫ t in ⋃ k ∈ gridCenters (gridScale P), gridCell (gridScale P) v k,
      verticalEnergy P (1/2) (t,ω)) =
      ∑ k ∈ gridCenters (gridScale P),
        ∫ t in gridCell (gridScale P) v k, verticalEnergy P (1/2) (t,ω) :=
    integral_biUnion_finset _ (fun _ _ => measurableSet_Ioc)
      (fun _ _ _ _ hkl => gridCell_disjoint hD0 v hkl) hi
  have hsub : (⋃ k ∈ gridCenters (gridScale P), gridCell (gridScale P) v k) ⊆
      Set.Ioc (v-1) (v+1) := by
    intro t ht
    rcases Set.mem_iUnion.mp ht with ⟨k,hk⟩
    rcases Set.mem_iUnion.mp hk with ⟨hk,ht⟩
    exact gridCell_subset_double hD v hk ht
  have hsum : (∑ k ∈ gridCenters (gridScale P),
      ∫ t in gridCell (gridScale P) v k, verticalEnergy P (1/2) (t,ω)) ≤
      intervalEnergy P (1/2) (v-1) (v+1) ω := by
    rw [← hu]
    exact setIntegral_mono_set (verticalEnergy_integrable_line P _ _ ω)
      (Eventually.of_forall (fun _ => sq_nonneg _)) (Eventually.of_forall hsub)
  calc
    _ = ∑ k ∈ gridCenters (gridScale P),
        verticalEnergy P (1/2) (v+(k : ℝ)/gridScale P,ω)/gridScale P := by
      simp only [discreteEnergy, Finset.sum_div, verticalEnergy]
    _ ≤ ∑ k ∈ gridCenters (gridScale P),
        (2*(∫ t in gridCell (gridScale P) v k, verticalEnergy P (1/2) (t,ω))+
          2*cellError P (v+(k : ℝ)/gridScale P) (1/(2*gridScale P)) ω) :=
      Finset.sum_le_sum (fun k _ => sample_div_le_gridCell P v hD0 k ω)
    _ = 2*(∑ k ∈ gridCenters (gridScale P),
        ∫ t in gridCell (gridScale P) v k, verticalEnergy P (1/2) (t,ω))+2*gridError P v ω := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, gridError]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hsum (by norm_num)) le_rfl

theorem fractional_integrable {f : PhaseSpace → ℝ} (hi : Integrable f phaseMeasure)
    (hn : ∀ ω, 0 ≤ f ω) : Integrable (fun ω => (f ω)^(3/4 : ℝ)) phaseMeasure := by
  have h := integrable_norm_rpow_of_le hi.aestronglyMeasurable
    (by norm_num : (0 : ℝ) ≤ 3/4) (by norm_num : (0 : ℝ) ≤ 1)
    (by norm_num : (3/4 : ℝ) ≤ 1) (by simpa only [Real.rpow_one] using hi.norm)
  simpa only [Real.norm_of_nonneg (hn _)] using h

theorem fractional_integral_le {f : PhaseSpace → ℝ} (hi : Integrable f phaseMeasure)
    (hn : ∀ ω, 0 ≤ f ω) :
    (∫ ω, (f ω)^(3/4 : ℝ) ∂phaseMeasure) ≤ (∫ ω, f ω ∂phaseMeasure)^(3/4 : ℝ) := by
  exact (Real.concaveOn_rpow (by norm_num : (0 : ℝ) ≤ 3/4) (by norm_num : (3/4 : ℝ) ≤ 1)).le_map_integral
    (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 3/4)).continuousOn isClosed_Ici
    (Eventually.of_forall hn) hi (fractional_integrable hi hn)

theorem interval_fractional_integrable (P a b : ℝ) :
    Integrable (fun ω => (intervalEnergy P (1/2) a b ω)^(3/4 : ℝ)) phaseMeasure :=
  fractional_integrable (intervalEnergy_integrable P a b (by norm_num)) (intervalEnergy_nonneg P _ a b)

theorem unitFractionalMoment_nonneg (P : ℝ) : 0 ≤ unitFractionalMoment P :=
  integral_nonneg (fun ω => Real.rpow_nonneg (unitEnergy_nonneg P 0 ω) _)

theorem intervalFractionalMoment_unit (P v : ℝ) :
    (∫ ω, (intervalEnergy P (1/2) (v-1/2) (v+1/2) ω)^(3/4 : ℝ) ∂phaseMeasure) =
      unitFractionalMoment P := by
  have h := intervalFractionalMoment_shift P (1/2) (3/4) v
    (a := -(1/2 : ℝ)) (b := 1/2) (by norm_num)
  rw [show -(1/2 : ℝ)+v = v-1/2 by ring, show (1/2 : ℝ)+v = v+1/2 by ring] at h
  simpa only [unitFractionalMoment, unitEnergy, Int.cast_zero, zero_sub, zero_add] using h

theorem double_interval_split (P v : ℝ) (ω : PhaseSpace) :
    intervalEnergy P (1/2) (v-1) (v+1) ω =
      intervalEnergy P (1/2) (v-1) v ω+intervalEnergy P (1/2) v (v+1) ω := by
  unfold intervalEnergy
  rw [← Set.Ioc_union_Ioc_eq_Ioc (show v-1 ≤ v by linarith) (show v ≤ v+1 by linarith)]
  exact setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
    (verticalEnergy_integrable_line P _ _ ω) (verticalEnergy_integrable_line P _ _ ω)

theorem double_interval_fractional_bound (P v : ℝ) :
    (∫ ω, (intervalEnergy P (1/2) (v-1) (v+1) ω)^(3/4 : ℝ) ∂phaseMeasure) ≤
      2*unitFractionalMoment P := by
  have hleft : (∫ ω, (intervalEnergy P (1/2) (v-1) v ω)^(3/4 : ℝ) ∂phaseMeasure) =
      unitFractionalMoment P := by
    have h := intervalFractionalMoment_unit P (v-1/2)
    rwa [show (v-1/2)-1/2 = v-1 by ring, show (v-1/2)+1/2 = v by ring] at h
  have hright : (∫ ω, (intervalEnergy P (1/2) v (v+1) ω)^(3/4 : ℝ) ∂phaseMeasure) =
      unitFractionalMoment P := by
    have h := intervalFractionalMoment_unit P (v+1/2)
    rwa [show (v+1/2)-1/2 = v by ring, show (v+1/2)+1/2 = v+1 by ring] at h
  calc
    _ ≤ ∫ ω, (intervalEnergy P (1/2) (v-1) v ω)^(3/4 : ℝ)+
        (intervalEnergy P (1/2) v (v+1) ω)^(3/4 : ℝ) ∂phaseMeasure := by
      apply integral_mono (interval_fractional_integrable P _ _)
        ((interval_fractional_integrable P _ _).add (interval_fractional_integrable P _ _))
      intro ω
      dsimp only [Pi.add_apply]
      rw [double_interval_split]
      exact Real.rpow_add_le_add_rpow (intervalEnergy_nonneg P _ _ _ ω)
        (intervalEnergy_nonneg P _ _ _ ω) (by norm_num) (by norm_num)
    _ = _ := by
      rw [integral_add (interval_fractional_integrable P _ _) (interval_fractional_integrable P _ _),
        hleft, hright]
      ring

theorem unconditionalGridMoment_le_unit {P : ℝ} (hD : 1 ≤ gridScale P) (v : ℝ) :
    unconditionalGridMoment P v ≤ (2 : ℝ)^(3/4 : ℝ)*
      (2*unitFractionalMoment P+(∫ ω, gridError P v ω ∂phaseMeasure)^(3/4 : ℝ)) := by
  have hD0 : 0 ≤ gridScale P := by linarith
  have hiE := interval_fractional_integrable P (v-1) (v+1)
  have hiG := fractional_integrable (gridError_integrable P v) (gridError_nonneg P v)
  have hp (ω : PhaseSpace) : (discreteEnergy P v ω)^(3/4 : ℝ) ≤
      (2 : ℝ)^(3/4 : ℝ)*((intervalEnergy P (1/2) (v-1) (v+1) ω)^(3/4 : ℝ)+
        (gridError P v ω)^(3/4 : ℝ)) := by
    have h := Real.rpow_le_rpow (discreteEnergy_nonneg hD0 v ω)
      (discreteEnergy_le_double_interval hD v ω) (by norm_num : (0 : ℝ) ≤ 3/4)
    calc
      _ ≤ (2*intervalEnergy P (1/2) (v-1) (v+1) ω+2*gridError P v ω)^(3/4 : ℝ) := h
      _ ≤ (2*intervalEnergy P (1/2) (v-1) (v+1) ω)^(3/4 : ℝ)+(2*gridError P v ω)^(3/4 : ℝ) :=
        Real.rpow_add_le_add_rpow (mul_nonneg (by norm_num) (intervalEnergy_nonneg P _ _ _ ω))
          (mul_nonneg (by norm_num) (gridError_nonneg P v ω))
          (by norm_num) (by norm_num)
      _ = _ := by
        rw [Real.mul_rpow (by norm_num) (intervalEnergy_nonneg P _ _ _ ω),
          Real.mul_rpow (by norm_num) (gridError_nonneg P v ω)]
        ring
  calc
    _ ≤ ∫ ω, (2 : ℝ)^(3/4 : ℝ)*((intervalEnergy P (1/2) (v-1) (v+1) ω)^(3/4 : ℝ)+
        (gridError P v ω)^(3/4 : ℝ)) ∂phaseMeasure :=
      integral_mono (discreteEnergy_fractional_integrable hD0 v) ((hiE.add hiG).const_mul _) hp
    _ = (2 : ℝ)^(3/4 : ℝ)*((∫ ω, (intervalEnergy P (1/2) (v-1) (v+1) ω)^(3/4 : ℝ) ∂phaseMeasure)+
        (∫ ω, (gridError P v ω)^(3/4 : ℝ) ∂phaseMeasure)) := by
      rw [integral_const_mul, integral_add hiE hiG]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add (double_interval_fractional_bound P v)
        (fractional_integral_le (gridError_integrable P v) (gridError_nonneg P v))) (by positivity)

end NField.Alignment.HarperReverseGrid

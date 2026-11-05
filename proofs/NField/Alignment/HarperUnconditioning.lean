/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperProfileGrid

/-!
# Removing the actual sharp box conditioning

A deterministic label profile moves the three-quarter power outside the
conditional expectation. Finite weighted Holder controls the rejected
profile pointwise, with zero box weights permitted. Integrating gives the
ordinary fractional moment of the original Euler-product grid plus its
explicit profile correction. No low-moment saving is asserted here.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperUnconditioning
open scoped BigOperators Topology Classical
open MeasureTheory Filter Asymptotics SteinhausMoment HarperSharpGrid HarperSharpProfile HarperProfileGrid
  HarperActualSharpConditioning HarperRandomEulerProduct HarperEulerIntegral
  HarperEulerDiscretization HarperEulerGridComparison HarperFrequencyTail
  HarperConditioningFrequencies HarperRoundedCutoff HarperActualConditioning HarperRoughSmoothing
  HarperMainConditioning HarperWeightedConditioning

def profileAverage (p : ℕ) (v : ℤ) : ℝ :=
  ∑ labels : Boxes p, randomWeight p (firstCoefficient ((p : ℝ)-1)) (secondCoefficient ((p : ℝ)-1)) labels*
    (gridProfile p labels v)^(3/4 : ℝ)
def profileIntegrand (p : ℕ) (v : ℤ) (ω : PhaseSpace) : ℝ :=
  ∑ labels : Boxes p, (gridProfile p labels v)^(3/4 : ℝ)*
    smoothBox p (firstCoefficient ((p : ℝ)-1)) (secondCoefficient ((p : ℝ)-1)) labels (fun n => steinhaus n ω)
def unconditionalGridMoment (P v : ℝ) : ℝ :=
  ∫ ω, (discreteEnergy P v ω)^(3/4 : ℝ) ∂phaseMeasure

theorem weighted_profile_identity {w U : ℝ} (hw : 0 ≤ w) (hU : 0 ≤ U) :
    w^(1/4 : ℝ)*(w*U)^(3/4 : ℝ) = w*U^(3/4 : ℝ) := by
  rw [Real.mul_rpow hw hU, ← mul_assoc, ← Real.rpow_add' hw (by norm_num : (1/4 : ℝ)+3/4 ≠ 0)]
  norm_num

theorem finite_profile_comparison {ι : Type*} [Fintype ι] (w U R : ι → ℝ) {A H B : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hU : ∀ i, 0 ≤ U i) (hR : ∀ i, 0 ≤ R i)
    (hA : 0 ≤ A) (hH : 0 ≤ H) (hs : ∑ i, w i = 1)
    (hpoint : ∀ i, U i ≤ A*H+R i) (hb : ∑ i, w i*R i ≤ B) :
    (∑ i, w i*(U i)^(3/4 : ℝ)) ≤ A^(3/4 : ℝ)*H^(3/4 : ℝ)+B^(3/4 : ℝ) := by
  have hh := weighted_holder Finset.univ w (fun i => w i*R i)
    (fun i _ => hw i) (fun i _ => mul_nonneg (hw i) (hR i))
  unfold conditioningSum at hh
  simp_rw [weighted_profile_identity (hw _) (hR _)] at hh
  rw [hs, Real.one_rpow, one_mul] at hh
  have he := hh.trans (Real.rpow_le_rpow (Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (hR i)))
    hb (by norm_num : (0 : ℝ) ≤ 3/4))
  calc
    _ ≤ ∑ i, w i*((A*H)^(3/4 : ℝ)+(R i)^(3/4 : ℝ)) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hw i)
      exact (Real.rpow_le_rpow (hU i) (hpoint i) (by norm_num : (0 : ℝ) ≤ 3/4)).trans
        (Real.rpow_add_le_add_rpow (mul_nonneg hA hH) (hR i) (by norm_num) (by norm_num))
    _ = A^(3/4 : ℝ)*H^(3/4 : ℝ)+∑ i, w i*(R i)^(3/4 : ℝ) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hs, one_mul, Real.mul_rpow hA hH]
    _ ≤ _ := add_le_add le_rfl he

theorem retainedGridMoment_le_weighted_profile {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (labels : Boxes p) (v : ℤ) : retainedGridMoment p labels v ≤
      profileConstant*(randomWeight p (firstCoefficient ((p : ℝ)-1)) (secondCoefficient ((p : ℝ)-1)) labels*
        gridProfile p labels v) := by
  have h := boxMoment_mono hell (firstCoefficient ((p : ℝ)-1)) (secondCoefficient ((p : ℝ)-1)) labels
    (retainedGridEnergy_integrable p labels v) (integrable_const (profileConstant*gridProfile p labels v))
    (retainedGridEnergy_le_profile hell labels v)
  convert! h using 1
  unfold boxMoment randomWeight
  rw [integral_const_mul]
  ring

theorem sharpGridConditioning_le_profileAverage {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1)) (v : ℤ) :
    sharpGridConditioning p v ≤ profileConstant^(3/4 : ℝ)*profileAverage p v := by
  unfold sharpGridConditioning conditioningSum profileAverage
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro labels _
  have hw := randomWeight_nonneg hell (firstCoefficient ((p : ℝ)-1)) (secondCoefficient ((p : ℝ)-1)) labels
  have hU := gridProfile_nonneg hell labels v
  have h := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (retainedGridMoment_nonneg hell labels v)
      (retainedGridMoment_le_weighted_profile hell labels v) (by norm_num : (0 : ℝ) ≤ 3/4))
    (Real.rpow_nonneg hw (1/4 : ℝ))
  rw [Real.mul_rpow profileConstant_pos.le (mul_nonneg hw hU), mul_left_comm,
    weighted_profile_identity hw hU] at h
  exact h

theorem profileIntegrand_integrable {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1)) (v : ℤ) :
    Integrable (profileIntegrand p v) phaseMeasure :=
  integrable_finsetSum _ (fun labels _ => boxMoment_integrable hell _ _ labels (integrable_const _))

theorem profileAverage_eq_integral {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1)) (v : ℤ) :
    profileAverage p v = ∫ ω, profileIntegrand p v ω ∂phaseMeasure := by
  unfold profileAverage profileIntegrand
  rw [integral_finsetSum _ (fun labels _ => boxMoment_integrable hell _ _ labels (integrable_const _))]
  apply Finset.sum_congr rfl
  intro labels _
  rw [integral_const_mul]
  exact mul_comm _ _

theorem profileIntegrand_bound {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (hD : 1 ≤ gridScale (primeCutoff ((p : ℝ)-1))) (v : ℤ)
    (hv : v ∈ centralFrequencies (frequencyCutoff (primeCutoff ((p : ℝ)-1)))) (ω : PhaseSpace) :
    profileIntegrand p v ω ≤ profileConstant^(3/4 : ℝ)*
      (discreteEnergy (primeCutoff ((p : ℝ)-1)) v ω)^(3/4 : ℝ)+(profileRejectionBound p)^(3/4 : ℝ) := by
  have h := finite_profile_comparison
    (fun labels => smoothBox p (firstCoefficient ((p : ℝ)-1)) (secondCoefficient ((p : ℝ)-1)) labels (fun n => steinhaus n ω))
    (fun labels => gridProfile p labels v) (fun labels => profileRejectedGrid p labels v ω)
    (fun labels => smoothBox_nonneg hell _ _ labels _) (fun labels => gridProfile_nonneg hell labels v)
    (fun labels => profileRejectedGrid_nonneg hell labels v ω) profileConstant_pos.le
    (discreteEnergy_nonneg (actual_gridScale_pos hell).le v ω) (smoothBox_sum p _ _ _)
    (fun labels => gridProfile_le_energy_add_rejected hell labels v hv ω)
    (by simpa only [mul_comm] using weighted_profileRejectedGrid_bound hell hD v ω)
  simpa only [profileIntegrand, mul_comm] using h

theorem discreteEnergy_fractional_integrable {P : ℝ} (hD : 0 ≤ gridScale P) (v : ℝ) :
    Integrable (fun ω => (discreteEnergy P v ω)^(3/4 : ℝ)) phaseMeasure := by
  have hi := discreteEnergy_integrable P v
  have h := integrable_norm_rpow_of_le hi.aestronglyMeasurable
    (by norm_num : (0 : ℝ) ≤ 3/4) (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (3/4 : ℝ) ≤ 1)
    (by simpa only [Real.rpow_one] using hi.norm)
  simpa only [Real.norm_of_nonneg (discreteEnergy_nonneg hD v _)] using h

theorem unconditionalGridMoment_nonneg {P : ℝ} (hD : 0 ≤ gridScale P) (v : ℝ) :
    0 ≤ unconditionalGridMoment P v :=
  integral_nonneg (fun ω => Real.rpow_nonneg (discreteEnergy_nonneg hD v ω) _)

theorem profileAverage_bound {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (hD : 1 ≤ gridScale (primeCutoff ((p : ℝ)-1))) (v : ℤ)
    (hv : v ∈ centralFrequencies (frequencyCutoff (primeCutoff ((p : ℝ)-1)))) :
    profileAverage p v ≤ profileConstant^(3/4 : ℝ)*unconditionalGridMoment (primeCutoff ((p : ℝ)-1)) v+
      (profileRejectionBound p)^(3/4 : ℝ) := by
  rw [profileAverage_eq_integral hell]
  have hi := discreteEnergy_fractional_integrable (actual_gridScale_pos hell).le (v : ℝ)
  calc
    _ ≤ ∫ ω, profileConstant^(3/4 : ℝ)*(discreteEnergy (primeCutoff ((p : ℝ)-1)) v ω)^(3/4 : ℝ)+
        (profileRejectionBound p)^(3/4 : ℝ) ∂phaseMeasure :=
      integral_mono (profileIntegrand_integrable hell v) ((hi.const_mul _).add (integrable_const _))
        (profileIntegrand_bound hell hD v hv)
    _ = _ := by
      rw [integral_add (hi.const_mul _) (integrable_const _), integral_const_mul]
      simp only [integral_const, probReal_univ, one_smul]
      rfl

theorem sharpGridConditioning_bound {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (hD : 1 ≤ gridScale (primeCutoff ((p : ℝ)-1))) (v : ℤ)
    (hv : v ∈ centralFrequencies (frequencyCutoff (primeCutoff ((p : ℝ)-1)))) :
    sharpGridConditioning p v ≤ profileConstant^(3/4 : ℝ)*
      (profileConstant^(3/4 : ℝ)*unconditionalGridMoment (primeCutoff ((p : ℝ)-1)) v+
        (profileRejectionBound p)^(3/4 : ℝ)) :=
  (sharpGridConditioning_le_profileAverage hell v).trans
    (mul_le_mul_of_nonneg_left (profileAverage_bound hell hD v hv) (Real.rpow_nonneg profileConstant_pos.le _))

end NField.Alignment.HarperUnconditioning

/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperSharpProfile

/-!
# The actual deterministic grid profile and its rejected mass

The retained grid is bounded by a deterministic label profile. At each
original central frequency the profile is bounded back by the actual full
Euler-product grid and a rejected-profile correction. Exact marginalization
and the original grid cardinality bound control that correction pointwise.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperProfileGrid
open scoped BigOperators Topology Classical
open MeasureTheory Filter Asymptotics SteinhausMoment HarperSharpGrid HarperSharpProfile
  HarperActualSharpConditioning HarperModerateSamples HarperRandomEulerProduct HarperEulerIntegral
  HarperEulerDiscretization HarperEulerGridComparison HarperFrequencyTail
  HarperConditioningFrequencies HarperRoundedCutoff HarperActualConditioning HarperRoughSmoothing

def gridProfile (p : ℕ) (labels : Boxes p) (v : ℤ) : ℝ :=
  (∑ k ∈ gridCenters (gridScale (primeCutoff ((p : ℝ)-1))),
    sampleProfile p labels (gridSampleIndex ((p : ℝ)-1) v k))/gridScale (primeCutoff ((p : ℝ)-1))
def profileRejectedGrid (p : ℕ) (labels : Boxes p) (v : ℤ) (ω : PhaseSpace) : ℝ :=
  (∑ k ∈ gridCenters (gridScale (primeCutoff ((p : ℝ)-1))),
    profileRejectedEnergy p labels (gridSampleIndex ((p : ℝ)-1) v k) ω)/gridScale (primeCutoff ((p : ℝ)-1))
def profileRejectionBound (p : ℕ) : ℝ :=
  2*rejectionFactor p*(profileConstant*(cutoffLog ((p : ℝ)-1))^(11/5 : ℝ))

theorem actual_gridScale_pos {x : ℝ} (hell : 0 < cutoffLog x) : 0 < gridScale (primeCutoff x) := by
  rw [gridScale,log_primeCutoff]
  exact Real.rpow_pos_of_pos hell _

theorem gridProfile_nonneg {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1)) (labels : Boxes p) (v : ℤ) :
    0 ≤ gridProfile p labels v :=
  div_nonneg (Finset.sum_nonneg (fun _ _ => sampleProfile_nonneg p labels _)) (actual_gridScale_pos hell).le

theorem profileRejectedGrid_nonneg {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (labels : Boxes p) (v : ℤ) (ω : PhaseSpace) : 0 ≤ profileRejectedGrid p labels v ω :=
  div_nonneg (Finset.sum_nonneg (fun _ _ => profileRejectedEnergy_nonneg p labels _ ω)) (actual_gridScale_pos hell).le

theorem profileRejectedGrid_integrable (p : ℕ) (labels : Boxes p) (v : ℤ) :
    Integrable (profileRejectedGrid p labels v) phaseMeasure :=
  (integrable_finsetSum _ (fun _ _ => profileRejectedEnergy_integrable p labels _)).div_const _

theorem retainedGridEnergy_le_profile {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (labels : Boxes p) (v : ℤ) (ω : PhaseSpace) :
    retainedGridEnergy p labels v ω ≤ profileConstant*gridProfile p labels v := by
  calc
    _ ≤ (∑ k ∈ gridCenters (gridScale (primeCutoff ((p : ℝ)-1))),
        profileConstant*sampleProfile p labels (gridSampleIndex ((p : ℝ)-1) v k))/gridScale (primeCutoff ((p : ℝ)-1)) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun k _ => retainedEnergy_le_sampleProfile hell labels (gridSampleIndex ((p : ℝ)-1) v k) ω))
        (actual_gridScale_pos hell).le
    _ = _ := by rw [← Finset.mul_sum]; unfold gridProfile; ring

theorem profileRejectedGrid_le_profile {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (labels : Boxes p) (v : ℤ) (ω : PhaseSpace) : profileRejectedGrid p labels v ω ≤ gridProfile p labels v :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum (fun k _ => profileRejectedEnergy_le p labels (gridSampleIndex ((p : ℝ)-1) v k) ω))
    (actual_gridScale_pos hell).le

theorem gridProfile_le_energy_add_rejected {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (labels : Boxes p) (v : ℤ) (hv : v ∈ centralFrequencies (frequencyCutoff (primeCutoff ((p : ℝ)-1))))
    (ω : PhaseSpace) : gridProfile p labels v ≤
      profileConstant*discreteEnergy (primeCutoff ((p : ℝ)-1)) v ω+profileRejectedGrid p labels v ω := by
  have h (k : ℤ) :=
    sampleProfile_le_energy_add_rejected p labels (gridSampleIndex ((p : ℝ)-1) v k) ω
  calc
    _ ≤ (∑ k ∈ gridCenters (gridScale (primeCutoff ((p : ℝ)-1))),
        (profileConstant*‖eulerProduct (primeCutoff ((p : ℝ)-1))
          (linePoint (1/2) ((v : ℝ)+(k : ℝ)/gridScale (primeCutoff ((p : ℝ)-1)))) ω‖^2+
          profileRejectedEnergy p labels (gridSampleIndex ((p : ℝ)-1) v k) ω))/gridScale (primeCutoff ((p : ℝ)-1)) := by
      apply div_le_div_of_nonneg_right _ (actual_gridScale_pos hell).le
      apply Finset.sum_le_sum
      intro k hk
      simpa only [central_gridSampleIndex_frequency hell v k hv hk] using h k
    _ = _ := by
      unfold discreteEnergy profileRejectedGrid
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      ring

theorem profileRejectionBound_nonneg {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1)) :
    0 ≤ profileRejectionBound p := by
  unfold profileRejectionBound
  exact mul_nonneg (mul_nonneg (by norm_num) (rejectionFactor_nonneg hell))
    (mul_nonneg profileConstant_pos.le (Real.rpow_nonneg hell.le _))

theorem weighted_profileRejectedGrid_bound {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (hD : 1 ≤ gridScale (primeCutoff ((p : ℝ)-1))) (v : ℤ) (ω : PhaseSpace) :
    (∑ labels : Boxes p, profileRejectedGrid p labels v ω*
      smoothBox p (firstCoefficient ((p : ℝ)-1)) (secondCoefficient ((p : ℝ)-1)) labels
        (fun n => steinhaus n ω)) ≤ profileRejectionBound p := by
  have hB : 0 ≤ rejectionFactor p*(profileConstant*(cutoffLog ((p : ℝ)-1))^(11/5 : ℝ)) :=
    mul_nonneg (rejectionFactor_nonneg hell) (mul_nonneg profileConstant_pos.le (Real.rpow_nonneg hell.le _))
  calc
    _ = (∑ k ∈ gridCenters (gridScale (primeCutoff ((p : ℝ)-1))),
        ∑ labels : Boxes p, profileRejectedEnergy p labels (gridSampleIndex ((p : ℝ)-1) v k) ω*
          smoothBox p (firstCoefficient ((p : ℝ)-1)) (secondCoefficient ((p : ℝ)-1)) labels
            (fun n => steinhaus n ω))/gridScale (primeCutoff ((p : ℝ)-1)) := by
      unfold profileRejectedGrid
      simp only [div_mul_eq_mul_div, Finset.sum_mul]
      rw [← Finset.sum_div, Finset.sum_comm]
    _ ≤ (∑ _k ∈ gridCenters (gridScale (primeCutoff ((p : ℝ)-1))),
        rejectionFactor p*(profileConstant*(cutoffLog ((p : ℝ)-1))^(11/5 : ℝ)))/gridScale (primeCutoff ((p : ℝ)-1)) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun k _ => weighted_profileRejectedEnergy_bound hell (gridSampleIndex ((p : ℝ)-1) v k) ω))
        (actual_gridScale_pos hell).le
    _ = ((gridCenters (gridScale (primeCutoff ((p : ℝ)-1)))).card : ℝ)/gridScale (primeCutoff ((p : ℝ)-1))*
        (rejectionFactor p*(profileConstant*(cutoffLog ((p : ℝ)-1))^(11/5 : ℝ))) := by simp; ring
    _ ≤ 2*(rejectionFactor p*(profileConstant*(cutoffLog ((p : ℝ)-1))^(11/5 : ℝ))) :=
      mul_le_mul_of_nonneg_right ((div_le_iff₀ (actual_gridScale_pos hell)).mpr (gridCenters_card_bound hD)) hB
    _ = _ := by unfold profileRejectionBound; ring

end NField.Alignment.HarperProfileGrid

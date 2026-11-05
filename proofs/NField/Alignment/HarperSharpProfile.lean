/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperSharpScales

/-!
# Label profiles for the actual sharp samples

A deterministic profile retains regular labels in the actual moderate range.
The sharp logarithmic comparison bounds each retained energy by this profile,
and bounds the profile back by the actual full energy plus an explicit
rejected profile. Exact box marginalization controls that correction at
every phase point, including all overflow labels in the original box sum.
No unconditional low-moment estimate is assumed.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperSharpProfile
open scoped BigOperators Topology Classical
open MeasureTheory Filter Asymptotics SteinhausMoment HarperSharpGrid HarperSharpScales
  HarperActualSharpConditioning HarperSharpPartition HarperPartition HarperModerateSamples
  HarperEulerLogComparison HarperRandomEulerProduct HarperEulerIntegral HarperEulerDiscretization
  HarperConditioningFrequencies HarperRoundedCutoff HarperActualConditioning HarperRoughSmoothing
  HarperParameterBounds HarperMainConditioning

def profileConstant : ℝ := Real.exp (2*(logRemainderConstant+1))
def profileRadius (x : ℝ) : ℝ := (11/10 : ℝ)*Real.log (cutoffLog x)+logRemainderConstant+1
def labelProfile (J : ℕ) (R : ℝ) (j : Fin (2*J+2)) : ℝ :=
  if j.val < 2*J+1 ∧ |labelCenter J j| ≤ R then Real.exp (2*labelCenter J j) else 0
def sampleProfile (p : ℕ) (labels : Boxes p) (i : Fin (factorCount ((p : ℝ)-1))) : ℝ :=
  labelProfile (rangeCount (cutoffLog ((p : ℝ)-1))) (profileRadius ((p : ℝ)-1)) (labels i)
def profileRejectedEnergy (p : ℕ) (labels : Boxes p) (i : Fin (factorCount ((p : ℝ)-1)))
    (ω : PhaseSpace) : ℝ := if sampleSharp p labels i ω then 0 else sampleProfile p labels i

theorem profileConstant_pos : 0 < profileConstant := Real.exp_pos _

theorem labelProfile_nonneg (J : ℕ) (R : ℝ) (j : Fin (2*J+2)) : 0 ≤ labelProfile J R j := by
  unfold labelProfile
  split_ifs <;> positivity

theorem labelProfile_le_exp (J : ℕ) (R : ℝ) (j : Fin (2*J+2)) :
    labelProfile J R j ≤ Real.exp (2*R) := by
  unfold labelProfile
  split_ifs with h
  · exact Real.exp_le_exp.mpr (by have := (abs_le.mp h.2).2; linarith)
  · exact (Real.exp_pos _).le

theorem weighted_rejected_labelProfile {delta : ℝ} (hd : 0 < delta) (J : ℕ) (R x : ℝ)
    (j : Fin (2*J+2)) :
    labelWeight delta J j x*(if sharpLabel J j x then 0 else labelProfile J R j) ≤
      delta*Real.exp (2*R) := by
  by_cases hs : sharpLabel J j x
  · rw [if_pos hs, mul_zero]
    positivity
  · rw [if_neg hs]
    by_cases ha : j.val < 2*J+1 ∧ |labelCenter J j| ≤ R
    · have hl : labelWeight delta J j x ≤ delta := by
        rw [labelWeight_regular delta J j ha.1]
        exact cell_localization hd (lt_of_not_ge (fun hh => hs ⟨ha.1,hh⟩))
      exact mul_le_mul hl (labelProfile_le_exp J R j) (labelProfile_nonneg J R j) hd.le
    · rw [labelProfile, if_neg ha, mul_zero]
      positivity

theorem boxWeight_rejected_profile {A : ℕ} {delta : ℝ} (hd : 0 < delta)
    (J : ℕ) (R : ℝ) (values : Fin A → ℝ) (k : Fin A) :
    (∑ labels : Fin A → Fin (2*J+2), boxWeight delta J values labels*
      (if sharpLabel J (labels k) (values k) then 0 else labelProfile J R (labels k))) ≤
      (2*(J : ℝ)+2)*delta*Real.exp (2*R) := by
  rw [boxWeight_marginal delta J values k (fun j => if sharpLabel J j (values k) then 0 else labelProfile J R j)]
  calc
    _ ≤ ∑ _j : Fin (2*J+2), delta*Real.exp (2*R) :=
      Finset.sum_le_sum (fun j _ => weighted_rejected_labelProfile hd J R (values k) j)
    _ = _ := by simp; ring

theorem sampleProfile_nonneg (p : ℕ) (labels : Boxes p) (i : Fin (factorCount ((p : ℝ)-1))) :
    0 ≤ sampleProfile p labels i := labelProfile_nonneg _ _ _

theorem exp_profileRadius {x : ℝ} (hell : 0 < cutoffLog x) :
    Real.exp (2*profileRadius x) = profileConstant*(cutoffLog x)^(11/5 : ℝ) := by
  rw [Real.rpow_def_of_pos hell, profileConstant, ← Real.exp_add]
  congr 1
  unfold profileRadius
  ring

theorem sampleProfile_bound {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (labels : Boxes p) (i : Fin (factorCount ((p : ℝ)-1))) :
    sampleProfile p labels i ≤ profileConstant*(cutoffLog ((p : ℝ)-1))^(11/5 : ℝ) := by
  exact (labelProfile_le_exp _ _ _).trans_eq (exp_profileRadius hell)

theorem sampleSharp_exp_comparison (p : ℕ) (labels : Boxes p)
    (i : Fin (factorCount ((p : ℝ)-1))) (ω : PhaseSpace) (hs : sampleSharp p labels i ω) :
    ‖eulerProduct (primeCutoff ((p : ℝ)-1)) (linePoint (1/2) (frequency ((p : ℝ)-1) i)) ω‖^2 ≤
      profileConstant*Real.exp (2*labelCenter (rangeCount (cutoffLog ((p : ℝ)-1))) (labels i)) ∧
    Real.exp (2*labelCenter (rangeCount (cutoffLog ((p : ℝ)-1))) (labels i)) ≤
      profileConstant*‖eulerProduct (primeCutoff ((p : ℝ)-1)) (linePoint (1/2) (frequency ((p : ℝ)-1) i)) ω‖^2 := by
  have hc := actual_log_eulerProduct_primeArgument_bound ((p : ℝ)-1) i ω
  change |Real.log ‖eulerProduct (primeCutoff ((p : ℝ)-1)) (linePoint (1/2) (frequency ((p : ℝ)-1) i)) ω‖-
    sampleArgument p i ω| ≤ logRemainderConstant at hc
  have hs' := abs_le.mp hs.2
  have hc' := abs_le.mp hc
  have hn := norm_pos_iff.mpr (eulerProduct_critical_ne_zero (primeCutoff ((p : ℝ)-1))
    (frequency ((p : ℝ)-1) i) ω)
  have he : Real.exp (2*Real.log ‖eulerProduct (primeCutoff ((p : ℝ)-1))
      (linePoint (1/2) (frequency ((p : ℝ)-1) i)) ω‖) =
      ‖eulerProduct (primeCutoff ((p : ℝ)-1)) (linePoint (1/2) (frequency ((p : ℝ)-1) i)) ω‖^2 := by
    rw [two_mul, Real.exp_add, Real.exp_log hn]
    ring
  constructor
  · rw [← he, profileConstant, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [hs'.1,hs'.2,hc'.1,hc'.2]
  · rw [← he, profileConstant, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [hs'.1,hs'.2,hc'.1,hc'.2]

theorem moderate_sharp_label_range {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (labels : Boxes p) (i : Fin (factorCount ((p : ℝ)-1))) (ω : PhaseSpace)
    (hs : sampleSharp p labels i ω)
    (hm : moderateSample (primeCutoff ((p : ℝ)-1)) (frequency ((p : ℝ)-1) i) ω) :
    |labelCenter (rangeCount (cutoffLog ((p : ℝ)-1))) (labels i)| ≤ profileRadius ((p : ℝ)-1) := by
  have hP : 0 < Real.log (primeCutoff ((p : ℝ)-1)) := by rwa [log_primeCutoff]
  have hb := moderate_prime_sum_bound hP (frequency ((p : ℝ)-1) i) ω hm
  rw [quadraticPrimeSum_eq_primeArgument, log_primeCutoff] at hb
  change |sampleArgument p i ω| ≤ _ at hb
  have hh := (abs_sub_le (labelCenter (rangeCount (cutoffLog ((p : ℝ)-1))) (labels i))
    (sampleArgument p i ω) 0).trans (add_le_add (by simpa only [abs_sub_comm] using hs.2) (by simpa only [sub_zero] using hb))
  simpa only [sub_zero, profileRadius, add_assoc, add_comm, add_left_comm] using hh

theorem retainedEnergy_le_sampleProfile {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (labels : Boxes p) (i : Fin (factorCount ((p : ℝ)-1))) (ω : PhaseSpace) :
    retainedEnergy p labels i ω ≤ profileConstant*sampleProfile p labels i := by
  by_cases hs : sampleSharp p labels i ω
  · rw [retainedEnergy, if_pos hs]
    by_cases hm : moderateSample (primeCutoff ((p : ℝ)-1)) (frequency ((p : ℝ)-1) i) ω
    · rw [moderateEnergy, if_pos hm, sampleProfile, labelProfile,
        if_pos ⟨hs.1,moderate_sharp_label_range hell labels i ω hs hm⟩]
      exact (sampleSharp_exp_comparison p labels i ω hs).1
    · rw [moderateEnergy, if_neg hm]
      exact mul_nonneg profileConstant_pos.le (sampleProfile_nonneg p labels i)
  · rw [retainedEnergy, if_neg hs]
    exact mul_nonneg profileConstant_pos.le (sampleProfile_nonneg p labels i)

theorem profileRejectedEnergy_nonneg (p : ℕ) (labels : Boxes p)
    (i : Fin (factorCount ((p : ℝ)-1))) (ω : PhaseSpace) : 0 ≤ profileRejectedEnergy p labels i ω := by
  unfold profileRejectedEnergy
  split_ifs
  · exact le_rfl
  · exact sampleProfile_nonneg p labels i

theorem profileRejectedEnergy_le (p : ℕ) (labels : Boxes p)
    (i : Fin (factorCount ((p : ℝ)-1))) (ω : PhaseSpace) :
    profileRejectedEnergy p labels i ω ≤ sampleProfile p labels i := by
  unfold profileRejectedEnergy
  split_ifs
  · exact sampleProfile_nonneg p labels i
  · exact le_rfl

theorem profileRejectedEnergy_integrable (p : ℕ) (labels : Boxes p)
    (i : Fin (factorCount ((p : ℝ)-1))) : Integrable (profileRejectedEnergy p labels i) phaseMeasure := by
  have h := (integrable_const (sampleProfile p labels i) (μ := phaseMeasure)).indicator
    (sampleSharp_measurableSet p labels i).compl
  convert! h using 1
  funext ω
  simp only [profileRejectedEnergy, Set.indicator_apply, Set.mem_compl_iff, Set.mem_setOf_eq]
  split_ifs <;> rfl

theorem sampleProfile_le_energy_add_rejected (p : ℕ) (labels : Boxes p)
    (i : Fin (factorCount ((p : ℝ)-1))) (ω : PhaseSpace) :
    sampleProfile p labels i ≤ profileConstant*
      ‖eulerProduct (primeCutoff ((p : ℝ)-1)) (linePoint (1/2) (frequency ((p : ℝ)-1) i)) ω‖^2+
        profileRejectedEnergy p labels i ω := by
  by_cases hs : sampleSharp p labels i ω
  · rw [profileRejectedEnergy, if_pos hs, add_zero]
    unfold sampleProfile labelProfile
    split_ifs
    · exact (sampleSharp_exp_comparison p labels i ω hs).2
    · exact mul_nonneg profileConstant_pos.le (sq_nonneg _)
  · rw [profileRejectedEnergy, if_neg hs]
    exact le_add_of_nonneg_left (mul_nonneg profileConstant_pos.le (sq_nonneg _))

theorem weighted_profileRejectedEnergy_bound {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (i : Fin (factorCount ((p : ℝ)-1))) (ω : PhaseSpace) :
    (∑ labels : Boxes p, profileRejectedEnergy p labels i ω *
      smoothBox p (firstCoefficient ((p : ℝ)-1)) (secondCoefficient ((p : ℝ)-1)) labels
        (fun n => steinhaus n ω)) ≤
      rejectionFactor p*(profileConstant*(cutoffLog ((p : ℝ)-1))^(11/5 : ℝ)) := by
  have h := boxWeight_rejected_profile (precision_pos hell) (rangeCount (cutoffLog ((p : ℝ)-1)))
    (profileRadius ((p : ℝ)-1)) (fun k => sampleArgument p k ω) i
  rw [exp_profileRadius hell] at h
  convert! h using 1
  apply Finset.sum_congr rfl
  intro labels _
  exact mul_comm _ _

end NField.Alignment.HarperSharpProfile

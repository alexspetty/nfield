/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperActualSharpConditioning
import NField.Alignment.HarperExtremeScales

/-!
# The actual grid under moderate sharp conditioning

A total sample index selects the already proved actual conditioning frequency
at every central grid point. The original normalized moderate grid splits
exactly into retained and rejected box-dependent energies. All integrability,
box-moment and finite-sum identities are proved. The complete rejected grid
has expectation O(log(L)*L^(-3/10)), uniformly in the integer center; a simpler
O(L^(7/10)) consequence suffices for the subsequent negligible-error proof.
The conditioning comparison retains the overflow label and zero-weight boxes.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperSharpGrid
open scoped BigOperators Topology Classical
open MeasureTheory Filter Asymptotics SteinhausMoment HarperActualSharpConditioning
  HarperExtremeGrid HarperModerateSamples HarperEulerDiscretization HarperEulerGridComparison
  HarperExtremeScales HarperFrequencyTail HarperConditioningFrequencies HarperRoundedCutoff
  HarperActualConditioning HarperRoughSmoothing HarperWeightedConditioning HarperSmoothingConditioning
  HarperConditioningDecay

def gridSampleIndex (x : ℝ) (v k : ℤ) : Fin (factorCount x) :=
  if h : ∃ i : Fin (factorCount x), frequency x i = (v : ℝ)+(k : ℝ)/gridScale (primeCutoff x)
  then Classical.choose h else ⟨0,by unfold factorCount; omega⟩
def retainedGridEnergy (p : ℕ) (labels : Boxes p) (v : ℤ) (ω : PhaseSpace) : ℝ :=
  (∑ k ∈ gridCenters (gridScale (primeCutoff ((p : ℝ)-1))),
    retainedEnergy p labels (gridSampleIndex ((p : ℝ)-1) v k) ω)/gridScale (primeCutoff ((p : ℝ)-1))
def rejectedGridEnergy (p : ℕ) (labels : Boxes p) (v : ℤ) (ω : PhaseSpace) : ℝ :=
  (∑ k ∈ gridCenters (gridScale (primeCutoff ((p : ℝ)-1))),
    rejectedEnergy p labels (gridSampleIndex ((p : ℝ)-1) v k) ω)/gridScale (primeCutoff ((p : ℝ)-1))
def retainedGridMoment (p : ℕ) (labels : Boxes p) (v : ℤ) : ℝ :=
  boxMoment p (firstCoefficient ((p : ℝ)-1)) (secondCoefficient ((p : ℝ)-1)) labels (retainedGridEnergy p labels v)
def rejectedGridMoment (p : ℕ) (labels : Boxes p) (v : ℤ) : ℝ :=
  boxMoment p (firstCoefficient ((p : ℝ)-1)) (secondCoefficient ((p : ℝ)-1)) labels (rejectedGridEnergy p labels v)
def totalRejectedGridMoment (p : ℕ) (v : ℤ) : ℝ := ∑ labels : Boxes p, rejectedGridMoment p labels v
def sharpGridConditioning (p : ℕ) (v : ℤ) : ℝ :=
  conditioningSum Finset.univ
    (randomWeight p (firstCoefficient ((p : ℝ)-1)) (secondCoefficient ((p : ℝ)-1)))
    (fun labels => retainedGridMoment p labels v)

theorem frequencyCutoff_primeCutoff (x : ℝ) : frequencyCutoff (primeCutoff x) = (cutoffRoot x : ℝ) := by
  rw [frequencyCutoff, log_primeCutoff, cutoffLog, ← Real.rpow_natCast_mul (Nat.cast_nonneg _) 100]
  norm_num

theorem gridSampleIndex_frequency {x : ℝ} (hx : 0 < cutoffRoot x) (v k : ℤ)
    (hv : |(v : ℝ)| ≤ (cutoffRoot x : ℝ)) (hk : k ∈ gridCenters (gridScale (primeCutoff x))) :
    frequency x (gridSampleIndex x v k) = (v : ℝ)+(k : ℝ)/gridScale (primeCutoff x) := by
  have h := actual_grid_center_is_conditioning_frequency hx v k hv hk
  rw [gridSampleIndex, dif_pos h]
  exact Classical.choose_spec h

theorem central_gridSampleIndex_frequency {x : ℝ} (hell : 0 < cutoffLog x) (v k : ℤ)
    (hv : v ∈ centralFrequencies (frequencyCutoff (primeCutoff x)))
    (hk : k ∈ gridCenters (gridScale (primeCutoff x))) :
    frequency x (gridSampleIndex x v k) = (v : ℝ)+(k : ℝ)/gridScale (primeCutoff x) := by
  have hx : 0 < cutoffRoot x := by
    by_contra hn
    have he : cutoffRoot x = 0 := Nat.eq_zero_of_not_pos hn
    simp [cutoffLog,he] at hell
  have hv' : |(v : ℝ)| ≤ (cutoffRoot x : ℝ) := by
    simpa only [centralFrequencies_mem,frequencyCutoff_primeCutoff] using hv
  exact gridSampleIndex_frequency hx v k hv' hk

theorem retainedGridEnergy_integrable (p : ℕ) (labels : Boxes p) (v : ℤ) :
    Integrable (retainedGridEnergy p labels v) phaseMeasure :=
  (integrable_finsetSum _ (fun _ _ => retainedEnergy_integrable p labels _)).div_const _

theorem rejectedGridEnergy_integrable (p : ℕ) (labels : Boxes p) (v : ℤ) :
    Integrable (rejectedGridEnergy p labels v) phaseMeasure :=
  (integrable_finsetSum _ (fun _ _ => rejectedEnergy_integrable p labels _)).div_const _

theorem retainedGridEnergy_nonneg {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (labels : Boxes p) (v : ℤ) (ω : PhaseSpace) : 0 ≤ retainedGridEnergy p labels v ω := by
  have hD : 0 ≤ gridScale (primeCutoff ((p : ℝ)-1)) := by
    rw [gridScale,log_primeCutoff]
    exact Real.rpow_nonneg hell.le _
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => retainedEnergy_nonneg p labels _ ω)) hD

theorem rejectedGridEnergy_nonneg {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (labels : Boxes p) (v : ℤ) (ω : PhaseSpace) : 0 ≤ rejectedGridEnergy p labels v ω := by
  have hD : 0 ≤ gridScale (primeCutoff ((p : ℝ)-1)) := by
    rw [gridScale,log_primeCutoff]
    exact Real.rpow_nonneg hell.le _
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => rejectedEnergy_nonneg p labels _ ω)) hD

theorem retained_rejected_grid_split {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (labels : Boxes p) (v : ℤ)
    (hv : v ∈ centralFrequencies (frequencyCutoff (primeCutoff ((p : ℝ)-1)))) (ω : PhaseSpace) :
    retainedGridEnergy p labels v ω+rejectedGridEnergy p labels v ω =
      moderateGridEnergy (primeCutoff ((p : ℝ)-1)) v ω := by
  unfold retainedGridEnergy rejectedGridEnergy moderateGridEnergy
  rw [← add_div, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [retained_rejected_split, central_gridSampleIndex_frequency hell v k hv hk]

theorem retainedGridMoment_nonneg {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1)) (labels : Boxes p) (v : ℤ) :
    0 ≤ retainedGridMoment p labels v :=
  boxMoment_nonneg hell _ _ labels (retainedGridEnergy_nonneg hell labels v)

theorem rejectedGridMoment_nonneg {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1)) (labels : Boxes p) (v : ℤ) :
    0 ≤ rejectedGridMoment p labels v :=
  boxMoment_nonneg hell _ _ labels (rejectedGridEnergy_nonneg hell labels v)

theorem totalRejectedGridMoment_nonneg {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1)) (v : ℤ) :
    0 ≤ totalRejectedGridMoment p v :=
  Finset.sum_nonneg (fun labels _ => rejectedGridMoment_nonneg hell labels v)

theorem rejectedGridMoment_eq_sum {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1)) (labels : Boxes p) (v : ℤ) :
    rejectedGridMoment p labels v =
      (∑ k ∈ gridCenters (gridScale (primeCutoff ((p : ℝ)-1))),
        boxMoment p (firstCoefficient ((p : ℝ)-1)) (secondCoefficient ((p : ℝ)-1)) labels
          (rejectedEnergy p labels (gridSampleIndex ((p : ℝ)-1) v k)))/gridScale (primeCutoff ((p : ℝ)-1)) := by
  unfold rejectedGridMoment rejectedGridEnergy boxMoment
  simp only [div_mul_eq_mul_div, Finset.sum_mul]
  rw [integral_div, integral_finsetSum _ (fun k _ => boxMoment_integrable hell _ _ labels
    (rejectedEnergy_integrable p labels _))]

theorem totalRejectedGridMoment_eq_sum {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1)) (v : ℤ) :
    totalRejectedGridMoment p v =
      (∑ k ∈ gridCenters (gridScale (primeCutoff ((p : ℝ)-1))),
        totalRejectedMoment p (gridSampleIndex ((p : ℝ)-1) v k))/gridScale (primeCutoff ((p : ℝ)-1)) := by
  unfold totalRejectedGridMoment
  simp_rw [rejectedGridMoment_eq_sum hell]
  rw [← Finset.sum_div, Finset.sum_comm]
  rfl

theorem retainedGridMoment_add_rejectedGridMoment {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (labels : Boxes p) (v : ℤ)
    (hv : v ∈ centralFrequencies (frequencyCutoff (primeCutoff ((p : ℝ)-1)))) :
    retainedGridMoment p labels v+rejectedGridMoment p labels v =
      boxMoment p (firstCoefficient ((p : ℝ)-1)) (secondCoefficient ((p : ℝ)-1)) labels
        (moderateGridEnergy (primeCutoff ((p : ℝ)-1)) v) := by
  have h := boxMoment_add hell (firstCoefficient ((p : ℝ)-1)) (secondCoefficient ((p : ℝ)-1)) labels
    (retainedGridEnergy_integrable p labels v) (rejectedGridEnergy_integrable p labels v)
  have he : (fun ω => retainedGridEnergy p labels v ω+rejectedGridEnergy p labels v ω) =
      moderateGridEnergy (primeCutoff ((p : ℝ)-1)) v := funext (retained_rejected_grid_split hell labels v hv)
  rw [he] at h
  exact h.symm

theorem moderateGrid_conditioning_le_sharp {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1)) (v : ℤ)
    (hv : v ∈ centralFrequencies (frequencyCutoff (primeCutoff ((p : ℝ)-1)))) :
    boxConditioning p (firstCoefficient ((p : ℝ)-1)) (secondCoefficient ((p : ℝ)-1))
      (moderateGridEnergy (primeCutoff ((p : ℝ)-1)) v) ≤
        sharpGridConditioning p v+(totalRejectedGridMoment p v)^(3/4 : ℝ) := by
  have hD : 0 ≤ gridScale (primeCutoff ((p : ℝ)-1)) := by
    rw [gridScale,log_primeCutoff]
    exact Real.rpow_nonneg hell.le _
  exact conditioning_add_bound
    (randomWeight p (firstCoefficient ((p : ℝ)-1)) (secondCoefficient ((p : ℝ)-1)))
    (fun i => boxMoment p (firstCoefficient ((p : ℝ)-1)) (secondCoefficient ((p : ℝ)-1)) i
      (moderateGridEnergy (primeCutoff ((p : ℝ)-1)) v))
    (fun i => retainedGridMoment p i v) (fun i => rejectedGridMoment p i v)
    (randomWeight_nonneg hell _ _)
    (fun i => boxMoment_nonneg hell _ _ i (moderateGridEnergy_nonneg hD v))
    (fun i => retainedGridMoment_nonneg hell i v) (fun i => rejectedGridMoment_nonneg hell i v)
    (randomWeight_sum hell _ _) (fun i => (retainedGridMoment_add_rejectedGridMoment hell i v hv).symm.le)

theorem totalRejectedGridMoment_bound {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    {B : ℝ} (hB : 0 ≤ B) (hD : 1 ≤ gridScale (primeCutoff ((p : ℝ)-1)))
    (hb : ∀ i : Fin (factorCount ((p : ℝ)-1)), totalRejectedMoment p i ≤ B) (v : ℤ) :
    totalRejectedGridMoment p v ≤ 2*B := by
  have hD0 : 0 < gridScale (primeCutoff ((p : ℝ)-1)) := lt_of_lt_of_le zero_lt_one hD
  rw [totalRejectedGridMoment_eq_sum hell]
  calc
    _ ≤ (∑ _k ∈ gridCenters (gridScale (primeCutoff ((p : ℝ)-1))), B)/gridScale (primeCutoff ((p : ℝ)-1)) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun k _ => hb _)) hD0.le
    _ = ((gridCenters (gridScale (primeCutoff ((p : ℝ)-1)))).card : ℝ)/gridScale (primeCutoff ((p : ℝ)-1))*B := by
      simp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right ((div_le_iff₀ hD0).mpr (gridCenters_card_bound hD)) hB

theorem eventual_totalRejectedGridMoment_log_bound : ∃ C : ℝ, 0 < C ∧ ∀ᶠ p : ℕ in atTop,
    ∀ v : ℤ, totalRejectedGridMoment p v ≤
      C*Real.log (cutoffLog ((p : ℝ)-1))*(cutoffLog ((p : ℝ)-1))^(-(3/10 : ℝ)) := by
  obtain ⟨C,hC,hb⟩ := eventual_totalRejectedMoment_log_bound
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [hb,(cutoffLog_tendsto.comp base_minus_one_tendsto).eventually_ge_atTop 1] with p hbound hL
  dsimp only [Function.comp_apply] at hL
  have hell : 0 < cutoffLog ((p : ℝ)-1) := lt_of_lt_of_le zero_lt_one hL
  have hD : 1 ≤ gridScale (primeCutoff ((p : ℝ)-1)) := by
    rw [gridScale,log_primeCutoff]
    exact Real.one_le_rpow hL (by norm_num)
  have hlog : 0 ≤ Real.log (cutoffLog ((p : ℝ)-1)) := Real.log_nonneg hL
  intro v
  have h := totalRejectedGridMoment_bound hell (show 0 ≤ C*Real.log (cutoffLog ((p : ℝ)-1))*
    (cutoffLog ((p : ℝ)-1))^(-(3/10 : ℝ)) by positivity) hD hbound v
  convert h using 1
  ring

theorem eventual_totalRejectedGridMoment_power_bound : ∃ C : ℝ, 0 < C ∧ ∀ᶠ p : ℕ in atTop,
    ∀ v : ℤ, totalRejectedGridMoment p v ≤ C*(cutoffLog ((p : ℝ)-1))^(7/10 : ℝ) := by
  obtain ⟨C,hC,hb⟩ := eventual_totalRejectedGridMoment_log_bound
  refine ⟨C,hC,?_⟩
  filter_upwards [hb,(cutoffLog_tendsto.comp base_minus_one_tendsto).eventually_gt_atTop 0] with p hbound hell
  dsimp only [Function.comp_apply] at hell
  have hlog : Real.log (cutoffLog ((p : ℝ)-1)) ≤ cutoffLog ((p : ℝ)-1) := by
    have h := Real.log_le_sub_one_of_pos hell
    linarith
  have he : cutoffLog ((p : ℝ)-1)*(cutoffLog ((p : ℝ)-1))^(-(3/10 : ℝ)) =
      (cutoffLog ((p : ℝ)-1))^(7/10 : ℝ) := by
    calc
      _ = (cutoffLog ((p : ℝ)-1))^(1 : ℝ)*(cutoffLog ((p : ℝ)-1))^(-(3/10 : ℝ)) := by
        rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hell]; norm_num
  intro v
  calc
    _ ≤ C*Real.log (cutoffLog ((p : ℝ)-1))*(cutoffLog ((p : ℝ)-1))^(-(3/10 : ℝ)) := hbound v
    _ ≤ C*cutoffLog ((p : ℝ)-1)*(cutoffLog ((p : ℝ)-1))^(-(3/10 : ℝ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog hC.le) (Real.rpow_nonneg hell.le _)
    _ = _ := by rw [mul_assoc,he]

end NField.Alignment.HarperSharpGrid

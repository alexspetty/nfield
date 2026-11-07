/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperModerateSamples
import NField.Alignment.HarperSharpPartition

/-!
# Actual sample rejection under sharp conditioning

The actual prime-sum coordinates, rounded cutoff, partition labels and
Steinhaus measure are retained. On moderate samples the complete box sum
collapses to one coordinate, including the overflow label. Its discarded
second moment is bounded uniformly in the sample index by
O(log(log(P)) * log(P)^(-3/10)).

This proves the moderate-sample rejection bound only. The downstream
`HarperEulerFractionalMoment` and `HarperExtremeScales` modules discharge
the extreme-sample contribution. `HarperSharpGrid` and `HarperSharpScales`
assemble moderate sharp-grid rejection and its negligible contribution.
`HarperUnconditioning` and `HarperUnconditioningScales` remove the remaining
conditioning and prove the complete profile correction negligible. The
Euler-product low-moment estimate is outside this module.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperActualSharpConditioning
open scoped BigOperators Topology Classical
open MeasureTheory Filter Asymptotics SteinhausMoment HarperRandomEulerProduct HarperEulerIntegral
  HarperEulerSecondMoment HarperModerateSamples HarperSharpPartition HarperPartition
  HarperConditioningFrequencies HarperRoundedCutoff HarperPrimeTaylorComparison HarperParameterBounds
  HarperSmoothDivisor HarperActualConditioning HarperRoughSmoothing HarperConditioningDecay CollisionMertensInput

def sampleArgument (p : ℕ) (k : Fin (factorCount ((p : ℝ)-1))) (ω : PhaseSpace) : ℝ :=
  primeArgument (primeCutoff ((p : ℝ)-1)) (firstCoefficient ((p : ℝ)-1) k)
    (secondCoefficient ((p : ℝ)-1) k) (fun n => steinhaus n ω)
def sampleSharp (p : ℕ) (labels : Boxes p) (k : Fin (factorCount ((p : ℝ)-1))) (ω : PhaseSpace) : Prop :=
  sharpLabel (rangeCount (cutoffLog ((p : ℝ)-1))) (labels k) (sampleArgument p k ω)
def rejectedEnergy (p : ℕ) (labels : Boxes p) (k : Fin (factorCount ((p : ℝ)-1))) (ω : PhaseSpace) : ℝ :=
  if sampleSharp p labels k ω then 0 else moderateEnergy (primeCutoff ((p : ℝ)-1)) (frequency ((p : ℝ)-1) k) ω
def retainedEnergy (p : ℕ) (labels : Boxes p) (k : Fin (factorCount ((p : ℝ)-1))) (ω : PhaseSpace) : ℝ :=
  if sampleSharp p labels k ω then moderateEnergy (primeCutoff ((p : ℝ)-1)) (frequency ((p : ℝ)-1) k) ω else 0

def rejectionFactor (p : ℕ) : ℝ :=
  (2*(rangeCount (cutoffLog ((p : ℝ)-1)) : ℝ)+2)*precision (cutoffLog ((p : ℝ)-1))
def totalRejectedMoment (p : ℕ) (k : Fin (factorCount ((p : ℝ)-1))) : ℝ :=
  ∑ labels : Boxes p, boxMoment p (firstCoefficient ((p : ℝ)-1)) (secondCoefficient ((p : ℝ)-1)) labels
    (rejectedEnergy p labels k)

theorem sampleArgument_measurable (p : ℕ) (k : Fin (factorCount ((p : ℝ)-1))) :
    Measurable (sampleArgument p k) :=
  Complex.continuous_re.measurable.comp (HarperPrimeProductMoment.random_prime_measurable _ _ _)

theorem sampleSharp_measurableSet (p : ℕ) (labels : Boxes p) (k : Fin (factorCount ((p : ℝ)-1))) :
    MeasurableSet {ω | sampleSharp p labels k ω} := by
  unfold sampleSharp sharpLabel
  by_cases hi : (labels k).val < 2*rangeCount (cutoffLog ((p : ℝ)-1))+1
  · simp only [hi, true_and]
    exact measurableSet_le ((sampleArgument_measurable p k).sub_const _).abs measurable_const
  · simp only [hi, false_and, Set.setOf_false, MeasurableSet.empty]

theorem rejectedEnergy_integrable (p : ℕ) (labels : Boxes p) (k : Fin (factorCount ((p : ℝ)-1))) :
    Integrable (rejectedEnergy p labels k) phaseMeasure := by
  have h := (moderateEnergy_integrable (primeCutoff ((p : ℝ)-1)) (frequency ((p : ℝ)-1) k)).indicator
    (sampleSharp_measurableSet p labels k).compl
  convert! h using 1
  funext ω
  simp only [rejectedEnergy, Set.indicator_apply, Set.mem_compl_iff, Set.mem_setOf_eq]
  split_ifs <;> rfl

theorem retainedEnergy_integrable (p : ℕ) (labels : Boxes p) (k : Fin (factorCount ((p : ℝ)-1))) :
    Integrable (retainedEnergy p labels k) phaseMeasure :=
  (moderateEnergy_integrable (primeCutoff ((p : ℝ)-1)) (frequency ((p : ℝ)-1) k)).indicator
    (sampleSharp_measurableSet p labels k)

theorem rejectedEnergy_nonneg (p : ℕ) (labels : Boxes p) (k : Fin (factorCount ((p : ℝ)-1)))
    (ω : PhaseSpace) : 0 ≤ rejectedEnergy p labels k ω := by
  unfold rejectedEnergy
  split_ifs
  · exact le_rfl
  · exact moderateEnergy_nonneg _ _ _

theorem retainedEnergy_nonneg (p : ℕ) (labels : Boxes p) (k : Fin (factorCount ((p : ℝ)-1)))
    (ω : PhaseSpace) : 0 ≤ retainedEnergy p labels k ω := by
  unfold retainedEnergy
  split_ifs
  · exact moderateEnergy_nonneg _ _ _
  · exact le_rfl

theorem retained_rejected_split (p : ℕ) (labels : Boxes p) (k : Fin (factorCount ((p : ℝ)-1)))
    (ω : PhaseSpace) : retainedEnergy p labels k ω+rejectedEnergy p labels k ω =
      moderateEnergy (primeCutoff ((p : ℝ)-1)) (frequency ((p : ℝ)-1) k) ω := by
  unfold retainedEnergy rejectedEnergy
  split_ifs <;> simp

theorem rejectionFactor_nonneg {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1)) :
    0 ≤ rejectionFactor p := mul_nonneg (by positivity) (precision_pos hell).le

theorem eventual_weighted_rejectedEnergy_bound : ∀ᶠ p : ℕ in atTop,
    ∀ k : Fin (factorCount ((p : ℝ)-1)), ∀ ω : PhaseSpace,
      (∑ labels : Boxes p, rejectedEnergy p labels k ω *
        smoothBox p (firstCoefficient ((p : ℝ)-1)) (secondCoefficient ((p : ℝ)-1)) labels
          (fun n => steinhaus n ω)) ≤
        rejectionFactor p*‖eulerProduct (primeCutoff ((p : ℝ)-1))
          (linePoint (1/2) (frequency ((p : ℝ)-1) k)) ω‖^2 := by
  filter_upwards [base_minus_one_tendsto.eventually eventual_actual_moderate_primeArgument_range,
    (cutoffLog_tendsto.comp base_minus_one_tendsto).eventually_gt_atTop 0] with p hr hell
  intro k ω
  by_cases hm : moderateSample (primeCutoff ((p : ℝ)-1)) (frequency ((p : ℝ)-1) k) ω
  · have hsum := boxWeight_rejected_sum_bound (precision_pos hell)
      (rangeCount (cutoffLog ((p : ℝ)-1))) (fun i => sampleArgument p i ω) k (hr k ω hm)
    have he : (∑ labels : Boxes p, rejectedEnergy p labels k ω *
        smoothBox p (firstCoefficient ((p : ℝ)-1)) (secondCoefficient ((p : ℝ)-1)) labels
          (fun n => steinhaus n ω)) =
        ‖eulerProduct (primeCutoff ((p : ℝ)-1)) (linePoint (1/2) (frequency ((p : ℝ)-1) k)) ω‖^2 *
          (∑ labels : Boxes p, if sampleSharp p labels k ω then 0 else
            boxWeight (precision (cutoffLog ((p : ℝ)-1))) (rangeCount (cutoffLog ((p : ℝ)-1)))
              (fun i => sampleArgument p i ω) labels) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro labels _
      unfold rejectedEnergy moderateEnergy
      rw [if_pos hm]
      split_ifs
      · simp only [zero_mul, mul_zero]
      · rfl
    rw [he]
    exact (mul_le_mul_of_nonneg_left hsum (sq_nonneg _)).trans_eq (mul_comm _ _)
  · have hn : 0 ≤ rejectionFactor p*‖eulerProduct (primeCutoff ((p : ℝ)-1))
        (linePoint (1/2) (frequency ((p : ℝ)-1) k)) ω‖^2 :=
      mul_nonneg (rejectionFactor_nonneg hell) (sq_nonneg _)
    simpa only [rejectedEnergy, moderateEnergy, if_neg hm, ite_self, zero_mul, Finset.sum_const_zero] using hn

theorem totalRejectedMoment_nonneg {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (k : Fin (factorCount ((p : ℝ)-1))) : 0 ≤ totalRejectedMoment p k :=
  Finset.sum_nonneg (fun labels _ => boxMoment_nonneg hell _ _ labels (rejectedEnergy_nonneg p labels k))

theorem eventual_totalRejectedMoment_bound : ∀ᶠ p : ℕ in atTop,
    ∀ k : Fin (factorCount ((p : ℝ)-1)), totalRejectedMoment p k ≤
      rejectionFactor p*inversePrimeProduct (primeCutoff ((p : ℝ)-1)) := by
  filter_upwards [eventual_weighted_rejectedEnergy_bound,
    (cutoffLog_tendsto.comp base_minus_one_tendsto).eventually_gt_atTop 0] with p hb hell
  intro k
  have hi (labels : Boxes p) := boxMoment_integrable hell
    (firstCoefficient ((p : ℝ)-1)) (secondCoefficient ((p : ℝ)-1)) labels (rejectedEnergy_integrable p labels k)
  unfold totalRejectedMoment boxMoment
  rw [← integral_finsetSum _ (fun labels _ => hi labels)]
  calc
    _ ≤ ∫ ω, rejectionFactor p*‖eulerProduct (primeCutoff ((p : ℝ)-1))
        (linePoint (1/2) (frequency ((p : ℝ)-1) k)) ω‖^2 ∂phaseMeasure :=
      integral_mono (integrable_finsetSum _ (fun labels _ => hi labels))
        ((eulerProduct_norm_sq_integrable _ (by norm_num [linePoint_re])).const_mul _) (hb k)
    _ = _ := by rw [integral_const_mul, critical_second_moment_eq_inversePrimeProduct]


theorem eventual_totalRejectedMoment_log_bound : ∃ C : ℝ, 0 < C ∧ ∀ᶠ p : ℕ in atTop,
    ∀ k : Fin (factorCount ((p : ℝ)-1)), totalRejectedMoment p k ≤
      C*Real.log (cutoffLog ((p : ℝ)-1))*(cutoffLog ((p : ℝ)-1))^(-(3/10 : ℝ)) := by
  obtain ⟨C,hC,hb⟩ := inversePrimeProduct_isBigO_log.exists_pos
  refine ⟨8*C,by positivity,?_⟩
  filter_upwards [eventual_totalRejectedMoment_bound,
    (cutoffLog_tendsto.comp base_minus_one_tendsto).eventually_gt_atTop 0,
    (Real.tendsto_log_atTop.comp (cutoffLog_tendsto.comp base_minus_one_tendsto)).eventually_ge_atTop 1,
    (primeCutoff_tendsto.comp base_minus_one_tendsto).eventually hb.bound] with p hmain hell hlog hprod
  intro k
  dsimp only [Function.comp_apply] at hell hlog hprod
  have hP : 0 < Real.log (primeCutoff ((p : ℝ)-1)) := by rwa [log_primeCutoff]
  rw [Real.norm_of_nonneg (inversePrimeProduct_pos _).le, Real.norm_of_nonneg hP.le,
    log_primeCutoff] at hprod
  have hJ : 2*(rangeCount (cutoffLog ((p : ℝ)-1)) : ℝ)+2 ≤
      8*Real.log (cutoffLog ((p : ℝ)-1)) := by
    have h := (rangeCount_bounds hell hlog).2.2.1
    linarith
  have hfac : rejectionFactor p ≤
      (8*Real.log (cutoffLog ((p : ℝ)-1)))*(cutoffLog ((p : ℝ)-1))^(-(13/10 : ℝ)) := by
    exact mul_le_mul_of_nonneg_right hJ (Real.rpow_nonneg hell.le _)
  have he : (cutoffLog ((p : ℝ)-1))^(-(13/10 : ℝ))*cutoffLog ((p : ℝ)-1) =
      (cutoffLog ((p : ℝ)-1))^(-(3/10 : ℝ)) := by
    calc
      _ = (cutoffLog ((p : ℝ)-1))^(-(13/10 : ℝ))*(cutoffLog ((p : ℝ)-1))^(1 : ℝ) := by
        rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hell]; norm_num
  calc
    _ ≤ rejectionFactor p*inversePrimeProduct (primeCutoff ((p : ℝ)-1)) := hmain k
    _ ≤ ((8*Real.log (cutoffLog ((p : ℝ)-1)))*(cutoffLog ((p : ℝ)-1))^(-(13/10 : ℝ)))*
        (C*cutoffLog ((p : ℝ)-1)) :=
      mul_le_mul hfac hprod (inversePrimeProduct_pos _).le (by positivity)
    _ = (8*C)*Real.log (cutoffLog ((p : ℝ)-1))*
        ((cutoffLog ((p : ℝ)-1))^(-(13/10 : ℝ))*cutoffLog ((p : ℝ)-1)) := by ring
    _ = _ := by rw [he]

end NField.Alignment.HarperActualSharpConditioning

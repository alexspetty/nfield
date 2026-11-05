/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperEulerSecondMoment
import NField.Alignment.HarperMainConditioning
import Mathlib.Analysis.PSeries

/-!
# Unit frequency intervals and their actual energies

The full spectral integral is the sum over disjoint unit intervals.
On each interval the exact Cauchy weight is bounded by a summable square
weight in its integer center. The three-quarter power gives the summable
exponent 3/2. Every interval has phase integrability and its unweighted
energy has the exact reciprocal-prime-product expectation. Weighted
Holder gives the unconditional bound needed for the distant intervals.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperFrequencyIntervals

open scoped BigOperators Topology
open MeasureTheory Set Filter SteinhausMoment HarperEulerIntegral HarperEulerSecondMoment
  HarperSmoothCount HarperRandomEulerProduct HarperMainConditioning HarperSmoothingConditioning
  HarperRoughSmoothing HarperActualConditioning HarperWeightedConditioning HarperConditioningFrequencies
  HarperRoundedCutoff

def frequencyWeight (r : ℝ) (v : ℤ) : ℝ := 1/(|(v : ℝ)|+1)^r

def unitEnergy (P : ℝ) (v : ℤ) : PhaseSpace → ℝ :=
  intervalEnergy P (1/2) ((v : ℝ)-1/2) ((v : ℝ)+1/2)

def unitSpectral (P : ℝ) (v : ℤ) (ω : PhaseSpace) : ℝ :=
  ∫ t in Ioc ((v : ℝ)-1/2) ((v : ℝ)+1/2), spectralDensity P (1/2) (t,ω)

theorem frequencyWeight_nonneg (r : ℝ) (v : ℤ) : 0 ≤ frequencyWeight r v := by
  unfold frequencyWeight
  positivity

theorem frequencyWeight_summable {r : ℝ} (hr : 1 < r) : Summable (frequencyWeight r) := by
  have h := (Real.summable_one_div_nat_add_rpow 1 r).mpr hr
  have he (n : ℕ) : frequencyWeight r (n : ℤ) = 1/|(n : ℝ)+1|^r := by
    simp [frequencyWeight, abs_of_nonneg (show (0 : ℝ) ≤ n from Nat.cast_nonneg n),
      abs_of_pos (by positivity : 0 < (n : ℝ)+1)]
  have hn : Summable (fun n : ℕ => frequencyWeight r (n : ℤ)) := by
    simpa only [he] using h
  rw [summable_int_iff_summable_nat_and_neg]
  exact ⟨hn, by simpa only [frequencyWeight, Int.cast_neg, abs_neg] using hn⟩

theorem frequencyWeight_rpow (v : ℤ) :
    (frequencyWeight 2 v)^(3/4 : ℝ) = frequencyWeight (3/2) v := by
  unfold frequencyWeight
  rw [Real.div_rpow (by norm_num) (Real.rpow_nonneg (by positivity) _), Real.one_rpow,
    ← Real.rpow_mul (by positivity)]
  norm_num

theorem cauchyWeight_unit_bound (v : ℤ) {t : ℝ}
    (ht : t ∈ Ioc ((v : ℝ)-1/2) ((v : ℝ)+1/2)) :
    cauchyWeight (1/2) t ≤ 16*frequencyWeight 2 v := by
  have hdist : |(v : ℝ)-t| ≤ 1/2 := abs_le.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hv : |(v : ℝ)| ≤ |t|+1/2 := by
    calc
      _ = |t+((v : ℝ)-t)| := by congr 1; ring
      _ ≤ |t|+|(v : ℝ)-t| := abs_add_le _ _
      _ ≤ _ := add_le_add le_rfl hdist
  have hsq : (|(v : ℝ)|+1)^2 ≤ 16*((1/2 : ℝ)^2+t^2) := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ |(v : ℝ)|+1)
      (by linarith : |(v : ℝ)|+1 ≤ |t|+3/2) 2
    nlinarith [sq_abs t, sq_nonneg (|t|-1/2)]
  unfold cauchyWeight frequencyWeight
  rw [Real.rpow_two, ← div_eq_mul_one_div]
  rw [← one_div]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  simpa only [one_mul] using hsq

theorem unitEnergy_nonneg (P : ℝ) (v : ℤ) (ω : PhaseSpace) : 0 ≤ unitEnergy P v ω :=
  intervalEnergy_nonneg _ _ _ _ _

theorem unitEnergy_integrable (P : ℝ) (v : ℤ) : Integrable (unitEnergy P v) phaseMeasure :=
  intervalEnergy_integrable P _ _ (by norm_num : (0 : ℝ) < 1/2)

theorem unitEnergy_mean (P : ℝ) (v : ℤ) :
    (∫ ω, unitEnergy P v ω ∂phaseMeasure) = CollisionMertensInput.inversePrimeProduct P :=
  unitEnergy_expectation P v

theorem unitSpectral_nonneg (P : ℝ) (v : ℤ) (ω : PhaseSpace) : 0 ≤ unitSpectral P v ω :=
  integral_nonneg (fun t => spectralDensity_nonneg _ _ (t,ω))

theorem unitSpectral_integrable (P : ℝ) (v : ℤ) : Integrable (unitSpectral P v) phaseMeasure := by
  have h : Integrable (spectralDensity P (1/2))
      ((volume.restrict (Ioc ((v : ℝ)-1/2) ((v : ℝ)+1/2))).prod phaseMeasure) :=
    (spectralDensity_integrable P (by norm_num : (0 : ℝ) < 1/2)).mono_measure
      (Measure.prod_mono Measure.restrict_le_self le_rfl)
  exact h.integral_prod_right

theorem unitSpectral_hasSum (P : ℝ) (ω : PhaseSpace) :
    HasSum (fun v : ℤ => unitSpectral P v ω) (spectralIntegral P (1/2) ω) := by
  have h := (spectralDensity_integrable_line P (by norm_num : (0 : ℝ) < 1/2) ω).hasSum_intervalIntegral (-1/2)
  have ha (v : ℤ) : (-1/2 : ℝ)+v = (v : ℝ)-1/2 := by ring
  have hb (v : ℤ) : (-1/2 : ℝ)+v+1 = (v : ℝ)+1/2 := by ring
  have hle (v : ℤ) : (v : ℝ)-1/2 ≤ (v : ℝ)+1/2 := by linarith
  simp_rw [hb, ha, intervalIntegral.integral_of_le (hle _)] at h
  exact h

theorem unitEnergy_line_integrable (P : ℝ) (v : ℤ) (ω : PhaseSpace) :
    IntegrableOn (fun t => verticalEnergy P (1/2) (t,ω))
      (Ioc ((v : ℝ)-1/2) ((v : ℝ)+1/2)) := by
  apply Integrable.of_bound
    ((((verticalProduct_measurable P (1/2)).norm.pow_const 2).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
    ((shiftedProduct P (1/2))^2)
  apply Filter.Eventually.of_forall
  intro t
  dsimp only [Function.comp_apply, id_eq]
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have h := eulerProduct_norm_le P (s := linePoint (1/2) t) (by norm_num [linePoint_re]) ω
  rw [linePoint_re] at h
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

theorem unitEnergy_bound (P : ℝ) (v : ℤ) (ω : PhaseSpace) :
    unitEnergy P v ω ≤ (shiftedProduct P (1/2))^2 := by
  calc
    _ ≤ ∫ t in Ioc ((v : ℝ)-1/2) ((v : ℝ)+1/2), (shiftedProduct P (1/2))^2 := by
      apply integral_mono (unitEnergy_line_integrable P v ω) (integrable_const _)
      intro t
      have h := eulerProduct_norm_le P (s := linePoint (1/2) t) (by norm_num [linePoint_re]) ω
      rw [linePoint_re] at h
      exact pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := by norm_num

theorem unitSpectral_le_unitEnergy (P : ℝ) (v : ℤ) (ω : PhaseSpace) :
    unitSpectral P v ω ≤ (16*frequencyWeight 2 v)*unitEnergy P v ω := by
  have he : (16*frequencyWeight 2 v)*unitEnergy P v ω =
      ∫ t in Ioc ((v : ℝ)-1/2) ((v : ℝ)+1/2),
        (16*frequencyWeight 2 v)*verticalEnergy P (1/2) (t,ω) :=
    (integral_const_mul _ _).symm
  rw [he]
  apply setIntegral_mono_on
    (spectralDensity_integrable_line P (by norm_num : (0 : ℝ) < 1/2) ω).integrableOn
    ((unitEnergy_line_integrable P v ω).const_mul _) measurableSet_Ioc
  intro t ht
  exact (mul_le_mul_of_nonneg_left (cauchyWeight_unit_bound v ht) (sq_nonneg _)).trans_eq (mul_comm _ _)

theorem unitSpectral_bound (P : ℝ) (v : ℤ) (ω : PhaseSpace) :
    unitSpectral P v ω ≤ (16*(shiftedProduct P (1/2))^2)*frequencyWeight 2 v := by
  calc
    _ ≤ (16*frequencyWeight 2 v)*unitEnergy P v ω := unitSpectral_le_unitEnergy P v ω
    _ ≤ (16*frequencyWeight 2 v)*(shiftedProduct P (1/2))^2 :=
      mul_le_mul_of_nonneg_left (unitEnergy_bound P v ω)
        (mul_nonneg (by norm_num) (frequencyWeight_nonneg _ _))
    _ = _ := by ring

theorem boxConditioning_le_expectation {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (c1 c2 : Coefficients p) {F : PhaseSpace → ℝ} (hF : Integrable F phaseMeasure)
    (hF0 : ∀ ω, 0 ≤ F ω) :
    boxConditioning p c1 c2 F ≤ (∫ ω, F ω ∂phaseMeasure)^(3/4 : ℝ) := by
  have h := weighted_holder Finset.univ (randomWeight p c1 c2)
    (fun i => boxMoment p c1 c2 i F) (fun i _ => randomWeight_nonneg hell c1 c2 i)
    (fun i _ => boxMoment_nonneg hell c1 c2 i hF0)
  rwa [randomWeight_sum hell c1 c2, Real.one_rpow, one_mul, boxMoment_sum hell c1 c2 hF] at h

theorem unitEnergy_conditioning_bound {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (c1 c2 : Coefficients p) (P : ℝ) (v : ℤ) :
    boxConditioning p c1 c2 (unitEnergy P v) ≤
      (CollisionMertensInput.inversePrimeProduct P)^(3/4 : ℝ) := by
  simpa only [unitEnergy_mean] using boxConditioning_le_expectation hell c1 c2
    (unitEnergy_integrable P v) (unitEnergy_nonneg P v)

end NField.Alignment.HarperFrequencyIntervals

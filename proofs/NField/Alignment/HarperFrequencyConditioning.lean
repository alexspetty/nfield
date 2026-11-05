/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperFrequencyIntervals

/-!
# Frequency localization under the actual box conditioning

Dominated convergence passes the countable unit-interval decomposition
through each actual box moment. The exact second moment and a summable
3/2 weight prove summability after the three-quarter power. Fractional
subadditivity and the finite box sum then localize the full spectral
conditioning without discarding zero-weight boxes.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperFrequencyConditioning

open scoped BigOperators Topology
open MeasureTheory Set Filter SteinhausMoment HarperEulerIntegral HarperEulerSecondMoment
  HarperSmoothCount HarperRandomEulerProduct HarperMainConditioning HarperSmoothingConditioning
  HarperRoughSmoothing HarperActualConditioning HarperWeightedConditioning HarperConditioningFrequencies
  HarperRoundedCutoff HarperFrequencyIntervals HarperProductApproximation HarperParameterBounds
  CollisionMertensInput

theorem fractional_sum_le {ι : Type*} (s : Finset ι) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (∑ i ∈ s, a i)^(3/4 : ℝ) ≤ ∑ i ∈ s, (a i)^(3/4 : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (Real.rpow_add_le_add_rpow (ha i) (Finset.sum_nonneg (fun j _ => ha j))
      (by norm_num) (by norm_num)).trans (add_le_add le_rfl ih)

theorem fractional_tsum_le {ι : Type*} (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hA : Summable a) (hB : Summable (fun i => (a i)^(3/4 : ℝ))) :
    (∑' i, a i)^(3/4 : ℝ) ≤ ∑' i, (a i)^(3/4 : ℝ) := by
  have hAt : Tendsto (fun s : Finset ι => ∑ i ∈ s, a i) atTop (𝓝 (∑' i, a i)) := hA.hasSum
  exact le_of_tendsto_of_tendsto (hAt.rpow_const (Or.inr (by norm_num))) hB.hasSum
    (Filter.Eventually.of_forall (fun s => fractional_sum_le s a ha))

private theorem boxWeight_le_one {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (c1 c2 : Coefficients p) (i : Boxes p) (ω : PhaseSpace) :
    smoothBox p c1 c2 i (fun n => steinhaus n ω) ≤ 1 :=
  smoothValue_le_one (precision_pos hell) _ _ _ _ _ _ _

theorem boxMoment_le_expectation {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (c1 c2 : Coefficients p) (i : Boxes p) {F : PhaseSpace → ℝ}
    (hF : Integrable F phaseMeasure) (hF0 : ∀ ω, 0 ≤ F ω) :
    boxMoment p c1 c2 i F ≤ ∫ ω, F ω ∂phaseMeasure :=
  integral_mono (boxMoment_integrable hell c1 c2 i hF) hF
    (fun ω => mul_le_of_le_one_right (hF0 ω) (boxWeight_le_one hell c1 c2 i ω))

theorem boxMoment_unitSpectral_le {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (c1 c2 : Coefficients p) (i : Boxes p) (P : ℝ) (v : ℤ) :
    boxMoment p c1 c2 i (unitSpectral P v) ≤
      (16*frequencyWeight 2 v)*boxMoment p c1 c2 i (unitEnergy P v) := by
  have h := boxMoment_mono hell c1 c2 i (unitSpectral_integrable P v)
    ((unitEnergy_integrable P v).const_mul (16*frequencyWeight 2 v))
    (unitSpectral_le_unitEnergy P v)
  rwa [boxMoment_const_mul] at h

theorem boxMoment_unitSpectral_bound {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (c1 c2 : Coefficients p) (i : Boxes p) (P : ℝ) (v : ℤ) :
    boxMoment p c1 c2 i (unitSpectral P v) ≤
      (16*inversePrimeProduct P)*frequencyWeight 2 v := by
  have h := boxMoment_le_expectation hell c1 c2 i (unitEnergy_integrable P v)
    (unitEnergy_nonneg P v)
  rw [unitEnergy_mean] at h
  calc
    _ ≤ (16*frequencyWeight 2 v)*boxMoment p c1 c2 i (unitEnergy P v) :=
      boxMoment_unitSpectral_le hell c1 c2 i P v
    _ ≤ (16*frequencyWeight 2 v)*inversePrimeProduct P :=
      mul_le_mul_of_nonneg_left h (mul_nonneg (by norm_num) (frequencyWeight_nonneg _ _))
    _ = _ := by ring

theorem boxMoment_unitSpectral_hasSum {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (c1 c2 : Coefficients p) (i : Boxes p) (P : ℝ) :
    HasSum (fun v : ℤ => boxMoment p c1 c2 i (unitSpectral P v))
      (boxMoment p c1 c2 i (spectralIntegral P (1/2))) := by
  apply hasSum_integral_of_dominated_convergence
    (fun v _ω => (16*(shiftedProduct P (1/2))^2)*frequencyWeight 2 v)
    (fun v => (boxMoment_integrable hell c1 c2 i (unitSpectral_integrable P v)).aestronglyMeasurable)
  · intro v
    apply Filter.Eventually.of_forall
    intro ω
    rw [Real.norm_of_nonneg (mul_nonneg (unitSpectral_nonneg P v ω) (smoothBox_nonneg hell c1 c2 i _))]
    exact (mul_le_of_le_one_right (unitSpectral_nonneg P v ω)
      (boxWeight_le_one hell c1 c2 i ω)).trans (unitSpectral_bound P v ω)
  · exact Filter.Eventually.of_forall (fun _ =>
      (frequencyWeight_summable (by norm_num : (1 : ℝ) < 2)).mul_left _)
  · exact integrable_const _
  · exact Filter.Eventually.of_forall (fun ω => (unitSpectral_hasSum P ω).mul_right _)

theorem boxMoment_unitSpectral_fractional_bound {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (c1 c2 : Coefficients p) (i : Boxes p) (P : ℝ) (v : ℤ) :
    (boxMoment p c1 c2 i (unitSpectral P v))^(3/4 : ℝ) ≤
      (16*inversePrimeProduct P)^(3/4 : ℝ)*frequencyWeight (3/2) v := by
  rw [← frequencyWeight_rpow,
    ← Real.mul_rpow (mul_nonneg (by norm_num) (inversePrimeProduct_pos P).le)
      (frequencyWeight_nonneg _ _)]
  exact Real.rpow_le_rpow (boxMoment_nonneg hell c1 c2 i (unitSpectral_nonneg P v))
    (boxMoment_unitSpectral_bound hell c1 c2 i P v) (by norm_num)

theorem boxMoment_unitSpectral_fractional_summable {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (c1 c2 : Coefficients p) (i : Boxes p) (P : ℝ) :
    Summable (fun v : ℤ => (boxMoment p c1 c2 i (unitSpectral P v))^(3/4 : ℝ)) :=
  ((frequencyWeight_summable (by norm_num : (1 : ℝ) < 3/2)).mul_left
    ((16*inversePrimeProduct P)^(3/4 : ℝ))).of_nonneg_of_le
      (fun v => Real.rpow_nonneg (boxMoment_nonneg hell c1 c2 i (unitSpectral_nonneg P v)) _)
      (boxMoment_unitSpectral_fractional_bound hell c1 c2 i P)

theorem boxConditioning_nonneg {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (c1 c2 : Coefficients p) {F : PhaseSpace → ℝ} (hF0 : ∀ ω, 0 ≤ F ω) :
    0 ≤ boxConditioning p c1 c2 F :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (Real.rpow_nonneg (randomWeight_nonneg hell c1 c2 i) _)
    (Real.rpow_nonneg (boxMoment_nonneg hell c1 c2 i hF0) _))

theorem unitSpectral_conditioning_summable {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (c1 c2 : Coefficients p) (P : ℝ) :
    Summable (fun v : ℤ => boxConditioning p c1 c2 (unitSpectral P v)) :=
  summable_sum (fun i _ =>
    (boxMoment_unitSpectral_fractional_summable hell c1 c2 i P).mul_left _)

theorem spectral_conditioning_le_sum {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (c1 c2 : Coefficients p) (P : ℝ) :
    boxConditioning p c1 c2 (spectralIntegral P (1/2)) ≤
      ∑' v : ℤ, boxConditioning p c1 c2 (unitSpectral P v) := by
  have hi (i : Boxes p) :
      (randomWeight p c1 c2 i)^(1/4 : ℝ)*
        (boxMoment p c1 c2 i (spectralIntegral P (1/2)))^(3/4 : ℝ) ≤
      ∑' v : ℤ, (randomWeight p c1 c2 i)^(1/4 : ℝ)*
        (boxMoment p c1 c2 i (unitSpectral P v))^(3/4 : ℝ) := by
    rw [tsum_mul_left]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (randomWeight_nonneg hell c1 c2 i) _)
    have hs := boxMoment_unitSpectral_hasSum hell c1 c2 i P
    rw [← hs.tsum_eq]
    exact fractional_tsum_le _ (fun v => boxMoment_nonneg hell c1 c2 i (unitSpectral_nonneg P v))
      hs.summable (boxMoment_unitSpectral_fractional_summable hell c1 c2 i P)
  unfold boxConditioning conditioningSum
  rw [Summable.tsum_finsetSum (fun i _ =>
    (boxMoment_unitSpectral_fractional_summable hell c1 c2 i P).mul_left _)]
  exact Finset.sum_le_sum (fun i _ => hi i)

theorem unitSpectral_conditioning_le_energy {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (c1 c2 : Coefficients p) (P : ℝ) (v : ℤ) :
    boxConditioning p c1 c2 (unitSpectral P v) ≤
      (16 : ℝ)^(3/4 : ℝ)*frequencyWeight (3/2) v * boxConditioning p c1 c2 (unitEnergy P v) := by
  have h := boxConditioning_mono hell c1 c2 (unitSpectral_integrable P v)
    ((unitEnergy_integrable P v).const_mul (16*frequencyWeight 2 v))
    (unitSpectral_nonneg P v) (unitSpectral_le_unitEnergy P v)
  rwa [boxConditioning_const_mul hell c1 c2
    (mul_nonneg (by norm_num) (frequencyWeight_nonneg _ _)) _ (unitEnergy_nonneg P v),
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 16) (frequencyWeight_nonneg _ _),
    frequencyWeight_rpow] at h

theorem unitEnergy_weighted_conditioning_summable {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (c1 c2 : Coefficients p) (P : ℝ) :
    Summable (fun v : ℤ => frequencyWeight (3/2) v * boxConditioning p c1 c2 (unitEnergy P v)) :=
  ((frequencyWeight_summable (by norm_num : (1 : ℝ) < 3/2)).mul_right
    ((inversePrimeProduct P)^(3/4 : ℝ))).of_nonneg_of_le
      (fun v => mul_nonneg (frequencyWeight_nonneg _ _) (boxConditioning_nonneg hell c1 c2 (unitEnergy_nonneg P v)))
      (fun v => mul_le_mul_of_nonneg_left (unitEnergy_conditioning_bound hell c1 c2 P v)
        (frequencyWeight_nonneg _ _))

theorem spectral_conditioning_localized {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (c1 c2 : Coefficients p) (P : ℝ) :
    boxConditioning p c1 c2 (spectralIntegral P (1/2)) ≤
      (16 : ℝ)^(3/4 : ℝ)*
        ∑' v : ℤ, frequencyWeight (3/2) v * boxConditioning p c1 c2 (unitEnergy P v) := by
  calc
    _ ≤ ∑' v : ℤ, boxConditioning p c1 c2 (unitSpectral P v) :=
      spectral_conditioning_le_sum hell c1 c2 P
    _ ≤ ∑' v : ℤ, (16 : ℝ)^(3/4 : ℝ)*
        (frequencyWeight (3/2) v * boxConditioning p c1 c2 (unitEnergy P v)) := by
      apply Summable.tsum_le_tsum _ (unitSpectral_conditioning_summable hell c1 c2 P)
        ((unitEnergy_weighted_conditioning_summable hell c1 c2 P).mul_left _)
      intro v
      simpa only [mul_assoc] using unitSpectral_conditioning_le_energy hell c1 c2 P v
    _ = _ := tsum_mul_left

end NField.Alignment.HarperFrequencyConditioning

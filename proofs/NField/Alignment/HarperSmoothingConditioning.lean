/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperRoughSmoothing


/-!
# Smoothing the actual three-quarter conditioning expression

Fractional subadditivity and weighted Holder retain zero-weight boxes.
The proved interval and random-moment bounds then reduce the actual random
conditioning to its smoothed main term and the explicit rough counting sum.
The scale is exactly exp(sqrt(log x)); its positivity and all cutoff conditions
are discharged at the actual parameters. The sieve estimate and later random
Euler-product estimate remain separate proof obligations.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperSmoothingConditioning

open scoped BigOperators
open MeasureTheory Filter SteinhausMoment HarperRoughDecomposition HarperRoughSmoothing
  HarperActualConditioning HarperWeightedConditioning HarperConditioningFrequencies
  HarperParameterBounds HarperRoundedCutoff HarperRetainedTransfer

theorem conditioning_split_bound {ι : Type*} [Fintype ι] (w a b c : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hc : ∀ i, 0 ≤ c i)
    (hsum : ∑ i, w i = 1) (hbound : ∀ i, a i ≤ 2*b i+2*c i) :
    conditioningSum Finset.univ w a ≤ (2 : ℝ)^(3/4 : ℝ) *
      (conditioningSum Finset.univ w b + (∑ i, c i)^(3/4 : ℝ)) := by
  have hpoint (i : ι) : (w i)^(1/4 : ℝ)*(a i)^(3/4 : ℝ) ≤
      (2 : ℝ)^(3/4 : ℝ)*((w i)^(1/4 : ℝ)*(b i)^(3/4 : ℝ) +
        (w i)^(1/4 : ℝ)*(c i)^(3/4 : ℝ)) := by
    have hpow := (Real.rpow_le_rpow (ha i) (hbound i) (by norm_num : (0 : ℝ) ≤ 3/4)).trans
      (Real.rpow_add_le_add_rpow (mul_nonneg (by norm_num) (hb i))
        (mul_nonneg (by norm_num) (hc i)) (by norm_num) (by norm_num))
    calc
      _ ≤ (w i)^(1/4 : ℝ)*((2*b i)^(3/4 : ℝ)+(2*c i)^(3/4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg (hw i) _)
      _ = _ := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (hb i),
          Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (hc i)]
        ring
  have hholder := weighted_holder Finset.univ w c (fun i _ => hw i) (fun i _ => hc i)
  rw [hsum, Real.one_rpow, one_mul] at hholder
  calc
    _ ≤ (2 : ℝ)^(3/4 : ℝ) *
        (conditioningSum Finset.univ w b + conditioningSum Finset.univ w c) := by
      unfold conditioningSum
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      exact Finset.sum_le_sum (fun i _ => hpoint i)
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add le_rfl hholder)
      (Real.rpow_nonneg (by norm_num) _)

def boxConditioning (p : ℕ) (c1 c2 : Coefficients p) (F : PhaseSpace → ℝ) : ℝ :=
  conditioningSum Finset.univ (randomWeight p c1 c2) (fun i => boxMoment p c1 c2 i F)

theorem boxConditioning_smoothing {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (c1 c2 : Coefficients p) {x X : ℝ} (hx : 0 ≤ x) (hX : 0 < X)
    (P y : ℝ) (w : ℕ → ℂ) (hw : ∀ n, ‖w n‖ ≤ 1) :
    boxConditioning p c1 c2 (roughSquare x P y w) ≤
      (2 : ℝ)^(3/4 : ℝ) * (boxConditioning p c1 c2 (smoothRoughAverage x P y X w) +
        (roughSmoothingError x P y X)^(3/4 : ℝ)) := by
  have h := conditioning_split_bound (randomWeight p c1 c2)
    (fun i => boxMoment p c1 c2 i (roughSquare x P y w))
    (fun i => boxMoment p c1 c2 i (smoothRoughAverage x P y X w))
    (fun i => boxMoment p c1 c2 i (roughTailAverage x P y X w))
    (randomWeight_nonneg hell c1 c2)
    (fun i => boxMoment_nonneg hell c1 c2 i (roughSquare_nonneg x P y w))
    (fun i => boxMoment_nonneg hell c1 c2 i (smoothRoughAverage_nonneg hX x P y w))
    (fun i => boxMoment_nonneg hell c1 c2 i (roughTailAverage_nonneg hX x P y w))
    (randomWeight_sum hell c1 c2) (fun i => weighted_rough_smoothing hell c1 c2 i hx hX P y w)
  rw [boxMoment_sum hell c1 c2 (roughTailAverage_integrable hX x P y w)] at h
  have he := Real.rpow_le_rpow (integral_nonneg (roughTailAverage_nonneg hX x P y w))
    (roughTailAverage_expectation_bound hx hX P y w hw) (by norm_num : (0 : ℝ) ≤ 3/4)
  exact h.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl he)
    (Real.rpow_nonneg (by norm_num) _))

theorem roughConditioning_eq_boxConditioning {p : ℕ}
    (hell : 0 < cutoffLog ((p : ℝ)-1)) (c1 c2 : Coefficients p) (w : ℕ → ℂ) :
    roughConditioning p c1 c2 w = boxConditioning p c1 c2
      (roughSquare ((p : ℝ)-1) (primeCutoff ((p : ℝ)-1)) (smoothCutoff ((p : ℝ)-1)) w) := by
  unfold roughConditioning boxConditioning conditioningSum
  apply Finset.sum_congr rfl
  intro i _
  exact conditional_term_identity (randomWeight_nonneg hell c1 c2 i)
    (boxMoment_nonneg hell c1 c2 i (roughSquare_nonneg _ _ _ w))

def smoothingScale (x : ℝ) : ℝ := Real.exp (Real.sqrt (Real.log x))

theorem actual_random_smoothing {p : ℕ} (hp : 1 ≤ p)
    (hell : 0 < cutoffLog ((p : ℝ)-1))
    (hPy : primeCutoff ((p : ℝ)-1) ≤ smoothCutoff ((p : ℝ)-1)) :
    actualRandomConditioning p ≤ (2 : ℝ)^(3/4 : ℝ) *
      (boxConditioning p (firstCoefficient ((p : ℝ)-1)) (secondCoefficient ((p : ℝ)-1))
        (smoothRoughAverage ((p : ℝ)-1) (primeCutoff ((p : ℝ)-1))
          (smoothCutoff ((p : ℝ)-1)) (smoothingScale ((p : ℝ)-1)) (fun _ => 1)) +
       (roughSmoothingError ((p : ℝ)-1) (primeCutoff ((p : ℝ)-1))
          (smoothCutoff ((p : ℝ)-1)) (smoothingScale ((p : ℝ)-1)))^(3/4 : ℝ)) := by
  rw [actual_random_decomposition hp hell hPy, roughConditioning_eq_boxConditioning hell]
  have hx : 0 ≤ (p : ℝ)-1 := sub_nonneg.mpr (by exact_mod_cast hp)
  exact boxConditioning_smoothing hell _ _ hx (Real.exp_pos _) _ _ _ (fun _ => by simp)

theorem eventual_actual_random_smoothing : ∀ᶠ p : ℕ in atTop,
    actualRandomConditioning p ≤ (2 : ℝ)^(3/4 : ℝ) *
      (boxConditioning p (firstCoefficient ((p : ℝ)-1)) (secondCoefficient ((p : ℝ)-1))
        (smoothRoughAverage ((p : ℝ)-1) (primeCutoff ((p : ℝ)-1))
          (smoothCutoff ((p : ℝ)-1)) (smoothingScale ((p : ℝ)-1)) (fun _ => 1)) +
       (roughSmoothingError ((p : ℝ)-1) (primeCutoff ((p : ℝ)-1))
          (smoothCutoff ((p : ℝ)-1)) (smoothingScale ((p : ℝ)-1)))^(3/4 : ℝ)) := by
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    (cutoffLog_tendsto.comp base_minus_one_tendsto).eventually_gt_atTop 0,
    base_minus_one_tendsto.eventually eventual_cutoff_hierarchy] with p hp hell hPy
  exact actual_random_smoothing hp hell hPy.1.le

end NField.Alignment.HarperSmoothingConditioning

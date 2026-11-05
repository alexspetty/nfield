/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperRecursionWeights

/-!
# A fixed contraction for the weighted moment recursion

The amplitude A/(1-q), with A fixed from the failure constant, makes the
exceptional-event coefficient at most one half uniformly as q tends to
one. The good-event contribution has a fixed bound as well.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperRecursionContraction
open HarperMomentRecursion HarperRecursionWeights

def contractionAmplitude (D : ℝ) : ℝ := 1+Real.log (4*max 1 D)

theorem contractionAmplitude_ge_one (D : ℝ) : 1 ≤ contractionAmplitude D := by
  have h : (1 : ℝ) ≤ 4*max 1 D := by linarith [le_max_left (1 : ℝ) D]
  have hl := Real.log_nonneg h
  unfold contractionAmplitude
  linarith

theorem contraction_coefficient (D : ℝ) :
    2*max 1 D*Real.exp (-contractionAmplitude D) ≤ 1/2 := by
  have hp : 0 < 4*max 1 D := by linarith [le_max_left (1 : ℝ) D]
  have he : 4*max 1 D ≤ Real.exp (contractionAmplitude D) := by
    rw [← Real.exp_log hp]
    apply Real.exp_le_exp.mpr
    unfold contractionAmplitude
    linarith
  rw [Real.exp_neg,← div_eq_mul_inv,div_le_iff₀ (Real.exp_pos _)]
  linarith

theorem recursive_exponential_bound {A q : ℝ} (hA : 0 ≤ A) (hq0 : 0 < q) (hq1 : q < 1) :
    (-2*(A/(1-q)))*(1-q/nextExponent q) ≤ -A := by
  have hqne : 1-q ≠ 0 := by linarith
  have hpne : 1+q ≠ 0 := by linarith
  have he : (-2*(A/(1-q)))*(1-q/nextExponent q) = -2*A/(1+q) := by
    unfold nextExponent
    field_simp
    ring
  rw [he,div_le_iff₀ (by linarith : 0 < 1+q)]
  nlinarith

theorem recursive_failure_power {D A q : ℝ} (hD : 0 ≤ D) (hA : 0 ≤ A)
    (hq0 : 0 < q) (hq1 : q < 1) :
    (D*Real.exp (-2*(A/(1-q))))^(1-q/nextExponent q) ≤ max 1 D*Real.exp (-A) := by
  have ht := interpolationExponent_bounds hq0 hq1
  rw [Real.mul_rpow hD (Real.exp_pos _).le,← Real.exp_mul]
  exact mul_le_mul (rpow_le_max_one hD (by linarith) (by linarith))
    (Real.exp_le_exp.mpr (recursive_exponential_bound hA hq0 hq1))
    (Real.exp_pos _).le (le_trans (by norm_num) (le_max_left _ _))

theorem weighted_next_moment_le {s q S : ℝ} {m : ℝ → ℝ}
    (hs : 0 ≤ s) (hq0 : 0 < q) (hq1 : q < 1)
    (hm : 0 ≤ m (nextExponent q)) (hS : weightedMoment s m (nextExponent q) ≤ S) :
    (momentWeight s q)^q*(m (nextExponent q))^(q/nextExponent q) ≤ 2*max 1 S := by
  have ht := interpolationExponent_bounds hq0 hq1
  have hr := nextExponent_bounds hq0.le hq1
  have hw := momentWeight_ge_one hs hr.2.2.le
  have hn : 0 ≤ weightedMoment s m (nextExponent q) :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _) hm
  calc
    _ ≤ (2*((momentWeight s (nextExponent q))^(nextExponent q))^(q/nextExponent q))*
        (m (nextExponent q))^(q/nextExponent q) :=
      mul_le_mul_of_nonneg_right (next_weight_power hs hq0 hq1) (Real.rpow_nonneg hm _)
    _ = 2*(weightedMoment s m (nextExponent q))^(q/nextExponent q) := by
      rw [mul_assoc,← Real.mul_rpow (Real.rpow_nonneg (by linarith) _) hm]
      rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((rpow_le_max_one hn ht.1.le ht.2.le).trans (max_le_max le_rfl hS)) (by norm_num)

theorem weighted_bad_term {s q D S : ℝ} {m : ℝ → ℝ}
    (hs : 0 ≤ s) (hD : 0 ≤ D) (hq0 : 0 < q) (hq1 : q < 1)
    (hm : 0 ≤ m (nextExponent q)) (hS : weightedMoment s m (nextExponent q) ≤ S) :
    (momentWeight s q)^q*((m (nextExponent q))^(q/nextExponent q)*
      (D*Real.exp (-2*(contractionAmplitude D/(1-q))))^(1-q/nextExponent q)) ≤
        (1/2)*max 1 S := by
  have hA : 0 ≤ contractionAmplitude D := (by norm_num : (0 : ℝ) ≤ 1).trans (contractionAmplitude_ge_one D)
  have hw := momentWeight_ge_one hs hq1.le
  calc
    _ = ((momentWeight s q)^q*(m (nextExponent q))^(q/nextExponent q))*
        (D*Real.exp (-2*(contractionAmplitude D/(1-q))))^(1-q/nextExponent q) := by ring
    _ ≤ (2*max 1 S)*(max 1 D*Real.exp (-contractionAmplitude D)) :=
      mul_le_mul (weighted_next_moment_le hs hq0 hq1 hm hS)
        (recursive_failure_power hD hA hq0 hq1)
        (Real.rpow_nonneg (mul_nonneg hD (Real.exp_pos _).le) _)
        (by linarith [le_max_left (1 : ℝ) S])
    _ = (2*max 1 D*Real.exp (-contractionAmplitude D))*max 1 S := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (contraction_coefficient D)
      (le_trans (by norm_num) (le_max_left _ _))

theorem weighted_recursion_bound {s C D q S : ℝ} {m : ℝ → ℝ}
    (hs : 0 < s) (hC : 0 ≤ C) (hD : 0 ≤ D) (hq0 : 0 < q) (hq1 : q < 1)
    (hreg : 1 ≤ (1-q)*s) (hm : 0 ≤ m (nextExponent q))
    (hS : weightedMoment s m (nextExponent q) ≤ S)
    (hrec : m q ≤ (C*min 1 ((contractionAmplitude D/(1-q))/s))^q+
      (m (nextExponent q))^(q/nextExponent q)*
        (D*Real.exp (-2*(contractionAmplitude D/(1-q))))^(1-q/nextExponent q)) :
    weightedMoment s m q ≤ max 1 (2*C*contractionAmplitude D)+(1/2)*max 1 S := by
  have hw := momentWeight_ge_one hs.le hq1.le
  have h := mul_le_mul_of_nonneg_left hrec (Real.rpow_nonneg (by linarith : 0 ≤ momentWeight s q) q)
  rw [mul_add] at h
  exact h.trans (add_le_add
    (weighted_good_term hs hC (contractionAmplitude_ge_one D) hq0 hq1 hreg)
    (weighted_bad_term hs.le hD hq0 hq1 hm hS))

end NField.Alignment.HarperRecursionContraction

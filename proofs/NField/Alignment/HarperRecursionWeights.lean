/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperMomentRecursion

/-!
# Weights for closing the critical moment recursion

The weight is 1+(1-q)*s. Its change at the next exponent costs at most
two. In the nontrivial range (1-q)*s>=1, amplitude A/(1-q) makes the
weighted good-event term uniformly bounded.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperRecursionWeights
open HarperMomentRecursion

def momentWeight (s q : ℝ) : ℝ := 1+(1-q)*s
def weightedMoment (s : ℝ) (m : ℝ → ℝ) (q : ℝ) : ℝ := (momentWeight s q)^q*m q

theorem rpow_le_max_one {z q : ℝ} (hz : 0 ≤ z) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    z^q ≤ max 1 z := by
  by_cases h : z ≤ 1
  · have hh : z^q ≤ 1 := by simpa only [Real.one_rpow] using Real.rpow_le_rpow hz h hq0
    exact hh.trans (le_max_left _ _)
  · exact (Real.rpow_le_self_of_one_le (le_of_not_ge h) hq1).trans (le_max_right _ _)

theorem momentWeight_ge_one {s q : ℝ} (hs : 0 ≤ s) (hq : q ≤ 1) : 1 ≤ momentWeight s q := by
  unfold momentWeight
  nlinarith

theorem momentWeight_le {s q : ℝ} (hs : 0 ≤ s) (hq : 0 ≤ q) : momentWeight s q ≤ 1+s := by
  unfold momentWeight
  nlinarith

theorem momentWeight_next (s q : ℝ) : momentWeight s q ≤ 2*momentWeight s (nextExponent q) := by
  unfold momentWeight nextExponent
  linarith

theorem next_weight_power {s q : ℝ} (hs : 0 ≤ s) (hq0 : 0 < q) (hq1 : q < 1) :
    (momentWeight s q)^q ≤
      2*((momentWeight s (nextExponent q))^(nextExponent q))^(q/nextExponent q) := by
  have hr := nextExponent_bounds hq0.le hq1
  have hw := momentWeight_ge_one hs hq1.le
  have hwr := momentWeight_ge_one hs hr.2.2.le
  have hrne := ne_of_gt hr.1
  have he : nextExponent q*(q/nextExponent q) = q := by field_simp
  rw [← Real.rpow_mul (by linarith : 0 ≤ momentWeight s (nextExponent q)),he]
  calc
    _ ≤ (2*momentWeight s (nextExponent q))^q :=
      Real.rpow_le_rpow (by linarith) (momentWeight_next s q) hq0.le
    _ = (2 : ℝ)^q*(momentWeight s (nextExponent q))^q :=
      Real.mul_rpow (by norm_num) (by linarith)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_self_of_one_le (by norm_num : (1 : ℝ) ≤ 2) hq1.le)
      (Real.rpow_nonneg (by linarith) _)

theorem recursion_amplitude_ge_one {A q : ℝ} (hA : 1 ≤ A) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    1 ≤ A/(1-q) := by
  rw [le_div_iff₀ (by linarith : 0 < 1-q)]
  linarith

theorem weighted_good_term {s C A q : ℝ} (hs : 0 < s) (hC : 0 ≤ C) (hA : 1 ≤ A)
    (hq0 : 0 < q) (hq1 : q < 1) (hreg : 1 ≤ (1-q)*s) :
    (momentWeight s q)^q*(C*min 1 ((A/(1-q))/s))^q ≤ max 1 (2*C*A) := by
  have hw := momentWeight_ge_one hs.le hq1.le
  have hmin : 0 ≤ min 1 ((A/(1-q))/s) := by
    apply le_min (by norm_num)
    apply div_nonneg _ hs.le
    exact div_nonneg (by linarith) (by linarith)
  have hfrac : momentWeight s q*(A/(1-q))/s ≤ 2*A := by
    rw [div_le_iff₀ hs,← mul_div_assoc,div_le_iff₀ (by linarith : 0 < 1-q)]
    unfold momentWeight
    nlinarith [mul_le_mul_of_nonneg_left hreg (show 0 ≤ A by linarith)]
  have hb : momentWeight s q*(C*min 1 ((A/(1-q))/s)) ≤ 2*C*A := by
    calc
      _ ≤ momentWeight s q*(C*((A/(1-q))/s)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (min_le_right _ _) hC) (by linarith)
      _ = C*(momentWeight s q*(A/(1-q))/s) := by ring
      _ ≤ C*(2*A) := mul_le_mul_of_nonneg_left hfrac hC
      _ = _ := by ring
  rw [← Real.mul_rpow (by linarith : 0 ≤ momentWeight s q) (mul_nonneg hC hmin)]
  exact (Real.rpow_le_rpow (mul_nonneg (by linarith) (mul_nonneg hC hmin)) hb hq0.le).trans
    (rpow_le_max_one (by positivity) hq0.le hq1.le)

end NField.Alignment.HarperRecursionWeights

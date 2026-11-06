/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetTailGrowth
import Mathlib.Analysis.PSeries

/-! # Square-root frequency sums and the convergent harmonic lifts -/

noncomputable section

namespace NField.Alignment.CommonResetRootSums

open scoped BigOperators
open CommonResetTailGrowth

theorem reciprocal_root_step (n : ℕ) :
    1/Real.sqrt ((n : ℝ)+1) ≤ 2*(Real.sqrt ((n : ℝ)+1)-Real.sqrt (n : ℝ)) := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ n+1 by positivity)
  have ht := Real.sq_sqrt (Nat.cast_nonneg n)
  apply (div_le_iff₀ (Real.sqrt_pos.mpr (by positivity))).mpr
  nlinarith [sq_nonneg (Real.sqrt ((n : ℝ)+1)-Real.sqrt (n : ℝ))]

/-- Title: `The entire reciprocal-square-root frequency sum is bounded by twice the square root of its cutoff`. -/
theorem sum_reciprocal_sqrt (Y : ℕ) :
    (∑ n ∈ Finset.Icc 1 Y, 1/Real.sqrt (n : ℝ)) ≤ 2*Real.sqrt (Y : ℝ) := by
  induction Y with
  | zero => simp
  | succ Y ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ Y+1)]
    simp only [Nat.cast_add, Nat.cast_one]
    linarith [reciprocal_root_step Y]

def harmonicLift (n : ℕ) : ℝ := (harmonic n : ℝ)/((n : ℝ)*Real.sqrt (n : ℝ))

theorem harmonicLift_nonneg (n : ℕ) : 0 ≤ harmonicLift n := by
  unfold harmonicLift
  exact div_nonneg (CommonResetSmallConductors.harmonic_nonneg n) (by positivity)

/-- Title: `The actual harmonic lift divided by the three-halves power is summable`. -/
theorem harmonicLift_summable : Summable harmonicLift := by
  have hb (n : ℕ) : harmonicLift n ≤ 5*(n : ℝ)^(-5/4 : ℝ) := by
    by_cases hn : n=0
    · subst n
      simp only [harmonicLift, Nat.cast_zero, zero_mul, div_zero]
      positivity
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hh := harmonic_small_power (1/4) (by norm_num) (show 1 ≤ n by omega)
    norm_num only at hh
    have he : (n : ℝ)*Real.sqrt (n : ℝ) = (n : ℝ)^(3/2 : ℝ) := by
      calc
        _ = (n : ℝ)^(1 : ℝ)*(n : ℝ)^(1/2 : ℝ) := by rw [Real.rpow_one, Real.sqrt_eq_rpow]
        _ = _ := by rw [← Real.rpow_add hnpos]; norm_num
    calc
      harmonicLift n ≤ (5*(n : ℝ)^(1/4 : ℝ))/((n : ℝ)*Real.sqrt (n : ℝ)) :=
        div_le_div_of_nonneg_right hh (by positivity)
      _ = _ := by rw [he, mul_div_assoc, ← Real.rpow_sub hnpos]; norm_num
  have hs : Summable (fun n : ℕ => (n : ℝ)^(-5/4 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  exact (hs.mul_left 5).of_nonneg_of_le harmonicLift_nonneg hb

def rootCube (n : ℕ) : ℝ := 1/((n : ℝ)*Real.sqrt (n : ℝ))

theorem rootCube_nonneg (n : ℕ) : 0 ≤ rootCube n := by unfold rootCube; positivity

theorem rootCube_summable : Summable rootCube := by
  have he (n : ℕ) : rootCube n = (n : ℝ)^(-3/2 : ℝ) := by
    by_cases hn : n=0
    · subst n
      norm_num [rootCube]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    unfold rootCube
    have hden : (n : ℝ)*Real.sqrt (n : ℝ) = (n : ℝ)^(3/2 : ℝ) := by
      calc
        _ = (n : ℝ)^(1 : ℝ)*(n : ℝ)^(1/2 : ℝ) := by rw [Real.rpow_one, Real.sqrt_eq_rpow]
        _ = _ := by rw [← Real.rpow_add hnpos]; norm_num
    rw [hden, one_div, ← Real.rpow_neg hnpos.le]
    norm_num
  exact (Real.summable_nat_rpow.mpr (by norm_num : (-3/2 : ℝ) < -1)).congr (fun n => (he n).symm)

theorem harmonicLift_sum_le (s : Finset ℕ) :
    (∑ n ∈ s, harmonicLift n) ≤ ∑' n : ℕ, harmonicLift n :=
  harmonicLift_summable.sum_le_tsum s (fun n _ => harmonicLift_nonneg n)

theorem rootCube_sum_le (s : Finset ℕ) :
    (∑ n ∈ s, rootCube n) ≤ ∑' n : ℕ, rootCube n :=
  rootCube_summable.sum_le_tsum s (fun n _ => rootCube_nonneg n)

end NField.Alignment.CommonResetRootSums

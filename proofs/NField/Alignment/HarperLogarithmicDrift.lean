/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperGaussianMovingPotential
import Mathlib.Analysis.PSeries

/-!
# Summable deficit cost of a logarithmic barrier

The constant-barrier estimate bounds the preceding survival probability.
The logarithmic boundary increment then has a summable n^(-5/4)
majorant, giving a deficit budget uniform in the path length.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperLogarithmicDrift
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set HarperMovingKilledPath HarperGaussianMovingPotential

def logBoundary (a : ℝ) (n : ℕ) : ℝ := a+10*Real.log (max (n : ℝ) 1)

def logDeficitConstant : ℝ := 2+369000*∑' j : ℕ, (j : ℝ)^(-(5/4 : ℝ))

theorem logBoundary_zero (a : ℝ) : logBoundary a 0 = a := by simp [logBoundary]

theorem logBoundary_one (a : ℝ) : logBoundary a 1 = a := by simp [logBoundary]

theorem logBoundary_mono (a : ℝ) : Monotone (logBoundary a) := by
  intro m n hmn
  unfold logBoundary
  have hmax : max (m : ℝ) 1 ≤ max (n : ℝ) 1 := max_le_max (by exact_mod_cast hmn) le_rfl
  have hpos : 0 < max (m : ℝ) 1 := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hlog := Real.log_le_log hpos hmax
  linarith

theorem logBoundary_positive_time (a : ℝ) {n : ℕ} (hn : 0 < n) :
    logBoundary a n = a+10*Real.log (n : ℝ) := by
  unfold logBoundary
  rw [max_eq_left (by exact_mod_cast hn : (1 : ℝ) ≤ n)]

theorem logBoundary_increment {n : ℕ} (hn : 0 < n) (a : ℝ) :
    logBoundary a (n+1)-logBoundary a n ≤ 10/(n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [logBoundary_positive_time a (by omega : 0 < n+1),logBoundary_positive_time a hn]
  simp only [Nat.cast_add,Nat.cast_one]
  have h := Real.log_le_sub_one_of_pos (show 0 < ((n : ℝ)+1)/(n : ℝ) by positivity)
  rw [Real.log_div (by positivity : (n : ℝ)+1 ≠ 0) hn0.ne'] at h
  have he : ((n : ℝ)+1)/(n : ℝ)-1 = 1/(n : ℝ) := by field_simp; ring
  rw [he] at h
  calc
    _ = 10*(Real.log ((n : ℝ)+1)-Real.log (n : ℝ)) := by ring
    _ ≤ 10*(1/(n : ℝ)) := mul_le_mul_of_nonneg_left h (by norm_num)
    _ = _ := by ring

theorem logBoundary_power_envelope {a : ℝ} (ha : 0 ≤ a) {n : ℕ} (hn : 0 < n) :
    logBoundary a n+1 ≤ (a+41)*(n : ℝ)^(1/4 : ℝ) := by
  rw [logBoundary_positive_time a hn]
  have hp : 1 ≤ (n : ℝ)^(1/4 : ℝ) := Real.one_le_rpow
    (by exact_mod_cast hn) (by norm_num)
  have hl := Real.log_natCast_le_rpow_div n (by norm_num : (0 : ℝ) < 1/4)
  have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ a+1 by linarith)
  norm_num at hl
  nlinarith

theorem logarithmic_drift_majorant {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    (logBoundary a (n+1)-logBoundary a n)*survivalEnvelope (logBoundary a) n ≤
      9000*(a+41)*(n : ℝ)^(-(5/4 : ℝ)) := by
  by_cases hn : n = 0
  · subst n
    simp [logBoundary_zero,logBoundary_one]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hB : 0 ≤ logBoundary a n := by
    have h := logBoundary_mono a (Nat.zero_le n)
    rw [logBoundary_zero] at h
    exact ha.trans h
  simp only [survivalEnvelope,hn,ite_false]
  have henv : 900*(logBoundary a n+1)/Real.sqrt (n : ℝ) ≤
      900*((a+41)*(n : ℝ)^(1/4 : ℝ))/Real.sqrt (n : ℝ) :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (logBoundary_power_envelope ha hnpos) (by norm_num))
      (Real.sqrt_nonneg _)
  have hp : (n : ℝ)*Real.sqrt (n : ℝ) = (n : ℝ)^(3/2 : ℝ) := by
    rw [show (3/2 : ℝ) = 1+1/2 by norm_num,Real.rpow_add hn0,Real.rpow_one,Real.sqrt_eq_rpow]
  calc
    _ ≤ (10/(n : ℝ))*(900*((a+41)*(n : ℝ)^(1/4 : ℝ))/Real.sqrt (n : ℝ)) :=
      mul_le_mul (logBoundary_increment hnpos a) henv (by positivity) (by positivity)
    _ = 9000*(a+41)*((n : ℝ)^(1/4 : ℝ)/((n : ℝ)*Real.sqrt (n : ℝ))) := by ring
    _ = _ := by rw [hp,← Real.rpow_sub hn0]; norm_num

theorem logarithmic_majorant_summable : Summable (fun j : ℕ => (j : ℝ)^(-(5/4 : ℝ))) := by
  exact Real.summable_nat_rpow.mpr (by norm_num)

theorem logDeficitConstant_pos : 0 < logDeficitConstant := by
  have hs : 0 ≤ ∑' j : ℕ, (j : ℝ)^(-(5/4 : ℝ)) :=
    tsum_nonneg (fun j => Real.rpow_nonneg (Nat.cast_nonneg j) _)
  unfold logDeficitConstant
  linarith

theorem logarithmic_driftBudget_bound {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    driftBudget (logBoundary a) n ≤ logDeficitConstant*(a+1) := by
  unfold driftBudget
  rw [logBoundary_zero]
  have hsum : (∑ j ∈ Finset.range n,
      (logBoundary a (j+1)-logBoundary a j)*survivalEnvelope (logBoundary a) j) ≤
      9000*(a+41)*∑' j : ℕ, (j : ℝ)^(-(5/4 : ℝ)) := by
    calc
      _ ≤ ∑ j ∈ Finset.range n, 9000*(a+41)*(j : ℝ)^(-(5/4 : ℝ)) :=
        Finset.sum_le_sum (fun j _ => logarithmic_drift_majorant ha j)
      _ = 9000*(a+41)*∑ j ∈ Finset.range n, (j : ℝ)^(-(5/4 : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (logarithmic_majorant_summable.sum_le_tsum (Finset.range n)
          (fun j _ => Real.rpow_nonneg (Nat.cast_nonneg j) _)) (by positivity)
  have hs : 0 ≤ ∑' j : ℕ, (j : ℝ)^(-(5/4 : ℝ)) :=
    tsum_nonneg (fun j => Real.rpow_nonneg (Nat.cast_nonneg j) _)
  unfold logDeficitConstant
  nlinarith

theorem gaussian_logarithmic_deficit_bound {n : ℕ} {a : ℝ} (ha : 0 ≤ a)
    (v : Fin n → NNReal) (hv : ∀ i, (1/4 : ℝ) ≤ v i ∧ (v i : ℝ) ≤ 1) :
    (∫ z, movingPotential (logBoundary a) z ∂Measure.pi (fun i => gaussianReal 0 (v i))) ≤
      logDeficitConstant*(a+1) := by
  exact (gaussian_movingPotential_budget (logBoundary a) (by simpa only [logBoundary_zero] using ha)
    (logBoundary_mono a) v hv).trans (logarithmic_driftBudget_bound ha n)

theorem gaussian_logarithmic_deficit_tail {n : ℕ} {a R : ℝ} (ha : 0 ≤ a) (hR : 0 ≤ R)
    (v : Fin n → NNReal) (hv : ∀ i, (1/4 : ℝ) ≤ v i ∧ (v i : ℝ) ≤ 1) :
    (Measure.pi (fun i => gaussianReal 0 (v i))).real
      (movingEvent (logBoundary a) ∩ {z | R ≤ logBoundary a n-∑ i, z i}) ≤
        logDeficitConstant*(a+1)/(R+2) := by
  exact (gaussian_moving_deficit_tail (logBoundary a) (by simpa only [logBoundary_zero] using ha)
    (logBoundary_mono a) v hv hR).trans
      (div_le_div_of_nonneg_right (logarithmic_driftBudget_bound ha n) (by linarith))

end NField.Alignment.HarperLogarithmicDrift

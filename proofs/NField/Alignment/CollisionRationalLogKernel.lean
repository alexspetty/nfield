/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.CollisionRationalLogKernel
open scoped BigOperators

def logPrefix (r : ℝ) (N : ℕ) : ℝ :=
  2*∑ i ∈ Finset.range N, r^(2*i+1)/(2*(i : ℝ)+1)
def logError (r : ℝ) (N : ℕ) : ℝ :=
  2*r^(2*N+1)/(1-r^2)

theorem log_ratio_enclosure {r : ℝ} (hr0 : 0≤r) (hr1 : r<1) (N : ℕ) :
    logPrefix r N ≤ Real.log ((1+r)/(1-r)) ∧
    Real.log ((1+r)/(1-r)) ≤ logPrefix r N+logError r N := by
  have hl := Real.sum_range_le_log_div hr0 hr1 N
  have hu := Real.log_div_le_sum_range_add hr0 hr1 N
  dsimp [logPrefix,logError]
  rw [mul_div_assoc]
  constructor <;> linarith

theorem logPrefix_nonneg {r : ℝ} (hr : 0≤r) (N : ℕ) : 0≤logPrefix r N := by
  unfold logPrefix
  positivity

def rangeRatio (x a : ℝ) : ℝ := (x-a)/(x+a)

theorem rangeRatio_bounds {x a : ℝ} (ha : 0<a) (hlo : a≤x) (hhi : x≤2*a) :
    0≤rangeRatio x a ∧ rangeRatio x a≤1/3 := by
  have hx : 0<x := ha.trans_le hlo
  unfold rangeRatio
  constructor
  · exact div_nonneg (sub_nonneg.mpr hlo) (by positivity)
  · apply (div_le_iff₀ (by positivity : 0<x+a)).mpr
    linarith

theorem rangeRatio_identity {x a : ℝ} (hx : 0<x) (ha : 0<a) :
    (1+rangeRatio x a)/(1-rangeRatio x a)=x/a := by
  unfold rangeRatio
  have hxa : x+a≠0 := (by positivity : 0<x+a).ne'
  field_simp [ha.ne',hxa]
  ring

theorem scaled_log_enclosure {x a l u : ℝ} (ha : 0<a)
    (hlo : a≤x) (hhi : x≤2*a) (hal : l≤Real.log a) (hau : Real.log a≤u) (N : ℕ) :
    l+logPrefix (rangeRatio x a) N ≤ Real.log x ∧
    Real.log x ≤ u+logPrefix (rangeRatio x a) N+logError (rangeRatio x a) N := by
  have hx : 0<x := ha.trans_le hlo
  have hr := rangeRatio_bounds ha hlo hhi
  have h := log_ratio_enclosure hr.1 (by linarith : rangeRatio x a<1) N
  rw [rangeRatio_identity hx ha,Real.log_div hx.ne' ha.ne'] at h
  constructor <;> linarith [h.1,h.2]

theorem binary_log_enclosure {x : ℝ} (b N : ℕ)
    (hlo : (2 : ℝ)^b≤x) (hhi : x≤2*(2 : ℝ)^b) :
    (b : ℝ)*logPrefix (1/3) N+logPrefix (rangeRatio x (2^b)) N ≤ Real.log x ∧
    Real.log x ≤ (b : ℝ)*(logPrefix (1/3) N+logError (1/3) N)+
      logPrefix (rangeRatio x (2^b)) N+logError (rangeRatio x (2^b)) N := by
  have htwo := log_ratio_enclosure (by norm_num : (0 : ℝ)≤1/3)
    (by norm_num : (1/3 : ℝ)<1) N
  norm_num only [show ((1 : ℝ)+1/3)/(1-1/3)=2 by norm_num] at htwo
  have hl : (b : ℝ)*logPrefix (1/3) N ≤ Real.log ((2 : ℝ)^b) := by
    rw [Real.log_pow]
    exact mul_le_mul_of_nonneg_left htwo.1 (Nat.cast_nonneg b)
  have hu : Real.log ((2 : ℝ)^b) ≤ (b : ℝ)*(logPrefix (1/3) N+logError (1/3) N) := by
    rw [Real.log_pow]
    exact mul_le_mul_of_nonneg_left htwo.2 (Nat.cast_nonneg b)
  exact scaled_log_enclosure (by positivity) hlo hhi hl hu N

end NField.Alignment.CollisionRationalLogKernel

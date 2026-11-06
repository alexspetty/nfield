/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetHuxley
import NField.Alignment.CommonResetWeightedDistribution

/-! # The common reset and a zero-total-weight interior example -/

noncomputable section

namespace NField.Alignment.CommonResetNarrativeExamples

open scoped BigOperators Topology
open CommonResetGram CommonResetWeightedSources CommonResetWeightedSampling
open CommonResetWeightedDistribution DedekindReciprocity RademacherThreeTerm
open Filter

/-- Title: `The resetting mass at the common origin is the total clock weight`. -/
theorem origin_reset_weight (N : ℕ) (c : ℕ → ℝ) :
    resetWeight N c 1=∑ j ∈ Finset.Icc 1 N, c j := by
  simp [resetWeight]

/-- Title: `The common reset contributes exactly the rank-one quadratic form`. -/
theorem common_reset_rank_one (N q : ℕ) (c : ℕ → ℝ) :
    ((Nat.totient 1 : ℝ)*resetWeight N c 1^2)/(q : ℝ)=
      (∑ j ∈ Finset.Icc 1 N, c j)^2/(q : ℝ) := by
  simp [origin_reset_weight]

/-- Title: `A mixture with total weight zero removes the common-reset term`. -/
theorem zero_total_removes_common_reset (N q : ℕ) (c : ℕ → ℝ)
    (hc : ∑ j ∈ Finset.Icc 1 N, c j=0) :
    ((Nat.totient 1 : ℝ)*resetWeight N c 1^2)/(q : ℝ)=0 := by
  rw [common_reset_rank_one, hc]
  simp

/-- Title: `Replacing the origin by the mean of its one-sided squares changes the actual grid average by the common-reset form`. -/
theorem origin_replacement_increment {q : ℕ} (hq : 0 < q) (N : ℕ) (c : ℕ → ℝ) :
    (1/(q : ℝ))*(∑ a ∈ Finset.range q,
      if a=0 then (∑ j ∈ Finset.Icc 1 N, c j)^2 else weightedProfile N c ((a : ℝ)/q)^2)-
      weightedSample N q c=(∑ j ∈ Finset.Icc 1 N, c j)^2/(q : ℝ) := by
  have hp (a : ℕ) :
      (if a=0 then (∑ j ∈ Finset.Icc 1 N, c j)^2 else weightedProfile N c ((a : ℝ)/q)^2)=
        weightedProfile N c ((a : ℝ)/q)^2+
          (if a=0 then (∑ j ∈ Finset.Icc 1 N, c j)^2 else 0) := by
    by_cases ha : a=0
    · subst a
      simp [weightedProfile_zero]
    · simp [ha]
  rw [weightedSample]
  simp only [hp, Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq', Finset.mem_range.mpr hq]
  ring

def cancellingWeights (j : ℕ) : ℝ := if j=1 then 1 else if j=3 then -1 else 0

/-- Title: `An exact zero-total-weight example has nonzero interior interaction`. -/
theorem zero_total_nonzero_interior :
    (∑ j ∈ Finset.Icc 1 3, cancellingWeights j)=0 ∧
      weightedInterior 3 4 cancellingWeights=-(1/9 : ℝ) := by
  have hset : Finset.Icc 1 3=({1, 2, 3} : Finset ℕ) := by decide
  constructor
  · norm_num [hset, cancellingWeights]
  · rw [weightedInterior_coefficient_sum]
    norm_num [hset, cancellingWeights, arithmeticCoefficientDedekindTerm,
      rationalSawtooth, Finset.sum_range_succ]

/-- Title: `The actual common-reset correction tends to one as the base grows`. -/
theorem common_reset_tendsto_one :
    Tendsto (fun p : ℕ => ((p-1 : ℕ) : ℝ)^2/(p : ℝ)^2) atTop (𝓝 1) := by
  have hi : Tendsto (fun p : ℕ => (p : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have he := (hc.sub hi).pow 2
  norm_num only [sub_zero, one_pow] at he
  apply he.congr'
  filter_upwards [eventually_ge_atTop 1] with p hp
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  rw [Nat.cast_sub hp, Nat.cast_one]
  field_simp [hp0] <;> ring

end NField.Alignment.CommonResetNarrativeExamples

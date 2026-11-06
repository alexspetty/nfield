/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetWeightedSampling
import NField.Alignment.BernoulliCurvature

/-! # Literal Bernoulli multiplication at arbitrary, including noncoprime, grid frequencies -/

noncomputable section

namespace NField.Alignment.CommonResetBernoulliCurvature

open scoped BigOperators
open BernoulliCurvature CommonResetBernoulliLifts CommonResetWeightedSampling
open CarrierJumpData

theorem bernoulli_scaled {g d : ℕ} (hg : 0 < g) (a : ℕ) :
    rationalBernoulliTwo (g*a) (g*d) = rationalBernoulliTwo a d := by
  have hgQ : (g : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
  unfold rationalBernoulliTwo
  push_cast
  field_simp

theorem bernoulli_grid_gcd_reduction {q j : ℕ} (hj : 0 < j) :
    (∑ a ∈ Finset.range j, rationalBernoulliTwo ((q*a)%j) j) =
      (q.gcd j : ℚ)*completeBernoulliTwoSum (j/(q.gcd j)) := by
  let g := q.gcd j
  let c := q/g
  let d := j/g
  have hg : 0 < g := Nat.gcd_pos_of_pos_right q hj
  have hgq : g ∣ q := Nat.gcd_dvd_left q j
  have hgj : g ∣ j := Nat.gcd_dvd_right q j
  have hq : q=g*c := (Nat.mul_div_cancel' hgq).symm
  have hjd : j=g*d := (Nat.mul_div_cancel' hgj).symm
  have hd : 0 < d := Nat.div_pos (Nat.le_of_dvd hj hgj) hg
  have hc : c.Coprime d := Nat.coprime_div_gcd_div_gcd hg
  have hpoint (a : ℕ) : rationalBernoulliTwo ((q*a)%j) j =
      rationalBernoulliTwo ((c*a)%d) d := by
    rw [hq, hjd, mul_assoc, Nat.mul_mod_mul_left, bernoulli_scaled hg]
  simp only [hpoint]
  let f (a : ℕ) := rationalBernoulliTwo ((c*a)%d) d
  have hperiod (a : ℕ) : f (a+d)=f a := by
    simp [f, Nat.mul_add, Nat.add_mod]
  have hblocks := sum_periodic_blocks f hperiod g 0
  simp only [add_zero, Finset.range_zero, Finset.sum_empty] at hblocks
  change (∑ a ∈ Finset.range j, f a) = (g : ℚ)*completeBernoulliTwoSum d
  rw [hjd]
  change (∑ a ∈ Finset.range (g*d), f a) = _
  rw [hblocks]
  congr 1
  have he := sum_coprime_affine hd hc 0 (fun a => rationalBernoulliTwo a d)
  simpa only [zero_add, completeBernoulliTwoSum, f] using he

/-- Title: `The complete Bernoulli grid sum includes the exact squared gcd correction`. -/
theorem bernoulli_grid_gcd {q j : ℕ} (hj : 0 < j) :
    (∑ a ∈ Finset.range j, rationalBernoulliTwo ((q*a)%j) j) =
      (q.gcd j : ℚ)^2/(6*(j : ℚ)) := by
  have hg : 0 < q.gcd j := Nat.gcd_pos_of_pos_right q hj
  have hgj := Nat.gcd_dvd_right q j
  have hd : 0 < j/(q.gcd j) := Nat.div_pos (Nat.le_of_dvd hj hgj) hg
  have hgQ : (q.gcd j : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
  have hdQ : ((j/(q.gcd j) : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have he : (j : ℚ) = (q.gcd j : ℚ)*((j/(q.gcd j) : ℕ) : ℚ) := by
    exact_mod_cast (Nat.mul_div_cancel' hgj).symm
  rw [bernoulli_grid_gcd_reduction hj, completeBernoulliTwoSum_closed hd, he]
  field_simp

/-- Title: `Counting derivative resets clock by clock gives the exact all-grid curvature moment`. -/
theorem weighted_clock_curvature {q : ℕ} (N : ℕ) (c : ℕ → ℝ) :
    (∑ j ∈ Finset.Icc 1 N, c j*
      ∑ a ∈ Finset.range j, (rationalBernoulliTwo ((q*a)%j) j : ℝ)) = curvatureMoment N q c/6 := by
  unfold curvatureMoment
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have he := congrArg (fun z : ℚ => (z : ℝ)) (bernoulli_grid_gcd (q := q) (Finset.mem_Icc.mp hj).1)
  push_cast at he
  rw [he, Nat.gcd_comm q j]
  ring

end NField.Alignment.CommonResetBernoulliCurvature

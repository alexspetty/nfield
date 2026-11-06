/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetBernoulliCurvature

/-! # The actual reduced-reset curvature and weighted quadrature identity -/

noncomputable section

namespace NField.Alignment.CommonResetWeightedCurvature

open scoped BigOperators
open BernoulliCurvature CommonResetBernoulliCurvature CommonResetWeightedSampling
open CommonResetWeightedSources CommonResetGram

theorem bernoulli_multiplied_reduce {k a : ℕ} (hk : 0 < k) (q : ℕ) :
    rationalBernoulliTwo ((q*a)%k) k =
      rationalBernoulliTwo ((q*(reduceGridPoint k a).2)%(reduceGridPoint k a).1)
        (reduceGridPoint k a).1 := by
  let g := a.gcd k
  have hg : 0 < g := Nat.gcd_pos_of_pos_right a hk
  have hka : a=g*(a/g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left a k)).symm
  have hkk : k=g*(k/g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right a k)).symm
  change rationalBernoulliTwo ((q*a)%k) k = rationalBernoulliTwo ((q*(a/g))%(k/g)) (k/g)
  have he : q*a=g*(q*(a/g)) := by
    calc
      q*a = q*(g*(a/g)) := congrArg (fun n => q*n) hka
      _ = _ := by ring
  conv_lhs => rw [he, hkk, Nat.mul_mod_mul_left, bernoulli_scaled hg]

/-- Title: `Every multiplied Bernoulli grid splits exactly into its reduced reset denominators`. -/
theorem bernoulli_grid_reduced_divisors {k : ℕ} (hk : 0 < k) (q : ℕ) :
    (∑ a ∈ Finset.range k, rationalBernoulliTwo ((q*a)%k) k) =
      ∑ d ∈ k.divisors, multipliedReducedBernoulliTwoSum q d := by
  calc
    _ = ∑ da ∈ reducedFractionPairs k, rationalBernoulliTwo ((q*da.2)%da.1) da.1 := by
      apply Finset.sum_bij (fun a _ => reduceGridPoint k a)
      · exact fun a ha => reduceGridPoint_mem hk ha
      · intro a ha b hb
        exact reduceGridPoint_injective hk ha hb
      · exact reduceGridPoint_surjective hk
      · intro a ha
        exact bernoulli_multiplied_reduce hk q
    _ = _ := by
      unfold reducedFractionPairs multipliedReducedBernoulliTwoSum
      rw [Finset.sum_filter]
      rw [show (∑ da ∈ k.divisors.product (Finset.range k),
          if da.2<da.1 ∧ da.2.Coprime da.1 then rationalBernoulliTwo ((q*da.2)%da.1) da.1 else 0) =
        ∑ d ∈ k.divisors, ∑ a ∈ Finset.range k,
          if a<d ∧ a.Coprime d then rationalBernoulliTwo ((q*a)%d) d else 0 from Finset.sum_product _ _ _]
      apply Finset.sum_congr rfl
      intro d hd
      have hdk := (Nat.mem_divisors.mp hd).1
      have hdle := Nat.le_of_dvd hk hdk
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext a
        simp only [Finset.mem_filter, Finset.mem_range]
        omega
      · intro a ha
        rfl

def weightedResetCurvature (N q : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, resetWeight N c d*(multipliedReducedBernoulliTwoSum q d : ℝ)

/-- Title: `The weighted curvature at every reduced reset, including the origin, equals the printed gcd moment`. -/
theorem weighted_reset_curvature (N q : ℕ) (c : ℕ → ℝ) :
    weightedResetCurvature N q c = curvatureMoment N q c/6 := by
  unfold weightedResetCurvature
  rw [← weighted_divisor_columns]
  calc
    _ = ∑ j ∈ Finset.Icc 1 N, c j*∑ a ∈ Finset.range j,
        (rationalBernoulliTwo ((q*a)%j) j : ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      congr 1
      have he := congrArg (fun z : ℚ => (z : ℝ))
        (bernoulli_grid_reduced_divisors (Finset.mem_Icc.mp hj).1 q)
      push_cast at he
      exact he.symm
    _ = _ := weighted_clock_curvature N c

def valueJumpPhaseSum (N q : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 2 N, ∑ a ∈ (Finset.Ico 1 d).filter (fun a => a.Coprime d),
    (-4*resetWeight N c d*weightedProfile N c ((a : ℝ)/d))*
      CollisionRampEnergy.midpointRow q ((a : ℝ)/d)

def slopeJumpBernoulliSum (N q : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, (-4*(2*slopeMoment N c)*resetWeight N c d)*
    (multipliedReducedBernoulliTwoSum q d : ℝ)

theorem valueJumpPhaseSum_eq (N q : ℕ) (c : ℕ → ℝ) :
    valueJumpPhaseSum N q c = -4*weightedInterior N q c := by
  unfold valueJumpPhaseSum weightedInterior
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro a ha
  ring

theorem slopeJumpBernoulliSum_eq (N q : ℕ) (c : ℕ → ℝ) :
    slopeJumpBernoulliSum N q c = -4*(2*slopeMoment N c)*(curvatureMoment N q c/6) := by
  rw [← weighted_reset_curvature]
  unfold slopeJumpBernoulliSum weightedResetCurvature
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun d hd => by ring)

/-- Title: `The literal finite weighted jump quadrature formula is valid on every positive grid`. -/
theorem weighted_jump_quadrature {q : ℕ} (hq : 0 < q) (N : ℕ) (c : ℕ → ℝ) :
    weightedSample N q c-(∫ x in (0 : ℝ)..1, weightedProfile N c x^2) =
      -resetMass N q c/q+valueJumpPhaseSum N q c/q-slopeJumpBernoulliSum N q c/(2*(q : ℝ)^2) := by
  have he := weighted_sampling_identity hq N c
  unfold weightedDefect at he
  rw [valueJumpPhaseSum_eq, slopeJumpBernoulliSum_eq]
  linear_combination -he

end NField.Alignment.CommonResetWeightedCurvature

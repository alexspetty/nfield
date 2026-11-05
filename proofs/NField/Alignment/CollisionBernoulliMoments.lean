/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionBernoulliProduct

/-!
# Exact mean and variance of the active-coordinate count

These are identities for the actual finite Bernoulli product mass. The
Chebyshev estimate is a consequence of a pointwise squared-deviation
inequality and positivity of that probability mass.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionBernoulliMoments

open scoped BigOperators Classical
open CollisionBernoulliProduct
variable {α : Type*} [DecidableEq α]

def countMean (b : α → ℝ) (S : Finset α) : ℝ := ∑ i ∈ S, b i
def countVariance (b : α → ℝ) (S : Finset α) : ℝ := ∑ i ∈ S, b i*(1-b i)
def lowCountMass (b : α → ℝ) (S : Finset α) : ℝ :=
  bernoulliAverage b S (fun A => if (A.card : ℝ)<countMean b S/2 then 1 else 0)

theorem bernoulli_count_mean (b : α → ℝ) (S : Finset α) :
    bernoulliAverage b S (fun A => (A.card : ℝ))=countMean b S := by
  induction S using Finset.induction_on with
  | empty => simp [bernoulliAverage_empty,countMean]
  | @insert i S hi ih =>
    have he : bernoulliAverage b S (fun A => ((insert i A).card : ℝ))=
        bernoulliAverage b S (fun A => (A.card : ℝ)+1) := by
      apply bernoulliAverage_congr
      intro A hA
      rw [Finset.card_insert_of_notMem (fun h => hi (hA h)),Nat.cast_add,Nat.cast_one]
    rw [bernoulliAverage_insert b hi,he,bernoulliAverage_add,bernoulliAverage_const,ih]
    unfold countMean
    rw [Finset.sum_insert hi]
    ring

theorem bernoulli_count_second_moment (b : α → ℝ) (S : Finset α) :
    bernoulliAverage b S (fun A => (A.card : ℝ)^2)=(countMean b S)^2+countVariance b S := by
  induction S using Finset.induction_on with
  | empty => simp [bernoulliAverage_empty,countMean,countVariance]
  | @insert i S hi ih =>
    have he : bernoulliAverage b S (fun A => ((insert i A).card : ℝ)^2)=
        bernoulliAverage b S (fun A => ((A.card : ℝ)^2+2*(A.card : ℝ))+1) := by
      apply bernoulliAverage_congr
      intro A hA
      rw [Finset.card_insert_of_notMem (fun h => hi (hA h)),Nat.cast_add,Nat.cast_one]
      ring
    rw [bernoulliAverage_insert b hi,he,bernoulliAverage_add,bernoulliAverage_add,
      bernoulliAverage_const_mul,bernoulliAverage_const,bernoulli_count_mean,ih]
    unfold countMean countVariance
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    ring

theorem bernoulli_count_variance (b : α → ℝ) (S : Finset α) :
    bernoulliAverage b S (fun A => ((A.card : ℝ)-countMean b S)^2)=countVariance b S := by
  have he : bernoulliAverage b S (fun A => ((A.card : ℝ)-countMean b S)^2)=
      bernoulliAverage b S (fun A => ((A.card : ℝ)^2+(-2*countMean b S)*(A.card : ℝ))+
        (countMean b S)^2) := by
    apply bernoulliAverage_congr
    intro A _
    ring
  rw [he,bernoulliAverage_add,bernoulliAverage_add,bernoulliAverage_const_mul,
    bernoulliAverage_const,bernoulli_count_mean,bernoulli_count_second_moment]
  ring

omit [DecidableEq α] in
theorem countMean_nonneg (b : α → ℝ) (S : Finset α) (hb : ∀ i∈S, 0 ≤ b i) :
    0 ≤ countMean b S := Finset.sum_nonneg hb

omit [DecidableEq α] in
theorem countVariance_le_mean (b : α → ℝ) (S : Finset α) :
    countVariance b S ≤ countMean b S := by
  apply Finset.sum_le_sum
  intro i _
  nlinarith [sq_nonneg (b i)]

theorem lowCountMass_nonneg (b : α → ℝ) (S : Finset α)
    (hb : ∀ i∈S, 0 ≤ b i ∧ b i ≤ 1) : 0 ≤ lowCountMass b S := by
  apply bernoulliAverage_nonneg b S hb
  intro A _
  split_ifs <;> norm_num

theorem lowCountMass_le_one (b : α → ℝ) (S : Finset α)
    (hb : ∀ i∈S, 0 ≤ b i ∧ b i ≤ 1) : lowCountMass b S ≤ 1 := by
  rw [← bernoulliAverage_const b S 1]
  apply bernoulliAverage_mono b S hb
  intro A _
  split_ifs <;> norm_num

theorem lowCountMass_chebyshev (b : α → ℝ) (S : Finset α)
    (hb : ∀ i∈S, 0 ≤ b i ∧ b i ≤ 1) (hm : 0<countMean b S) :
    lowCountMass b S ≤ 4/countMean b S := by
  have hp : ∀ A⊆S,
      ((countMean b S)^2/4)*(if (A.card : ℝ)<countMean b S/2 then 1 else 0) ≤
        ((A.card : ℝ)-countMean b S)^2 := by
    intro A _
    split_ifs with h
    · have hx : 0 ≤ countMean b S/2-(A.card : ℝ) := by linarith
      have hy : 0 ≤ 3*countMean b S/2-(A.card : ℝ) := by linarith
      nlinarith [mul_nonneg hx hy]
    · simp only [mul_zero]
      exact sq_nonneg _
  have h := bernoulliAverage_mono b S hb hp
  rw [bernoulliAverage_const_mul,bernoulli_count_variance] at h
  change ((countMean b S)^2/4)*lowCountMass b S ≤ countVariance b S at h
  have hv := countVariance_le_mean b S
  apply (le_div_iff₀ hm).mpr
  have hmul : countMean b S*(countMean b S*lowCountMass b S-4) ≤ 0 := by nlinarith
  have hsign : countMean b S*lowCountMass b S-4 ≤ 0 := by
    by_contra hn
    have hp := mul_pos hm (lt_of_not_ge hn)
    linarith
  nlinarith

end NField.Alignment.CollisionBernoulliMoments

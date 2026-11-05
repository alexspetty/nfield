/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionBernoulliMoments
import NField.Alignment.CollisionActivationRestriction

/-!
# Uniform concentration under the finite Bernoulli product law

The active-count inverse-square-root estimate follows from the exact
variance and a split at half the mean. Together with the proved coupling
and Sperner estimate it gives an explicit universal constant of twenty.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionBernoulliActivationFinite

open scoped BigOperators Classical
open CollisionBernoulliProduct CollisionBernoulliMoments CollisionActivationRestriction
variable {α : Type*} [DecidableEq α]

def inverseRootAverage (b : α → ℝ) (S : Finset α) : ℝ :=
  bernoulliAverage b S (fun A => 1/Real.sqrt (1+(A.card : ℝ)))

theorem inverseRoot_count_le_one (k : ℕ) : 1/Real.sqrt (1+(k : ℝ)) ≤ 1 := by
  have hpos : 0<Real.sqrt (1+(k : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  apply (div_le_one hpos).mpr
  have h := Real.sqrt_le_sqrt (show (1 : ℝ)≤1+(k : ℝ) by linarith [Nat.cast_nonneg (α := ℝ) k])
  simpa only [Real.sqrt_one] using h

theorem inverseRoot_good_count {m : ℝ} (hm : 0≤m) (k : ℕ) (hk : m/2≤(k : ℝ)) :
    1/Real.sqrt (1+(k : ℝ)) ≤ 2/Real.sqrt (1+m) := by
  have hkp : 0<Real.sqrt (1+(k : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  have hmp : 0<Real.sqrt (1+m) := Real.sqrt_pos.mpr (by positivity)
  apply (div_le_div_iff₀ hkp hmp).mpr
  have h : Real.sqrt (1+m) ≤ Real.sqrt (4*(1+(k : ℝ))) :=
    Real.sqrt_le_sqrt (by linarith [Nat.cast_nonneg (α := ℝ) k])
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ)≤4)] at h
  norm_num at h ⊢
  exact h

theorem inverseRootAverage_le_one (b : α → ℝ) (S : Finset α)
    (hb : ∀ i∈S, 0 ≤ b i ∧ b i ≤ 1) : inverseRootAverage b S ≤ 1 := by
  rw [← bernoulliAverage_const b S 1]
  exact bernoulliAverage_mono b S hb (fun A _ => inverseRoot_count_le_one A.card)

theorem inverseRootAverage_split (b : α → ℝ) (S : Finset α)
    (hb : ∀ i∈S, 0 ≤ b i ∧ b i ≤ 1) :
    inverseRootAverage b S ≤ lowCountMass b S+2/Real.sqrt (1+countMean b S) := by
  have hm := countMean_nonneg b S (fun i hi => (hb i hi).1)
  have hp : ∀ A⊆S, 1/Real.sqrt (1+(A.card : ℝ)) ≤
      (if (A.card : ℝ)<countMean b S/2 then 1 else 0)+2/Real.sqrt (1+countMean b S) := by
    intro A _
    by_cases hA : (A.card : ℝ)<countMean b S/2
    · rw [if_pos hA]
      exact (inverseRoot_count_le_one A.card).trans (le_add_of_nonneg_right (by positivity))
    · rw [if_neg hA,zero_add]
      exact inverseRoot_good_count hm A.card (le_of_not_gt hA)
  have h := bernoulliAverage_mono b S hb hp
  rw [bernoulliAverage_add,bernoulliAverage_const] at h
  exact h

theorem inverseRootAverage_bound (b : α → ℝ) (S : Finset α)
    (hb : ∀ i∈S, 0 ≤ b i ∧ b i ≤ 1) :
    inverseRootAverage b S ≤ 10/Real.sqrt (1+countMean b S) := by
  have hm := countMean_nonneg b S (fun i hi => (hb i hi).1)
  have hpos : 0<Real.sqrt (1+countMean b S) := Real.sqrt_pos.mpr (by positivity)
  by_cases hsmall : countMean b S≤1
  · apply (inverseRootAverage_le_one b S hb).trans
    apply (le_div_iff₀ hpos).mpr
    have h := Real.sqrt_le_sqrt (show 1+countMean b S≤4 by linarith)
    norm_num at h ⊢
    linarith
  · have hm1 : 1<countMean b S := lt_of_not_ge hsmall
    have hm0 : 0<countMean b S := by linarith
    have hroot : Real.sqrt (1+countMean b S) ≤ 2*countMean b S := by
      calc
        _ ≤ Real.sqrt (4*(countMean b S)^2) :=
          Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (countMean b S-1)])
        _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ)≤4),Real.sqrt_sq hm]; norm_num
    have hbad : 4/countMean b S ≤ 8/Real.sqrt (1+countMean b S) := by
      apply (div_le_div_iff₀ hm0 hpos).mpr
      linarith
    calc
      _ ≤ lowCountMass b S+2/Real.sqrt (1+countMean b S) := inverseRootAverage_split b S hb
      _ ≤ 4/countMean b S+2/Real.sqrt (1+countMean b S) :=
        add_le_add (lowCountMass_chebyshev b S hb hm0) le_rfl
      _ ≤ 8/Real.sqrt (1+countMean b S)+2/Real.sqrt (1+countMean b S) := add_le_add hbad le_rfl
      _ = _ := by ring

theorem bernoulli_product_short_interval_bound (b : α → ℝ) (S : Finset α)
    (hb : ∀ i∈S, 0 ≤ b i ∧ b i ≤ 1/2) (F : Finset α → ℝ)
    {a u v : ℝ} (ha : 0<a) (huv : v-u<a)
    (hF : ∀ s i, i∉s → F s+a ≤ F (insert i s)) :
    bernoulliAverage b S (fun A => if F A∈Set.Icc u v then 1 else 0) ≤
      20/Real.sqrt (1+countMean b S) := by
  have hb2 : ∀ i∈S, 0 ≤ 2*b i ∧ 2*b i ≤ 1 := by
    intro i hi
    obtain ⟨h0,h1⟩ := hb i hi
    constructor <;> linarith
  have hm := countMean_nonneg b S (fun i hi => (hb i hi).1)
  have hmean : countMean (fun i => 2*b i) S=2*countMean b S := by
    unfold countMean
    rw [Finset.mul_sum]
  have hpos : 0<Real.sqrt (1+countMean b S) := Real.sqrt_pos.mpr (by positivity)
  calc
    _ = bernoulliAverage (fun i => 2*b i) S
        (fun A => fairAverage A (fun B => if F B∈Set.Icc u v then 1 else 0)) :=
      (activation_coupling b S _).symm
    _ ≤ bernoulliAverage (fun i => 2*b i) S (fun A => 2/Real.sqrt (1+(A.card : ℝ))) := by
      apply bernoulliAverage_mono _ S hb2
      intro A _
      simpa only [add_comm] using fair_short_interval_on A F ha huv hF
    _ = 2*inverseRootAverage (fun i => 2*b i) S := by
      unfold inverseRootAverage
      rw [← bernoulliAverage_const_mul]
      apply bernoulliAverage_congr
      intro A _
      ring
    _ ≤ 2*(10/Real.sqrt (1+countMean (fun i => 2*b i) S)) :=
      mul_le_mul_of_nonneg_left (inverseRootAverage_bound _ S hb2) (by norm_num)
    _ = 20/Real.sqrt (1+2*countMean b S) := by rw [hmean]; ring
    _ ≤ 20/Real.sqrt (1+countMean b S) :=
      div_le_div_of_nonneg_left (by norm_num) hpos (Real.sqrt_le_sqrt (by linarith))

end NField.Alignment.CollisionBernoulliActivationFinite

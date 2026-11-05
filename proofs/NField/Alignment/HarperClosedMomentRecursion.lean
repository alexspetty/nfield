/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperRecursionContraction

/-!
# Closing the uniform critical moment recursion

For each fixed scale, Jensen bounds the set of all weighted moments.
Its finite supremum obeys a contraction inequality. The resulting bound
is independent of scale; no limiting argument in the exponent is assumed.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperClosedMomentRecursion
open Set HarperMomentRecursion HarperRecursionWeights HarperRecursionContraction

def recursionConstant (C D : ℝ) : ℝ := 2*max 1 (2*C*contractionAmplitude D)

theorem recursionConstant_pos (C D : ℝ) : 0 < recursionConstant C D := by
  unfold recursionConstant
  linarith [le_max_left (1 : ℝ) (2*C*contractionAmplitude D)]

theorem weightedMoment_bound {s q : ℝ} {m : ℝ → ℝ}
    (hs : 0 ≤ s) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hm : m q ≤ 1) :
    weightedMoment s m q ≤ 1+s := by
  have hw := momentWeight_ge_one hs hq1
  calc
    _ ≤ (momentWeight s q)^q*1 :=
      mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg (by linarith) _)
    _ ≤ momentWeight s q := by
      rw [mul_one]
      exact Real.rpow_le_self_of_one_le hw hq1
    _ ≤ _ := momentWeight_le hs hq0

theorem weightedMoment_small {s q : ℝ} {m : ℝ → ℝ}
    (hs : 0 ≤ s) (hq1 : q ≤ 1) (hm : m q ≤ 1) (hsmall : (1-q)*s ≤ 1) :
    weightedMoment s m q ≤ 2 := by
  have hw := momentWeight_ge_one hs hq1
  calc
    _ ≤ (momentWeight s q)^q*1 :=
      mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg (by linarith) _)
    _ ≤ momentWeight s q := by
      rw [mul_one]
      exact Real.rpow_le_self_of_one_le hw hq1
    _ ≤ _ := by unfold momentWeight; linarith

theorem uniform_weighted_moment_bound {s C D : ℝ} {m : ℝ → ℝ}
    (hs : 0 < s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hseed : ∀ q : ℝ, 3/4 ≤ q → q ≤ 1 → 0 ≤ m q ∧ m q ≤ 1)
    (hrec : ∀ q : ℝ, 3/4 ≤ q → q < 1 → ∀ a : ℝ, 1 ≤ a →
      m q ≤ (C*min 1 (a/s))^q+(m (nextExponent q))^(q/nextExponent q)*
        (D*Real.exp (-2*a))^(1-q/nextExponent q)) :
    ∀ q : ℝ, 3/4 ≤ q → q ≤ 1 → weightedMoment s m q ≤ recursionConstant C D := by
  let T : Set ℝ := weightedMoment s m '' Icc (3/4) 1
  have hT : T.Nonempty := ⟨weightedMoment s m 1,1,by norm_num,rfl⟩
  have hB : BddAbove T := by
    refine ⟨1+s,?_⟩
    rintro y ⟨q,hq,rfl⟩
    exact weightedMoment_bound hs.le (by linarith [hq.1]) hq.2 (hseed q hq.1 hq.2).2
  let S := sSup T
  have hle (q : ℝ) (hq : q ∈ Icc (3/4) 1) : weightedMoment s m q ≤ S :=
    le_csSup hB ⟨q,hq,rfl⟩
  have hS : S ≤ max 2 (max 1 (2*C*contractionAmplitude D)+(1/2)*max 1 S) := by
    apply csSup_le hT
    rintro y ⟨q,hq,rfl⟩
    by_cases hsmall : (1-q)*s ≤ 1
    · exact (weightedMoment_small hs.le hq.2 (hseed q hq.1 hq.2).2 hsmall).trans (le_max_left _ _)
    · have hq0 : 0 < q := by linarith [hq.1]
      have hq1 : q < 1 := lt_of_le_of_ne hq.2 (by
        intro he
        subst q
        norm_num at hsmall)
      have hr := nextExponent_bounds hq0.le hq1
      have hrdom : nextExponent q ∈ Icc (3/4) 1 := ⟨hq.1.trans hr.2.1.le,hr.2.2.le⟩
      have h := weighted_recursion_bound hs hC hD hq0 hq1 (le_of_not_ge hsmall)
        (hseed _ hrdom.1 hrdom.2).1 (hle _ hrdom)
        (hrec q hq.1 hq1 _ (recursion_amplitude_ge_one (contractionAmplitude_ge_one D) hq0.le hq1))
      exact h.trans (le_max_right _ _)
  have hSbound : S ≤ recursionConstant C D := by
    have hK := le_max_left (1 : ℝ) (2*C*contractionAmplitude D)
    unfold recursionConstant
    by_cases h : S ≤ 1
    · linarith
    · rw [max_eq_right (le_of_not_ge h)] at hS
      rcases le_max_iff.mp hS with h | h <;> linarith
  intro q hq0 hq1
  exact (hle q ⟨hq0,hq1⟩).trans hSbound

theorem uniform_moment_bound {s C D : ℝ} {m : ℝ → ℝ}
    (hs : 0 < s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hseed : ∀ q : ℝ, 3/4 ≤ q → q ≤ 1 → 0 ≤ m q ∧ m q ≤ 1)
    (hrec : ∀ q : ℝ, 3/4 ≤ q → q < 1 → ∀ a : ℝ, 1 ≤ a →
      m q ≤ (C*min 1 (a/s))^q+(m (nextExponent q))^(q/nextExponent q)*
        (D*Real.exp (-2*a))^(1-q/nextExponent q)) :
    ∀ q : ℝ, 3/4 ≤ q → q ≤ 1 → m q ≤ recursionConstant C D/(momentWeight s q)^q := by
  intro q hq0 hq1
  have hw := momentWeight_ge_one hs.le hq1
  apply (le_div_iff₀ (Real.rpow_pos_of_pos (by linarith : 0 < momentWeight s q) q)).mpr
  simpa only [weightedMoment,mul_comm] using uniform_weighted_moment_bound hs hC hD hseed hrec q hq0 hq1

end NField.Alignment.HarperClosedMomentRecursion

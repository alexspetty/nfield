/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetRetainedBands
import NField.Alignment.CommonResetFrequencies
import NField.Alignment.CommonResetBernoulliLifts

/-! # Natural-index correspondence for every original half-range frequency -/

noncomputable section

namespace NField.Alignment.CommonResetNaturalFrequencies

open scoped BigOperators
open CommonResetRetainedBands CommonResetBandPhases CommonResetEndpointTailRows
open CommonResetHalfFrequencies CommonResetBernoulliLifts CommonResetFrequencies

def positiveHalf (t : ℕ) : Finset ℕ := (Finset.range t).filter (fun a => 0 < a ∧ 2*a < t)

theorem sum_lowerResidues_values {R : Type*} [AddCommMonoid R] {t : ℕ} [NeZero t]
    (f : ℕ → R) : (∑ a ∈ lowerResidues t, f a.val) = ∑ a ∈ positiveHalf t, f a := by
  classical
  rw [lowerResidues, Finset.sum_filter]
  rw [sum_residue_values (fun a : ℕ => if 0 < a ∧ 2*a < t then f a else 0)]
  exact (Finset.sum_filter _ _).symm

theorem sum_lowerUnits_values {R : Type*} [AddCommMonoid R] {t : ℕ} [NeZero t]
    (f : ℕ → R) :
    (∑ a ∈ lowerUnits t, f a.val.val) =
      ∑ a ∈ (positiveHalf t).filter (fun a => a.Coprime t), f a := by
  classical
  apply Finset.sum_bij (fun a _ => a.val.val)
  · intro a ha
    have haI := (Finset.mem_filter.mp ha).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt _), haI⟩,
      ZMod.val_coe_unit_coprime a⟩
  · intro a ha b hb he
    apply Units.ext
    exact ZMod.val_injective t he
  · intro a ha
    have haD := Finset.mem_filter.mp ha
    have haI := Finset.mem_filter.mp haD.1
    let z := ZMod.unitOfCoprime a haD.2
    have hz : z.val.val = a := by
      change (ZMod.unitOfCoprime a haD.2).val.val = a
      rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp haI.1)]
    refine ⟨z, ?_, hz⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [hz] using haI.2⟩
  · intro a ha
    rfl

/-- Title: `The actual finite frequency equals the three original natural-index linked phases`. -/
theorem unit_frequency_original {p t : ℕ} [NeZero t] (hp : 2 ≤ p)
    (u : (ZMod t)ˣ) (v j : ZMod t) (hj : j ∈ lowerResidues t) :
    frequencyTerm (p-1) (p^2) u v j = originalFrequency p t u.val.val v.val j.val := by
  rw [frequencyTerm_three_phases hp u v j hj]
  simp only [originalFrequency, gatedPhase, if_pos (ZMod.val_coe_unit_coprime u)]

/-- Title: `The conductor source retains every permitted unit and nonunit frequency under natural reindexing`. -/
theorem completeFrequencies_natural {p t : ℕ} (hp : 2 ≤ p) (ht : 2 ≤ t) :
    completeFrequencies (p-1) (p^2) t =
      (harmonic ((p-1)/t) : ℝ)*∑ u ∈ positiveHalf t, ∑ v ∈ positiveHalf t,
        ∑ j ∈ positiveHalf t, originalFrequency p t u v j := by
  letI : NeZero t := ⟨by omega⟩
  rw [completeFrequencies, dif_pos ht]
  congr 1
  calc
    _ = ∑ u ∈ lowerUnits t, ∑ v ∈ lowerResidues t,
        ∑ j ∈ lowerResidues t, originalFrequency p t u.val.val v.val j.val := by
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      exact Finset.sum_congr rfl (fun j hj => unit_frequency_original hp u v j hj)
    _ = ∑ u ∈ (positiveHalf t).filter (fun u => u.Coprime t), ∑ v ∈ positiveHalf t,
        ∑ j ∈ positiveHalf t, originalFrequency p t u v j := by
      rw [← sum_lowerUnits_values (t := t) (fun u : ℕ =>
        ∑ v ∈ positiveHalf t, ∑ j ∈ positiveHalf t, originalFrequency p t u v j)]
      apply Finset.sum_congr rfl
      intro u hu
      calc
        _ = ∑ v ∈ lowerResidues t, ∑ j ∈ positiveHalf t, originalFrequency p t u.val.val v.val j := by
          apply Finset.sum_congr rfl
          intro v hv
          exact sum_lowerResidues_values (t := t) (fun j => originalFrequency p t u.val.val v.val j)
        _ = _ := sum_lowerResidues_values (t := t)
          (fun v : ℕ => ∑ j ∈ positiveHalf t, originalFrequency p t u.val.val v j)
    _ = _ := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro u hu
      by_cases hc : u.Coprime t
      · rw [if_pos hc]
      · simp only [if_neg hc, originalFrequency, gatedPhase, add_zero, Finset.sum_const_zero]

theorem positiveHalf_subset {t p : ℕ} (htp : t ≤ p) : positiveHalf t ⊆ Finset.Icc 1 p := by
  intro a ha
  have haD := Finset.mem_filter.mp ha
  exact Finset.mem_Icc.mpr ⟨haD.2.1, (Nat.le_of_lt (Finset.mem_range.mp haD.1)).trans htp⟩

theorem positiveHalf_sum_uniform {R : Type*} [AddCommMonoid R] {t p : ℕ} (htp : t ≤ 2*p+1)
    (f : ℕ → R) :
    (∑ a ∈ positiveHalf t, f a) = ∑ a ∈ Finset.Icc 1 p, if 2*a < t then f a else 0 := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext a
    simp only [positiveHalf, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  · intro a _
    rfl

def naturalFrequency (p t u v j : ℕ) : ℝ :=
  if 2*u < t ∧ 2*v < t ∧ 2*j < t then originalFrequency p t u v j else 0

/-- Title: `The complete conductor source uses one common natural frequency range without omitted triples`. -/
theorem completeFrequencies_uniform {p t P : ℕ} (hp : 2 ≤ p) (ht : 2 ≤ t) (htP : t ≤ 2*P+1) :
    completeFrequencies (p-1) (p^2) t =
      (harmonic ((p-1)/t) : ℝ)*∑ u ∈ Finset.Icc 1 P, ∑ v ∈ Finset.Icc 1 P,
        ∑ j ∈ Finset.Icc 1 P, naturalFrequency p t u v j := by
  rw [completeFrequencies_natural hp ht]
  simp_rw [positiveHalf_sum_uniform htP]
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  by_cases huT : 2*u < t
  · rw [if_pos huT]
    apply Finset.sum_congr rfl
    intro v hv
    by_cases hvT : 2*v < t
    · rw [if_pos hvT]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [naturalFrequency, huT, hvT, true_and]
    · simp only [naturalFrequency, hvT, and_false, false_and, if_false, Finset.sum_const_zero]
  · simp only [naturalFrequency, huT, false_and, if_false, Finset.sum_const_zero]

end NField.Alignment.CommonResetNaturalFrequencies

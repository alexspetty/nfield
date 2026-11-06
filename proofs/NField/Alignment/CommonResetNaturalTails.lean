/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetNaturalFrequencies
import NField.Alignment.CommonResetEndpointTailAssembly

/-! # Exact correspondence between natural frequency tails and their proved complete tails -/

noncomputable section

namespace NField.Alignment.CommonResetNaturalTails

open scoped BigOperators
open CommonResetNaturalFrequencies CommonResetRetainedBands CommonResetBandPhases
open CommonResetFrequencies CommonResetHalfFrequencies CommonResetLinearTailAssembly
open CommonResetTailRows CommonResetEndpointTailRows CommonResetEndpointTailAssembly

theorem naturalFrequency_nonunit (p t u v j : ℕ) (hcop : ¬ u.Coprime t) :
    naturalFrequency p t u v j = 0 := by
  unfold naturalFrequency
  split_ifs
  · simp only [originalFrequency, gatedPhase, if_neg hcop, add_zero]
  · rfl

theorem originalFrequency_unit_cast {p t u v j : ℕ} [NeZero t]
    (hp : 2 ≤ p) (hut : u < t) (hvt : v < t) (hj : 0 < j) (hjt : 2*j < t)
    (hcop : u.Coprime t) :
    originalFrequency p t u v j =
      frequencyTerm (p-1) (p^2) (ZMod.unitOfCoprime u hcop) (v : ZMod t) (j : ZMod t) := by
  have huval : (ZMod.unitOfCoprime u hcop).val.val = u := by
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hut]
  have hvval : (v : ZMod t).val=v := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt hvt]
  have hjval : (j : ZMod t).val=j := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have hjlower : (j : ZMod t) ∈ lowerResidues t := by
    simp only [lowerResidues, Finset.mem_filter, Finset.mem_univ, true_and, hjval]
    exact ⟨hj, hjt⟩
  have he := unit_frequency_original hp (ZMod.unitOfCoprime u hcop) (v : ZMod t) (j : ZMod t) hjlower
  simpa only [huval, hvval, hjval] using he.symm

/-- Title: `The natural linear-frequency tail is exactly the original completed linear tail`. -/
theorem natural_linear_slice {p t u j : ℕ} (hp : 2 ≤ p) (ht : 0 < t)
    (hut : 2*u < t) (hj : 0 < j) (hjt : 2*j < t)
    (start length : ℕ) (hs : 0 < start) :
    (∑ a ∈ Finset.range length, naturalFrequency p t u (start+a) j) =
      naturalLinearTail (p-1) (p^2) t u j start length := by
  letI : NeZero t := ⟨ht.ne'⟩
  rw [naturalLinearTail, dif_pos ht]
  by_cases hc : u.Coprime t
  · rw [dif_pos hc, linearTail]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases hva : 2*(start+a)<t
    · rw [naturalFrequency, if_pos ⟨hut, hva, hjt⟩, if_pos hva]
      exact originalFrequency_unit_cast hp (by omega) (by omega) hj hjt hc
    · simp only [naturalFrequency, hva, and_false, false_and, if_false]
  · rw [dif_neg hc]
    simp only [naturalFrequency_nonunit p t u _ j hc, Finset.sum_const_zero]

/-- Title: `The natural endpoint-frequency tail is exactly the original completed endpoint tail`. -/
theorem natural_endpoint_slice {p t u v : ℕ} (hp : 2 ≤ p) (ht : 0 < t)
    (hut : 2*u < t) (hvt : 2*v < t)
    (start length : ℕ) (hs : 0 < start) :
    (∑ a ∈ Finset.range length, naturalFrequency p t u v (start+a)) =
      naturalEndpointTail p t u v start length := by
  letI : NeZero t := ⟨ht.ne'⟩
  rw [naturalEndpointTail, dif_pos ht]
  by_cases hc : u.Coprime t
  · rw [dif_pos hc, endpointTail]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases hja : 2*(start+a)<t
    · rw [naturalFrequency, if_pos ⟨hut, hvt, hja⟩, if_pos hja]
      exact originalFrequency_unit_cast hp (by omega) (by omega) (by omega) hja hc
    · simp only [naturalFrequency, hja, and_false, if_false]
  · rw [dif_neg hc]
    simp only [naturalFrequency_nonunit p t u v _ hc, Finset.sum_const_zero]

end NField.Alignment.CommonResetNaturalTails

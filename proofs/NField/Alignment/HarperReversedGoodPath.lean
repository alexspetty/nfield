/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperBlockPhaseShift

/-!
# The good event as a reversed block path

Natural subtraction is used only inside Fin(M+1), where every index is
at most M. The suffix sums over [j,M] therefore equal the literal initial
partial sums in reversed order, with no truncated-subtraction collisions.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperReversedGoodPath
open scoped BigOperators
open MeasureTheory Set SteinhausMoment HarperPathGrid HarperFrequencyMesh HarperCriticalGoodEvent
  HarperPrimeBlockLaw HarperPrimeBlockPath

def reverseIndex (M : ℕ) (i : Fin (M+1)) : ℕ := M-i.val

theorem reverseIndex_strictAnti (M : ℕ) : StrictAnti (reverseIndex M) := by
  intro i j hij
  dsimp [reverseIndex]
  have hi := i.isLt
  have hj := j.isLt
  have hij' : i.val < j.val := hij
  omega

theorem reverseIndex_zero (M : ℕ) : reverseIndex M 0 = M := by simp [reverseIndex]

theorem reverseIndex_le (M : ℕ) (i : Fin (M+1)) : reverseIndex M i ≤ M := Nat.sub_le _ _

theorem reversed_partialSum (M : ℕ) (f : ℕ → ℝ) (j : Fin (M+1)) :
    partialSum (fun i => f (reverseIndex M i)) j =
      ∑ l ∈ Finset.Icc (reverseIndex M j) M, f l := by
  classical
  unfold partialSum
  apply Finset.sum_bij (fun i _ => reverseIndex M i)
  · intro i hi
    simp only [Finset.mem_Iic,Fin.le_def] at hi
    simp only [Finset.mem_Icc,reverseIndex]
    omega
  · intro i hi k hk hik
    apply Fin.ext
    dsimp [reverseIndex] at hik
    have hi' := i.isLt
    have hk' := k.isLt
    omega
  · intro l hl
    simp only [Finset.mem_Icc,reverseIndex] at hl
    refine ⟨⟨M-l,by omega⟩,?_,?_⟩
    · simp only [Finset.mem_Iic,Fin.le_def]
      have hj := j.isLt
      omega
    · dsimp [reverseIndex]
      omega
  · intro i _
    rfl

def fixedGoodPath (x : ℝ) (M : ℕ) (t a : ℝ) : Set PhaseSpace :=
  blockPathEvent x (reverseIndex M) (fun i => approximation x t (reverseIndex M i))
    (fun i => -sourceAllowance x a (reverseIndex M i))
    (fun i => sourceAllowance x a (reverseIndex M i))

theorem fixedGoodPath_measurable (x : ℝ) (M : ℕ) (t a : ℝ) :
    MeasurableSet (fixedGoodPath x M t a) := blockPathEvent_measurable _ _ _ _ _

theorem fixedGoodPath_iff (x : ℝ) (M : ℕ) (t a : ℝ) (ω : PhaseSpace) :
    ω ∈ fixedGoodPath x M t a ↔ ∀ j ≤ M, |suffixLog x M t j ω| ≤ sourceAllowance x a j := by
  constructor
  · intro h j hj
    let i : Fin (M+1) := ⟨M-j,by omega⟩
    have hi : reverseIndex M i = j := by dsimp [reverseIndex,i]; omega
    have hp := h i
    rw [reversed_partialSum M (fun l => blockLog x l (approximation x t l) ω) i,hi] at hp
    simpa only [hi,suffixLog] using (abs_le.mpr hp)
  · intro h i
    have hp := abs_le.mp (h (reverseIndex M i) (reverseIndex_le M i))
    change -sourceAllowance x a (reverseIndex M i) ≤
        partialSum (fun j => blockLog x (reverseIndex M j) (approximation x t (reverseIndex M j)) ω) i ∧ _
    rw [reversed_partialSum M (fun l => blockLog x l (approximation x t l) ω) i]
    exact hp

theorem sourceGoodEvent_subset_fixed {x t a : ℝ} (M : ℕ) (ht : |t| ≤ 1/2) :
    sourceGoodEvent x M a ⊆ fixedGoodPath x M t a := by
  intro ω hω
  exact (fixedGoodPath_iff x M t a ω).mpr (hω t ht)

end NField.Alignment.HarperReversedGoodPath

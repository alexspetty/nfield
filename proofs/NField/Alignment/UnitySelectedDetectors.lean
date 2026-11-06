/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.UnityGramCosts

/-! # Uniform cost for every finite selected subfamily of prescribed depths -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.UnitySelectedDetectors
open scoped BigOperators
open UnityNativeHilbert UnityFiniteGram UnityPrescribedDetectors UnityDetectorBandCost UnityGramCosts

def selectedFamily (N : ℕ) (S : Finset ℕ) : S → NativeHilbert := fun h => detector N h

theorem selected_trace_le_cost (N : ℕ) (S : Finset ℕ) :
    Matrix.trace (gramMatrix (selectedFamily N S))≤∑ h∈S, bandCost N h := by
  rw [gramMatrix_trace]
  change (∑ h : S, ‖detector N h‖^2)≤∑ h∈S, bandCost N h
  rw [Finset.sum_coe_sort S (fun h => ‖detector N h‖^2)]
  exact Finset.sum_le_sum (fun h _ => detector_cost N h)

/-- Title: `Every selected detector subfamily has the same uniform cost bound`.

 The exact uniform cost chain survives any finite selection of depths. -/
theorem selected_uniform_cost (N : ℕ) (S : Finset ℕ) :
    (∀h : S, gramMatrix (selectedFamily N S) h h≤bandCost N h ∧ bandCost N h≤1) ∧
    largestEigenvalue (selectedFamily N S)≤Matrix.trace (gramMatrix (selectedFamily N S)) ∧
    Matrix.trace (gramMatrix (selectedFamily N S))≤(∑ h∈S, bandCost N h) ∧
    (∑ h∈S, bandCost N h)≤2 := by
  refine ⟨?_, largestEigenvalue_le_trace _, selected_trace_le_cost N S,
    selected_band_cost_le_two N S⟩
  intro h
  rw [gramMatrix_diagonal]
  exact ⟨detector_cost N h, UnityProjectionBands.newRoot_cost _⟩

end NField.Alignment.UnitySelectedDetectors

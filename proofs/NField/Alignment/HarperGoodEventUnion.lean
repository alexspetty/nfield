/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperRoundedSourcePath

/-!
# A finite union bound for failure of the actual critical good event

Each scale contributes one integer interval of possible current codes.
The original event still quantifies over the entire unit frequency
interval. Tail-probability estimates remain explicit inputs to the last
aggregation theorem; no exceptional-event decay is asserted here.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperGoodEventUnion
open scoped BigOperators
open MeasureTheory Set SteinhausMoment HarperFrequencyRounding HarperFrequencyMesh
  HarperFrequencyCodes HarperCriticalGoodEvent

theorem goodEvent_iff_finite {x : ℝ} (hx : 1 < x) (M : ℕ)
    (hM : Real.exp 2 ≤ logScale x M) (A : ℕ → ℝ) (ω : PhaseSpace) :
    ω ∈ goodEvent x M A ↔ ∀ j : Fin (M+1),
      ∀ k ∈ (attainableCodes_finite hx j.val (hM.trans (logScale_antitone hx (by omega)))).toFinset,
        |suffixLog x M (representative (mesh x) j.val k) j.val ω| ≤ A j.val := by
  rw [goodEvent_iff_codes]
  constructor
  · intro h j k hk
    exact h j.val (by omega) k ((Set.Finite.mem_toFinset _).mp hk)
  · intro h j hj k hk
    exact h ⟨j,by omega⟩ k ((Set.Finite.mem_toFinset _).mpr hk)

theorem goodEvent_compl_subset {x : ℝ} (hx : 1 < x) (M : ℕ)
    (hM : Real.exp 2 ≤ logScale x M) (A : ℕ → ℝ) :
    (goodEvent x M A)ᶜ ⊆ ⋃ j : Fin (M+1), ⋃ k ∈ codeBox (mesh x j.val),
      {ω | A j.val < |suffixLog x M (representative (mesh x) j.val k) j.val ω|} := by
  classical
  intro ω hω
  have hn : ¬ ∀ j ≤ M, ∀ k ∈ attainableCodes (mesh x) j,
      |suffixLog x M (representative (mesh x) j k) j ω| ≤ A j := by
    rwa [← goodEvent_iff_codes]
  push Not at hn
  obtain ⟨j,hj,k,hk,hbad⟩ := hn
  have hbox := attainableCodes_subset_box hx j (hM.trans (logScale_antitone hx hj)) hk
  exact Set.mem_iUnion.mpr ⟨⟨j,by omega⟩,Set.mem_iUnion.mpr ⟨k,Set.mem_iUnion.mpr ⟨hbox,hbad⟩⟩⟩

theorem goodEvent_failure_union_bound {x : ℝ} (hx : 1 < x) (M : ℕ)
    (hM : Real.exp 2 ≤ logScale x M) (A : ℕ → ℝ)
    (μ : Measure PhaseSpace) [IsFiniteMeasure μ] :
    μ.real (goodEvent x M A)ᶜ ≤ ∑ j : Fin (M+1), ∑ k ∈ codeBox (mesh x j.val),
      μ.real {ω | A j.val < |suffixLog x M (representative (mesh x) j.val k) j.val ω|} := by
  calc
    _ ≤ μ.real (⋃ j : Fin (M+1), ⋃ k ∈ codeBox (mesh x j.val),
        {ω | A j.val < |suffixLog x M (representative (mesh x) j.val k) j.val ω|}) :=
      measureReal_mono (goodEvent_compl_subset hx M hM A) (by finiteness)
    _ ≤ ∑ j : Fin (M+1), μ.real (⋃ k ∈ codeBox (mesh x j.val),
        {ω | A j.val < |suffixLog x M (representative (mesh x) j.val k) j.val ω|}) :=
      measureReal_iUnion_fintype_le _
    _ ≤ _ := Finset.sum_le_sum (fun j _ => measureReal_biUnion_finset_le _ _)

theorem goodEvent_failure_card_bound {x : ℝ} (hx : 1 < x) (M : ℕ)
    (hM : Real.exp 2 ≤ logScale x M) (A p : ℕ → ℝ)
    (μ : Measure PhaseSpace) [IsFiniteMeasure μ]
    (hp : ∀ j ≤ M, 0 ≤ p j)
    (htail : ∀ j : Fin (M+1), ∀ k ∈ codeBox (mesh x j.val),
      μ.real {ω | A j.val < |suffixLog x M (representative (mesh x) j.val k) j.val ω|} ≤ p j.val) :
    μ.real (goodEvent x M A)ᶜ ≤ ∑ j : Fin (M+1), (2/(mesh x j.val)+3)*p j.val := by
  apply (goodEvent_failure_union_bound hx M hM A μ).trans
  apply Finset.sum_le_sum
  intro j _
  have hj : j.val ≤ M := by omega
  have he : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hL := hM.trans (logScale_antitone hx hj)
  calc
    _ ≤ ∑ _k ∈ codeBox (mesh x j.val), p j.val := Finset.sum_le_sum (fun k hk => htail j k hk)
    _ = ((codeBox (mesh x j.val)).card : ℝ)*p j.val := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (codeBox_card_bound (mesh_pos (by linarith : 1 < logScale x j.val))) (hp j.val hj)

end NField.Alignment.HarperGoodEventUnion

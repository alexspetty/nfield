/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperPathMaximum

/-!
# First crossings of a finite partial-sum path

Crossing events use a weak inequality at the crossing and strict
inequalities at all preceding positive times. They are measurable,
pairwise disjoint, and cover every path which reaches the level.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperFirstCrossing
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set HarperPathGrid HarperPathTransfer HarperKilledPath
  HarperGaussianPathSplit HarperPathMaximum

def firstCrossing {n : ℕ} (b : ℝ) (j : Fin n) : Set (Fin n → ℝ) :=
  {z | b ≤ partialSum z j ∧ ∀ i, i < j → partialSum z i < b}

theorem measurableSet_firstCrossing {n : ℕ} (b : ℝ) (j : Fin n) :
    MeasurableSet (firstCrossing b j) := by
  unfold firstCrossing
  apply MeasurableSet.inter
  · exact measurableSet_le measurable_const (partialSum_measurable j)
  · change MeasurableSet {z : Fin n → ℝ | ∀ i, i < j → partialSum z i < b}
    rw [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro i
    by_cases hi : i < j
    · simp only [hi,true_implies]
      exact measurableSet_lt (partialSum_measurable i) measurable_const
    · simp only [hi,false_implies,Set.setOf_true,MeasurableSet.univ]

theorem firstCrossing_disjoint {n : ℕ} (b : ℝ) :
    Pairwise (fun i j : Fin n => Disjoint (firstCrossing b i) (firstCrossing b j)) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro z hi hj
  rcases lt_or_gt_of_ne hij with h | h
  · exact not_lt_of_ge hi.1 (hj.2 i h)
  · exact not_lt_of_ge hj.1 (hi.2 j h)

theorem exists_firstCrossing {n : ℕ} (b : ℝ) (z : Fin n → ℝ)
    (hz : ∃ j, b ≤ partialSum z j) : ∃ j, z ∈ firstCrossing b j := by
  classical
  let s := Finset.univ.filter (fun j : Fin n => b ≤ partialSum z j)
  have hs : s.Nonempty := by
    obtain ⟨j,hj⟩ := hz
    exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩
  obtain ⟨j,hj,hmin⟩ := s.exists_min_image (fun i => i) hs
  refine ⟨j,(Finset.mem_filter.mp hj).2,fun i hi => ?_⟩
  apply lt_of_not_ge
  intro hbi
  have hji := hmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hbi⟩)
  exact not_le_of_gt hi hji

theorem firstCrossing_mass_sum_le_one {n : ℕ} (μ : Measure (Fin n → ℝ))
    [IsProbabilityMeasure μ] (b : ℝ) (s : Finset (Fin n)) :
    (∑ j ∈ s, μ.real (firstCrossing b j)) ≤ 1 := by
  have h := sum_measureReal_le_measureReal_univ (μ := μ) (s := s)
    (fun j _ => measurableSet_firstCrossing b j)
    (fun i _ j _ hij => firstCrossing_disjoint b hij)
  simpa only [probReal_univ] using h

theorem firstCrossing_append_iff {m n : ℕ} (b : ℝ) (j : Fin m)
    (y : Fin m → ℝ) (z : Fin n → ℝ) :
    Fin.append y z ∈ firstCrossing b (Fin.castAdd n j) ↔ y ∈ firstCrossing b j := by
  constructor
  · rintro ⟨hj,hpre⟩
    refine ⟨?_,fun i hi => ?_⟩
    · simpa only [partialSum_append_left] using hj
    · have hi' : Fin.castAdd n i < Fin.castAdd n j := hi
      simpa only [partialSum_append_left] using hpre _ hi'
  · rintro ⟨hj,hpre⟩
    refine ⟨?_,fun i hi => ?_⟩
    · simpa only [partialSum_append_left] using hj
    · induction i using Fin.addCases with
      | left i =>
        have hi' : i < j := hi
        simpa only [partialSum_append_left] using hpre i hi'
      | right i =>
        have hi' : m+i.val < j.val := hi
        omega

theorem crossing_window_suffix_cover {k n : ℕ} (b c : ℝ) :
    (appendEquiv (k+1) n) ⁻¹'
      (maximumWindow b c ∩ firstCrossing b (Fin.castAdd n (Fin.last k))) ⊆
        firstCrossing b (Fin.last k) ×ˢ (survivalEvent c : Set (Fin n → ℝ)) := by
  intro p hp
  have hw : Fin.append p.1 p.2 ∈ maximumWindow b c := hp.1
  have hf : p.1 ∈ firstCrossing b (Fin.last k) :=
    (firstCrossing_append_iff b (Fin.last k) p.1 p.2).mp hp.2
  refine ⟨hf,fun j => ?_⟩
  have hs : b ≤ ∑ i, p.1 i := by simpa only [partialSum_last] using hf.1
  have hu := hw.1 (Fin.natAdd (k+1) j)
  rw [partialSum_append_right] at hu
  linarith

end NField.Alignment.HarperFirstCrossing

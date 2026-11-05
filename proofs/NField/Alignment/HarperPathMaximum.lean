/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperGaussianBarrier

/-!
# Maxima and shifted suffixes of finite partial-sum paths

The maximum is over positive times only, excluding the initial zero.
All path events below use the canonical initial partial sums.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperPathMaximum
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set HarperPathGrid HarperPathTransfer HarperKilledPath
  HarperGaussianPathSplit

def pathMaximum {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) : ℝ :=
  Finset.univ.sup' ⟨⟨0,hn⟩,Finset.mem_univ _⟩ (partialSum z)

def maximumWindow {n : ℕ} (b c : ℝ) : Set (Fin n → ℝ) :=
  {z | (∀ j, partialSum z j ≤ b+c) ∧ ∃ j, b ≤ partialSum z j}

theorem pathMaximum_le_iff {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) (a : ℝ) :
    pathMaximum hn z ≤ a ↔ ∀ j, partialSum z j ≤ a := by
  simp only [pathMaximum,Finset.sup'_le_iff,Finset.mem_univ,forall_const]

theorem le_pathMaximum_iff {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) (a : ℝ) :
    a ≤ pathMaximum hn z ↔ ∃ j, a ≤ partialSum z j := by
  simp only [pathMaximum,Finset.le_sup'_iff,Finset.mem_univ,true_and]

theorem pathMaximum_measurable {n : ℕ} (hn : 0 < n) : Measurable (pathMaximum hn) := by
  have h := Finset.measurable_sup' (s := (Finset.univ : Finset (Fin n)))
    ⟨⟨0,hn⟩,Finset.mem_univ _⟩ (fun j _ => partialSum_measurable j)
  convert h using 1
  funext z
  rw [Finset.sup'_apply]
  rfl

theorem mem_maximumWindow_iff {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) (b c : ℝ) :
    z ∈ maximumWindow b c ↔ pathMaximum hn z ∈ Icc b (b+c) := by
  simp only [maximumWindow,Set.mem_setOf_eq,Set.mem_Icc,pathMaximum_le_iff,le_pathMaximum_iff]
  exact and_comm

theorem measurableSet_maximumWindow {n : ℕ} (b c : ℝ) :
    MeasurableSet (maximumWindow (n := n) b c) := by
  have hu : MeasurableSet {z : Fin n → ℝ | ∀ j, partialSum z j ≤ b+c} :=
    measurableSet_survivalEvent (b+c)
  have hl : MeasurableSet {z : Fin n → ℝ | ∃ j, b ≤ partialSum z j} := by
    rw [Set.setOf_exists]
    exact MeasurableSet.iUnion (fun j => measurableSet_le measurable_const (partialSum_measurable j))
  exact hu.inter hl

theorem partialSum_append_right {m n : ℕ} (y : Fin m → ℝ) (z : Fin n → ℝ) (j : Fin n) :
    partialSum (Fin.append y z) (Fin.natAdd m j) = (∑ i, y i)+partialSum z j := by
  have hm (i : Fin m) : Fin.castAdd n i ≤ Fin.natAdd m j := by
    simp only [Fin.le_def,Fin.val_castAdd,Fin.val_natAdd]
    omega
  simp [partialSum_eq_sum_ite,Fin.sum_univ_add,hm]

theorem late_window_iff {m n : ℕ} (hn : 0 < n) (y : Fin m → ℝ) (z : Fin n → ℝ)
    (b c : ℝ) :
    ((∀ j : Fin n, partialSum (Fin.append y z) (Fin.natAdd m j) ≤ b+c) ∧
      ∃ j : Fin n, b ≤ partialSum (Fin.append y z) (Fin.natAdd m j)) ↔
        (∑ i, y i)+pathMaximum hn z ∈ Icc b (b+c) := by
  simp only [partialSum_append_right,Set.mem_Icc]
  constructor
  · rintro ⟨hu,⟨j,hj⟩⟩
    have hlo : b-(∑ i, y i) ≤ pathMaximum hn z :=
      (le_pathMaximum_iff hn z _).mpr ⟨j,by linarith⟩
    have hhi : pathMaximum hn z ≤ b+c-(∑ i, y i) :=
      (pathMaximum_le_iff hn z _).mpr (fun j => by linarith [hu j])
    exact ⟨by linarith,by linarith⟩
  · rintro ⟨hlo,hhi⟩
    have hu := (pathMaximum_le_iff hn z (b+c-∑ i, y i)).mp (by linarith)
    obtain ⟨j,hj⟩ := (le_pathMaximum_iff hn z (b-∑ i, y i)).mp (by linarith)
    exact ⟨fun j => by linarith [hu j],⟨j,by linarith⟩⟩

end NField.Alignment.HarperPathMaximum

/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperFirstCrossing
import NField.Alignment.HarperGaussianLateMaximum

/-!
# Gaussian survival after the first crossing

A crossing in the prefix leaves an independent suffix whose required
upper barrier is at most the interval width. The actual crossing masses
are preserved by the prefix projection and may be summed without loss.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperGaussianFirstCrossing
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set HarperPathGrid HarperKilledPath
  HarperGaussianPathSplit HarperPathMaximum HarperFirstCrossing HarperGaussianLateMaximum
  HarperGaussianBarrier

def earlyIndices (m n : ℕ) : Finset (Fin (m+n)) :=
  Finset.univ.filter (fun j => j.val < m)

theorem gaussian_firstCrossing_prefix_mass {m n : ℕ} (v : Fin (m+n) → NNReal)
    (b : ℝ) (j : Fin m) :
    (Measure.pi (fun i => gaussianReal 0 (v i))).real (firstCrossing b (Fin.castAdd n j)) =
      (Measure.pi (fun i => gaussianReal 0 (v (Fin.castAdd n i)))).real (firstCrossing b j) := by
  have he : (appendEquiv m n) ⁻¹' firstCrossing b (Fin.castAdd n j) =
      firstCrossing b j ×ˢ (Set.univ : Set (Fin n → ℝ)) := by
    ext p
    change (Fin.append p.1 p.2 ∈ firstCrossing b (Fin.castAdd n j)) ↔ _
    simp only [Set.mem_prod,Set.mem_univ,and_true,firstCrossing_append_iff]
  have hm : (Measure.pi (fun i => gaussianReal 0 (v i))).real (firstCrossing b (Fin.castAdd n j)) =
      ((Measure.pi (fun i => gaussianReal 0 (v (Fin.castAdd n i)))).prod
        (Measure.pi (fun i => gaussianReal 0 (v (Fin.natAdd m i))))).real
        (firstCrossing b j ×ˢ (Set.univ : Set (Fin n → ℝ))) := by
    simp only [measureReal_def]
    rw [← (gaussian_append_measurePreserving v).map_eq,
      Measure.map_apply (appendEquiv m n).measurable (measurableSet_firstCrossing b _),he]
  rw [hm,measureReal_prod_prod,probReal_univ,mul_one]

theorem gaussian_crossing_window_bound {k n : ℕ} (hn : 0 < n)
    (v : Fin ((k+1)+n) → NNReal)
    (hv : ∀ i : Fin n, (1/4 : ℝ) ≤ v (Fin.natAdd (k+1) i) ∧
      (v (Fin.natAdd (k+1) i) : ℝ) ≤ 1) (b : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    (Measure.pi (fun i => gaussianReal 0 (v i))).real
      (maximumWindow b c ∩ firstCrossing b (Fin.castAdd n (Fin.last k))) ≤
        (900*(c+1)/Real.sqrt (n : ℝ)) *
          (Measure.pi (fun i => gaussianReal 0 (v i))).real
            (firstCrossing b (Fin.castAdd n (Fin.last k))) := by
  let μ := Measure.pi (fun i => gaussianReal 0 (v (Fin.castAdd n i)))
  let ν := Measure.pi (fun i => gaussianReal 0 (v (Fin.natAdd (k+1) i)))
  have he : (Measure.pi (fun i => gaussianReal 0 (v i))).real
      (maximumWindow b c ∩ firstCrossing b (Fin.castAdd n (Fin.last k))) =
      (μ.prod ν).real ((appendEquiv (k+1) n) ⁻¹'
        (maximumWindow b c ∩ firstCrossing b (Fin.castAdd n (Fin.last k)))) := by
    simp only [measureReal_def]
    rw [← (gaussian_append_measurePreserving v).map_eq,
      Measure.map_apply (appendEquiv (k+1) n).measurable
        ((measurableSet_maximumWindow b c).inter (measurableSet_firstCrossing b _))]
  rw [he,gaussian_firstCrossing_prefix_mass]
  have hcover := measureReal_mono (μ := μ.prod ν) (crossing_window_suffix_cover (k := k) (n := n) b c)
    (by finiteness)
  rw [measureReal_prod_prod] at hcover
  have hbar := gaussian_constant_barrier_upper hn (fun i => v (Fin.natAdd (k+1) i)) hc hv
  have hmul := mul_le_mul_of_nonneg_left hbar
    (show 0 ≤ μ.real (firstCrossing b (Fin.last k)) from measureReal_nonneg)
  change _ ≤ (900*(c+1)/Real.sqrt (n : ℝ))*μ.real (firstCrossing b (Fin.last k))
  change ν.real (survivalEvent c) ≤ _ at hbar
  change μ.real (firstCrossing b (Fin.last k))*ν.real (survivalEvent c) ≤ _ at hmul
  nlinarith

theorem gaussian_crossing_window_index {N k n : ℕ} (hN : N = (k+1)+n) (hn : 0 < n)
    (v : Fin N → NNReal) (hv : ∀ i, (1/4 : ℝ) ≤ v i ∧ (v i : ℝ) ≤ 1)
    (j : Fin N) (hj : j.val = k) (b : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    (Measure.pi (fun i => gaussianReal 0 (v i))).real (maximumWindow b c ∩ firstCrossing b j) ≤
      (900*(c+1)/Real.sqrt (n : ℝ))*
        (Measure.pi (fun i => gaussianReal 0 (v i))).real (firstCrossing b j) := by
  subst N
  have hj' : j = Fin.castAdd n (Fin.last k) := Fin.ext hj
  subst j
  exact gaussian_crossing_window_bound hn v (fun i => hv _) b hc

theorem maximumWindow_early_late_cover (m n : ℕ) (b c : ℝ) :
    (maximumWindow b c : Set (Fin (m+n) → ℝ)) ⊆
      (⋃ j ∈ earlyIndices m n, maximumWindow b c ∩ firstCrossing b j) ∪
        lateWindow (m := m) (n := n) b c := by
  intro z hz
  obtain ⟨j,hj⟩ := exists_firstCrossing b z hz.2
  by_cases he : j.val < m
  · exact Or.inl (Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩,⟨hz,hj⟩⟩⟩)
  · let t : Fin n := ⟨j.val-m,by omega⟩
    have ht : Fin.natAdd m t = j := Fin.ext (by dsimp [t]; omega)
    refine Or.inr ⟨fun i => hz.1 _,⟨t,?_⟩⟩
    rw [ht]
    exact hj.1

end NField.Alignment.HarperGaussianFirstCrossing

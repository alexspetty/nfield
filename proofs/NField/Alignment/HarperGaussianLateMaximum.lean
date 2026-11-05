/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperGaussianIntervalMass
import NField.Alignment.HarperPathMaximum

/-!
# Interval mass for the late part of a Gaussian walk

The late maximum is the independent prefix endpoint plus the suffix
maximum. Its interval mass is controlled by the Gaussian endpoint density,
without any positive-variance requirement on the suffix itself.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperGaussianLateMaximum
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set HarperPathGrid HarperPathTransfer
  HarperGaussianPathSplit HarperPathMaximum HarperGaussianIntervalMass

def lateWindow {m n : ℕ} (b c : ℝ) : Set (Fin (m+n) → ℝ) :=
  {z | (∀ j : Fin n, partialSum z (Fin.natAdd m j) ≤ b+c) ∧
    ∃ j : Fin n, b ≤ partialSum z (Fin.natAdd m j)}

theorem measurableSet_lateWindow {m n : ℕ} (b c : ℝ) :
    MeasurableSet (lateWindow (m := m) (n := n) b c) := by
  unfold lateWindow
  apply MeasurableSet.inter
  · change MeasurableSet {z : Fin (m+n) → ℝ | ∀ j : Fin n, partialSum z (Fin.natAdd m j) ≤ b+c}
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter (fun j =>
      measurableSet_le (partialSum_measurable (Fin.natAdd m j)) measurable_const)
  · change MeasurableSet {z : Fin (m+n) → ℝ | ∃ j : Fin n, b ≤ partialSum z (Fin.natAdd m j)}
    rw [Set.setOf_exists]
    exact MeasurableSet.iUnion (fun j =>
      measurableSet_le measurable_const (partialSum_measurable (Fin.natAdd m j)))

theorem lateWindow_preimage {m n : ℕ} (hn : 0 < n) (b c : ℝ) :
    (appendEquiv m n) ⁻¹' lateWindow b c =
      {p | b ≤ (∑ i, p.1 i)+pathMaximum hn p.2 ∧
        (∑ i, p.1 i)+pathMaximum hn p.2 ≤ b+c} := by
  ext p
  exact late_window_iff hn p.1 p.2 b c

theorem gaussian_late_maximum_interval {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (v : Fin (m+n) → NNReal) (hv : ∀ i : Fin m, (1/4 : ℝ) ≤ v (Fin.castAdd n i))
    (b : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    (Measure.pi (fun i => gaussianReal 0 (v i))).real (lateWindow (m := m) (n := n) b c) ≤
      2*c/Real.sqrt (m : ℝ) := by
  have he : (Measure.pi (fun i => gaussianReal 0 (v i))).real (lateWindow (m := m) (n := n) b c) =
      ((Measure.pi (fun i => gaussianReal 0 (v (Fin.castAdd n i)))).prod
        (Measure.pi (fun i => gaussianReal 0 (v (Fin.natAdd m i))))).real
        {p | b ≤ (∑ i, p.1 i)+pathMaximum hn p.2 ∧
          (∑ i, p.1 i)+pathMaximum hn p.2 ≤ b+c} := by
    simp only [measureReal_def]
    rw [← (gaussian_append_measurePreserving v).map_eq,
      Measure.map_apply (appendEquiv m n).measurable (measurableSet_lateWindow b c),
      lateWindow_preimage hn]
  rw [he]
  exact gaussian_sum_random_shift_interval _ (pathMaximum hn) (pathMaximum_measurable hn)
    hm (fun i => v (Fin.castAdd n i)) hv b hc

end NField.Alignment.HarperGaussianLateMaximum

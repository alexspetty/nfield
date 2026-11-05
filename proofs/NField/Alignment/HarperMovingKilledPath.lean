/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperGaussianBarrierPerturbation

/-!
# Surviving deficit for an increasing barrier

The barrier is indexed by elapsed time, including time zero. Extending a
surviving path increases its deficit by exactly the barrier increment
before the next Gaussian step is killed at the new boundary.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperMovingKilledPath
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set HarperPathGrid HarperKilledPath
  HarperGaussianOvershoot HarperGaussianBarrierPerturbation

def movingEvent {n : ℕ} (B : ℕ → ℝ) : Set (Fin n → ℝ) :=
  barrierEvent (fun j => B (j.val+1))

def movingPotential {n : ℕ} (B : ℕ → ℝ) (z : Fin n → ℝ) : ℝ :=
  (movingEvent B).indicator (fun y => B n-(∑ i, y i)+2) z

theorem measurableSet_movingEvent {n : ℕ} (B : ℕ → ℝ) :
    MeasurableSet (movingEvent (n := n) B) := measurableSet_barrierEvent _

theorem movingEvent_snoc {n : ℕ} (B : ℕ → ℝ) (y : Fin n → ℝ) (z : ℝ) :
    Fin.snoc y z ∈ movingEvent B ↔ y ∈ movingEvent B ∧ (∑ i, y i)+z ≤ B (n+1) := by
  simp only [movingEvent,barrierEvent,Set.mem_setOf_eq,Fin.forall_iff_castSucc,
    partialSum_last,Fin.sum_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last,
    partialSum_snoc_castSucc,Fin.val_castSucc,Fin.val_last]
  exact and_comm

theorem sum_le_of_moving {n : ℕ} {B : ℕ → ℝ} (hB : 0 ≤ B 0)
    {z : Fin n → ℝ} (hz : z ∈ movingEvent B) : (∑ i, z i) ≤ B n := by
  cases n with
  | zero => simpa using hB
  | succ n => simpa only [partialSum_last,Fin.val_last] using hz (Fin.last n)

theorem movingEvent_subset_constant {n : ℕ} {B : ℕ → ℝ} (hB : Monotone B) :
    movingEvent (n := n) B ⊆ survivalEvent (B n) := by
  intro z hz j
  exact (hz j).trans (hB (by omega : j.val+1 ≤ n))

theorem movingPotential_nonneg {n : ℕ} {B : ℕ → ℝ} (hB : 0 ≤ B 0) (z : Fin n → ℝ) :
    0 ≤ movingPotential B z := by
  unfold movingPotential
  by_cases hz : z ∈ movingEvent B
  · rw [Set.indicator_of_mem hz]
    linarith [sum_le_of_moving hB hz]
  · rw [Set.indicator_of_notMem hz]

theorem movingPotential_snoc {n : ℕ} (B : ℕ → ℝ) (y : Fin n → ℝ) (z : ℝ) :
    movingPotential B (Fin.snoc y z) =
      (movingEvent B).indicator (fun w => killedPotential (B (n+1)-∑ i, w i) z) y := by
  classical
  unfold movingPotential killedPotential
  by_cases hy : y ∈ movingEvent B
  · rw [Set.indicator_of_mem hy]
    by_cases hz : z ≤ B (n+1)-∑ i, y i
    · rw [Set.indicator_of_mem (show z ∈ Iic (B (n+1)-∑ i, y i) from hz),
        Set.indicator_of_mem ((movingEvent_snoc B y z).mpr ⟨hy,by linarith⟩)]
      simp only [Fin.sum_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last]
      ring
    · rw [Set.indicator_of_notMem (show z ∉ Iic (B (n+1)-∑ i, y i) from hz),
        Set.indicator_of_notMem (by rw [movingEvent_snoc]; intro h; apply hz; linarith [h.2])]
  · rw [Set.indicator_of_notMem hy,
      Set.indicator_of_notMem (by rw [movingEvent_snoc]; exact fun h => hy h.1)]

theorem gaussian_movingPotential_integrable {n : ℕ} (B : ℕ → ℝ) (v : Fin n → NNReal) :
    Integrable (movingPotential B) (Measure.pi (fun i => gaussianReal 0 (v i))) := by
  have hs : Integrable (fun z : Fin n → ℝ => ∑ i, z i)
      (Measure.pi (fun i => gaussianReal 0 (v i))) := by
    apply integrable_finsetSum
    intro i _
    exact integrable_comp_eval (μ := fun i => gaussianReal 0 (v i)) (i := i)
      (gaussian_identity_integrable 0 (v i))
  exact (((integrable_const (B n)).sub hs).add (integrable_const 2)).indicator
    (measurableSet_movingEvent B)

end NField.Alignment.HarperMovingKilledPath

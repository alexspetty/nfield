/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperGaussianOvershoot
import Mathlib.MeasureTheory.Integral.Pi

/-!
# The surviving deficit on a finite Gaussian path

The path event uses the same initial partial sums as the source-block
comparison. Appending one increment gives an exact killed-potential
recursion. No probabilistic bound is assumed in these identities.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperKilledPath
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set HarperPathGrid HarperGaussianOvershoot

def survivalEvent {n : ℕ} (c : ℝ) : Set (Fin n → ℝ) :=
  {z | ∀ j, partialSum z j ≤ c}

def pathPotential {n : ℕ} (c : ℝ) (z : Fin n → ℝ) : ℝ :=
  (survivalEvent c).indicator (fun y => c-(∑ i, y i)+2) z

theorem partialSum_eq_sum_ite {n : ℕ} (z : Fin n → ℝ) (j : Fin n) :
    partialSum z j = ∑ i, if i ≤ j then z i else 0 := by
  classical
  have he : Finset.univ.filter (fun i => i ≤ j) = Finset.Iic j := by
    ext i
    simp
  simp only [Finset.sum_ite,Finset.sum_const_zero,add_zero,he,partialSum]

theorem partialSum_last {n : ℕ} (z : Fin (n+1) → ℝ) :
    partialSum z (Fin.last n) = ∑ i, z i := by
  simp [partialSum_eq_sum_ite,Fin.le_last]

theorem partialSum_snoc_castSucc {n : ℕ} (y : Fin n → ℝ) (z : ℝ) (j : Fin n) :
    partialSum (Fin.snoc y z) j.castSucc = partialSum y j := by
  simp [partialSum_eq_sum_ite,Fin.sum_univ_castSucc]

theorem survivalEvent_snoc {n : ℕ} (c : ℝ) (y : Fin n → ℝ) (z : ℝ) :
    Fin.snoc y z ∈ survivalEvent c ↔
      y ∈ survivalEvent c ∧ (∑ i, y i)+z ≤ c := by
  simp only [survivalEvent,Set.mem_setOf_eq,Fin.forall_iff_castSucc,
    partialSum_last,Fin.sum_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last,
    partialSum_snoc_castSucc]
  exact and_comm

theorem measurableSet_survivalEvent {n : ℕ} (c : ℝ) :
    MeasurableSet (survivalEvent (n := n) c) := by
  unfold survivalEvent
  rw [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro j
  have hm : Measurable (fun z : Fin n → ℝ => partialSum z j) := by
    unfold partialSum
    fun_prop
  exact measurableSet_le hm measurable_const

theorem sum_le_of_survival {n : ℕ} {c : ℝ} (hc : 0 ≤ c)
    {z : Fin n → ℝ} (hz : z ∈ survivalEvent c) : (∑ i, z i) ≤ c := by
  cases n with
  | zero => simpa using hc
  | succ n => simpa only [partialSum_last] using hz (Fin.last n)

theorem pathPotential_nonneg {n : ℕ} {c : ℝ} (hc : 0 ≤ c) (z : Fin n → ℝ) :
    0 ≤ pathPotential c z := by
  unfold pathPotential
  by_cases hz : z ∈ survivalEvent c
  · rw [Set.indicator_of_mem hz]
    linarith [sum_le_of_survival hc hz]
  · rw [Set.indicator_of_notMem hz]

theorem pathPotential_snoc {n : ℕ} (c : ℝ) (y : Fin n → ℝ) (z : ℝ) :
    pathPotential c (Fin.snoc y z) =
      (survivalEvent c).indicator (fun w => killedPotential (c-∑ i, w i) z) y := by
  classical
  unfold pathPotential killedPotential
  by_cases hy : y ∈ survivalEvent c
  · rw [Set.indicator_of_mem hy]
    by_cases hz : z ≤ c-∑ i, y i
    · rw [Set.indicator_of_mem (show z ∈ Iic (c-∑ i, y i) from hz),
        Set.indicator_of_mem ((survivalEvent_snoc c y z).mpr ⟨hy,by linarith⟩)]
      simp only [Fin.sum_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last]
      ring
    · rw [Set.indicator_of_notMem (show z ∉ Iic (c-∑ i, y i) from hz),
        Set.indicator_of_notMem (by rw [survivalEvent_snoc]; intro h; apply hz; linarith [h.2])]
  · rw [Set.indicator_of_notMem hy,
      Set.indicator_of_notMem (by rw [survivalEvent_snoc]; exact fun h => hy h.1)]

theorem gaussian_pathPotential_integrable {n : ℕ} (c : ℝ) (v : Fin n → NNReal) :
    Integrable (pathPotential c) (Measure.pi (fun i => gaussianReal 0 (v i))) := by
  have hs : Integrable (fun z : Fin n → ℝ => ∑ i, z i)
      (Measure.pi (fun i => gaussianReal 0 (v i))) := by
    apply integrable_finsetSum
    intro i _
    exact integrable_comp_eval (μ := fun i => gaussianReal 0 (v i)) (i := i)
      (gaussian_identity_integrable 0 (v i))
  exact (((integrable_const c).sub hs).add (integrable_const 2)).indicator
    (measurableSet_survivalEvent c)

end NField.Alignment.HarperKilledPath

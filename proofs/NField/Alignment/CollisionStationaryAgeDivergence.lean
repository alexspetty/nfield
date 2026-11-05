/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionIntegerSingularity
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Almost-everywhere divergence of the uncentered age

The age partial sums are increasing. A subsequence of the centered
potentials converges almost everywhere, whereas the deterministic means
diverge. The entire uncentered sequence therefore tends to infinity.
-/

noncomputable section

namespace NField.Alignment.CollisionStationaryAgeDivergence

open scoped BigOperators
open Filter MeasureTheory
open ProfiniteRemainderMeasure CollisionRemainderDynamics CollisionPotentialHilbert
open CollisionPotentialConvergence CollisionIntegerSingularity

def uncenteredAge (M : ℕ) (x : Phase) : ℝ :=
  (2/3 : ℝ) * ∑ k ∈ Finset.Icc 2 M, collisionWeight k *
    (centered k x + ((k : ℝ)-1)/2)

theorem uncenteredAge_split (M : ℕ) (x : Phase) :
    uncenteredAge M x = potentialMap collisionWeight M x + stationaryAge collisionWeight M := by
  simp only [uncenteredAge, potentialMap, ContinuousMap.smul_apply, ContinuousMap.sum_apply,
    remainderMap, ContinuousMap.coe_mk, smul_eq_mul, stationaryAge]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem uncenteredAge_monotone (x : Phase) : Monotone (fun M => uncenteredAge M x) := by
  intro M N hMN
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2/3)
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl hMN)
  intro k hk _
  have hkpos : 0 < k := by have := (Finset.mem_Icc.mp hk).1; omega
  letI : NeZero k := ⟨hkpos.ne'⟩
  rw [centered_eq, sub_add_cancel]
  exact mul_nonneg (collisionWeight_nonneg k) (Nat.cast_nonneg _)

theorem uncenteredAge_tendsto_atTop_ae :
    ∀ᵐ x ∂phaseHaar, Tendsto (fun M => uncenteredAge M x) atTop atTop := by
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp tendsto_collisionPotential).exists_seq_tendsto_ae
  have he : ∀ᵐ x ∂phaseHaar, ∀ M,
      finitePotential collisionWeight M x = potentialMap collisionWeight M x := by
    apply ae_all_iff.mpr
    intro M
    rw [finitePotential_toLp]
    exact ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) phaseHaar (potentialMap collisionWeight M)
  filter_upwards [hae, he] with x hx hex
  have hc : Tendsto (fun i => potentialMap collisionWeight (ns i) x) atTop (nhds (collisionPotential x)) := by
    simpa only [hex] using hx
  have hd := stationaryAge_tendsto_atTop.comp hns.tendsto_atTop
  have ht : Tendsto (fun i => uncenteredAge (ns i) x) atTop atTop := by
    simp_rw [uncenteredAge_split]
    exact hc.add_atTop hd
  exact tendsto_atTop_of_monotone_of_subseq (uncenteredAge_monotone x) ht

end NField.Alignment.CollisionStationaryAgeDivergence

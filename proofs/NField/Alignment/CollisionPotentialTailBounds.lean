/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionDistributionApproximation
import NField.Alignment.CollisionStationaryAgeAsymptotic

/-!
# Pointwise cutoff bounds and uniform finite tail variance

These are the elementary inputs for the stationary tail theorem. They
retain the exact cutoff height and the common infinite L2 remainder.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionPotentialTailBounds

open scoped BigOperators Classical
open Filter MeasureTheory ProfiniteRemainderMeasure CollisionRemainderDynamics
open CollisionPotentialHilbert CollisionPotentialConvergence CollisionMassReadout
open CollisionDistributionApproximation

theorem centered_abs_bound {k : ℕ} (hk : 0 < k) (x : Phase) :
    |centered k x| ≤ ((k : ℝ)-1)/2 := by
  letI : NeZero k := ⟨hk.ne'⟩
  rw [centered_eq]
  have hv : (((residueHom k x).toAdd.val : ℕ) : ℝ)+1 ≤ (k : ℝ) := by
    exact_mod_cast (show (residueHom k x).toAdd.val+1 ≤ k by
      have := ZMod.val_lt (residueHom k x).toAdd
      omega)
  have hz : (0 : ℝ) ≤ (residueHom k x).toAdd.val := Nat.cast_nonneg _
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem potentialMap_abs_bound (M : ℕ) (x : Phase) :
    |potentialMap collisionWeight M x| ≤ stationaryAge collisionWeight M := by
  simp only [potentialMap,ContinuousMap.smul_apply,ContinuousMap.sum_apply,
    remainderMap,ContinuousMap.coe_mk,smul_eq_mul]
  rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2/3)]
  calc
    _ ≤ (2/3 : ℝ)*(∑ k∈Finset.Icc 2 M, |collisionWeight k*centered k x|) :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
    _ ≤ (2/3 : ℝ)*(∑ k∈Finset.Icc 2 M, collisionWeight k*(((k : ℝ)-1)/2)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro k hk
      rw [abs_mul,abs_of_nonneg (collisionWeight_nonneg k)]
      exact mul_le_mul_of_nonneg_left (centered_abs_bound (by
        have := (Finset.mem_Icc.mp hk).1
        omega) x) (collisionWeight_nonneg k)
    _ = _ := by
      unfold stationaryAge
      rw [Finset.mul_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring

theorem stationaryAge_nonneg (M : ℕ) : 0 ≤ stationaryAge collisionWeight M :=
  (abs_nonneg (potentialMap collisionWeight M (1 : Phase))).trans (potentialMap_abs_bound M 1)

theorem stationaryAge_monotone : Monotone (stationaryAge collisionWeight) := by
  intro M N hMN
  unfold stationaryAge
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.Icc_subset_Icc_right hMN
  · intro k hk _
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
    exact mul_nonneg (collisionWeight_nonneg k) (by linarith)

theorem positive_gram_tail_norm_monotone {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (v : ℕ → E) (hv : ∀ i j, 0 ≤ inner ℝ (v i) (v j))
    {L M N : ℕ} (hLM : L ≤ M) (hMN : M ≤ N) :
    ‖(∑ i∈Finset.range M, v i)-(∑ i∈Finset.range L, v i)‖ ≤
      ‖(∑ i∈Finset.range N, v i)-(∑ i∈Finset.range L, v i)‖ := by
  have he (k : ℕ) (hLk : L ≤ k) :
      (∑ i∈Finset.range k, v i)-(∑ i∈Finset.range L, v i)=
        ∑ i∈Finset.range (k-L), v (L+i) := by
    rw [← Finset.sum_Ico_eq_sum_range]
    rw [← Finset.sum_range_add_sum_Ico v hLk]
    simp
  rw [he M hLM,he N (hLM.trans hMN)]
  have hs := positive_gram_norm_monotone (fun i => v (L+i))
    (fun i j => hv (L+i) (L+j)) (Nat.sub_le_sub_right hMN L)
  dsimp only at hs
  nlinarith [norm_nonneg (∑ i∈Finset.range (M-L), v (L+i)),
    norm_nonneg (∑ i∈Finset.range (N-L), v (L+i))]

theorem finite_cutoff_tail_norm_monotone {L M N : ℕ} (hLM : L ≤ M) (hMN : M ≤ N) :
    ‖finitePotential collisionWeight M-finitePotential collisionWeight L‖ ≤
      ‖finitePotential collisionWeight N-finitePotential collisionWeight L‖ := by
  rw [← collisionVector_partial_sum,← collisionVector_partial_sum,← collisionVector_partial_sum]
  exact positive_gram_tail_norm_monotone collisionVector collisionVector_gram_nonneg
    (by omega) (by omega)

theorem finite_cutoff_tail_norm_le_infinite {L M : ℕ} (hLM : L ≤ M) :
    ‖finitePotential collisionWeight M-finitePotential collisionWeight L‖ ≤
      ‖collisionPotential-finitePotential collisionWeight L‖ := by
  have hlim := (tendsto_collisionPotential.sub
    (tendsto_const_nhds (x := finitePotential collisionWeight L))).norm
  apply ge_of_tendsto hlim
  filter_upwards [eventually_ge_atTop M] with N hMN
  exact finite_cutoff_tail_norm_monotone hLM hMN

end NField.Alignment.CollisionPotentialTailBounds

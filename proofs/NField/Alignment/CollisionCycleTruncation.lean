/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionCycleStationarity

/-!
# Computable bounds for the complete cycle total variation

The finite cutoff does not renormalize retained cycle mass. The missing
contribution is nonnegative and at most the omitted part of unit mass.
Cesaro observations retain the convention `0..N`, with denominator `N+1`.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionCycleTruncation

open scoped BigOperators
open CollisionRemainderDynamics CollisionMassReadout CollisionCycleStationarity

def retainedCycleMass (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (M + 1), collisionWeight k

def truncatedTotalVariation (N M : ℕ) : ℝ :=
  (1 / 2 : ℝ) * ∑ k ∈ Finset.range (M + 1), cycleVariation N k

theorem cycleVariation_summable (N : ℕ) : Summable (cycleVariation N) :=
  Summable.of_nonneg_of_le (cycleVariation_nonneg N) (cycleVariation_le N)
    (collisionWeight_summable.mul_left 2)

theorem truncatedTotalVariation_le (N M : ℕ) :
    truncatedTotalVariation N M ≤ totalVariation N := by
  exact mul_le_mul_of_nonneg_left
    ((cycleVariation_summable N).sum_le_tsum (Finset.range (M + 1))
      (fun k _ => cycleVariation_nonneg N k)) (by norm_num)

theorem totalVariation_le_truncated_add_omitted (N M : ℕ) :
    totalVariation N ≤ truncatedTotalVariation N M + (1 - retainedCycleMass M) := by
  have hs := (collisionWeight_summable.mul_left 2).sub (cycleVariation_summable N)
  have hb := hs.sum_le_tsum (Finset.range (M + 1))
    (fun k _ => sub_nonneg.mpr (cycleVariation_le N k))
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
    (collisionWeight_summable.mul_left 2).tsum_sub (cycleVariation_summable N),
    tsum_mul_left, collisionWeight_tsum] at hb
  unfold totalVariation truncatedTotalVariation retainedCycleMass
  linarith

theorem totalVariation_exact_cutoff_enclosure (N M : ℕ) :
    truncatedTotalVariation N M ≤ totalVariation N ∧
    totalVariation N ≤ truncatedTotalVariation N M + (1 - retainedCycleMass M) :=
  ⟨truncatedTotalVariation_le N M, totalVariation_le_truncated_add_omitted N M⟩

end NField.Alignment.CollisionCycleTruncation

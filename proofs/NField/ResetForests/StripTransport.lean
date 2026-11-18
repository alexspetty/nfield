/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.BranchTransport
import Mathlib.Algebra.BigOperators.Intervals
/-! # The complete strip sum with every accumulated length weight -/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.BranchTransport

open scoped BigOperators

theorem weighted_strip_identity {L U : ℕ} (hL : 2 ≤ L) (hLU : L ≤ U) (q : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc L U, q k) =
      ((U - L + 1 : ℕ) : ℝ) * q L +
      ∑ k ∈ Finset.Icc L (U - 1), ((U - k : ℕ) : ℝ) * (q (k + 1) - q k) := by
  have htel := Finset.sum_Icc_sub hLU (fun i => ((U : ℝ) + 1 - (i : ℝ)) * q i)
  have hpoint (i : ℕ) :
      (((U : ℝ) + 1 - ((i + 1 : ℕ) : ℝ)) * q (i + 1) -
        ((U : ℝ) + 1 - (i : ℝ)) * q i) =
      ((U : ℝ) - (i : ℝ)) * (q (i + 1) - q i) - q i := by
    push_cast
    ring
  simp_rw [hpoint] at htel
  rw [Finset.sum_sub_distrib] at htel
  simp only [Nat.cast_add, Nat.cast_one, sub_self, zero_mul, zero_sub] at htel
  have hU : U - 1 + 1 = U := by omega
  have hsplit := Finset.sum_Icc_succ_top (f := fun i => ((U : ℝ) - (i : ℝ)) * (q (i + 1) - q i))
    (by omega : L ≤ U - 1 + 1)
  rw [hU] at hsplit
  simp only [sub_self, zero_mul, add_zero] at hsplit
  have hweights : (∑ k ∈ Finset.Icc L (U - 1), ((U - k : ℕ) : ℝ) * (q (k + 1) - q k)) =
      ∑ k ∈ Finset.Icc L (U - 1), ((U : ℝ) - (k : ℝ)) * (q (k + 1) - q k) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hku := (Finset.mem_Icc.mp hk).2
    rw [Nat.cast_sub (by omega : k ≤ U)]
  rw [hweights, Nat.cast_add, Nat.cast_sub hLU, Nat.cast_one]
  linarith

theorem actual_clock_strip_identity (p : ℕ) {L U : ℕ} (hL : 2 ≤ L) (hLU : L ≤ U) :
    (∑ k ∈ Finset.Icc L U, 4 * Core.clockReading (p - 1) (p ^ 2) k) =
      ((U - L + 1 : ℕ) : ℝ) * (4 * Core.clockReading (p - 1) (p ^ 2) L) +
      ∑ k ∈ Finset.Icc L (U - 1), ((U - k : ℕ) : ℝ) *
        (4 * Core.clockReading (p - 1) (p ^ 2) (k + 1) - 4 * Core.clockReading (p - 1) (p ^ 2) k) :=
  weighted_strip_identity hL hLU _

end NField.ResetForests.BranchTransport

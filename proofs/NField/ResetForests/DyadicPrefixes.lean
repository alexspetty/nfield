/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.PacketPrefixes
/-! # A fixed dyadic packet-count partition independent of detector readings -/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.PrefixGeometry

def dyadicCuts (K r : ℕ) : ℕ := if r = 0 then 0 else min K (2 ^ (r - 1))

theorem dyadic_cuts_zero (K : ℕ) : dyadicCuts K 0 = 0 := by
  simp [dyadicCuts]

theorem dyadic_cuts_monotone (K : ℕ) : Monotone (dyadicCuts K) := by
  intro a b hab
  by_cases ha : a = 0
  · rw [ha, dyadic_cuts_zero]
    exact Nat.zero_le _
  · have hb : b ≠ 0 := by omega
    simp only [dyadicCuts, if_neg ha, if_neg hb]
    exact min_le_min_left K (Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_right hab 1))

theorem count_le_dyadic_power (K : ℕ) : K ≤ 2 ^ K := by
  induction K with
  | zero => norm_num
  | succ K ih =>
    rw [pow_succ]
    have hp : 0 < 2 ^ K := pow_pos (by decide) _
    omega

theorem dyadic_cuts_final (K : ℕ) : dyadicCuts K (K + 1) = K := by
  simp only [dyadicCuts, Nat.succ_ne_zero, if_false,
    Nat.add_sub_cancel, min_eq_left (count_le_dyadic_power K)]

theorem actual_dyadic_prefix_partition (p : ℕ) (loads : Finset ℕ) :
    let K := (orderedPackets p loads).length
    let J := physicalPrefixes p loads (dyadicCuts K)
    Monotone J ∧ J 0 = ∅ ∧ J (K + 1) = Finset.univ := by
  dsimp only
  exact ⟨physical_prefix_monotone _ _ _ (dyadic_cuts_monotone _),
    physical_prefix_zero _ _ _ (dyadic_cuts_zero _),
    physical_prefix_final _ _ _ _ (dyadic_cuts_final _)⟩

end NField.ResetForests.PrefixGeometry

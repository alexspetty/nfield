/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.ActualSignedLoss
import NField.ResetForests.CostPopulations
/-! # The exact coarsening identity on all three printed load-one chains -/

set_option autoImplicit false
noncomputable section

namespace NField.ResetForests.ExactCost

open scoped BigOperators Matrix
open RecordGeometry PrefixGeometry

def actualLoadOneSignedLoss (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) (L : ℕ) : Prop :=
  let G := SourceMetrics.sampledGram (p - 1) (p ^ 2)
  let hG := (SourceMetrics.both_prime_square_grams_posDef hp hodd).2
  let A := physicalRecord p {1}
  let b := physicalReadoutWeights p {1}
  let J := physicalPrefixes p {1} (dyadicCuts (orderedPackets p {1}).length)
  let c : Fin (p - 1) → ℝ := fun _ => 1
  let v := prefixIncrement G hG A J c
  let e := fun r => sourceWork G (v r) (v r)
  let d := fun r => finalReadout A b (v r)
  let S := (Finset.range L).filter (fun r => 0 < e r)
  (∑ r ∈ Finset.range L, e r) * prefixCost G hG A b J c L - (finalReadout A b c)^2 =
    ∑ r ∈ S, ∑ s ∈ S.filter (fun s => r < s),
      e r * e s * (d r / e r - d s / e s)^2

theorem actual_load_one_signed_loss {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (L : ℕ)
    (hL : dyadicCuts (orderedPackets p {1}).length L = (orderedPackets p {1}).length) :
    actualLoadOneSignedLoss p hp hodd L := by
  apply source_prefix_signed_loss
  · exact physical_prefix_zero _ _ _ (dyadic_cuts_zero _)
  · exact physical_prefix_final _ _ _ _ hL

theorem cost43_signed_loss : actualLoadOneSignedLoss 43 cost43_prime (by decide) 2 := by
  apply actual_load_one_signed_loss
  rw [cost43_ordered]
  decide

theorem cost61_signed_loss : actualLoadOneSignedLoss 61 cost61_prime (by decide) 4 := by
  apply actual_load_one_signed_loss
  rw [cost61_ordered]
  decide

theorem cost73_signed_loss : actualLoadOneSignedLoss 73 cost73_prime (by decide) 4 := by
  apply actual_load_one_signed_loss
  rw [cost73_ordered]
  decide

end NField.ResetForests.ExactCost

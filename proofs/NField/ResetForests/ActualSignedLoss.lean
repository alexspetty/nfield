/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.ExactPrefixWitness
/-! # Signed coarsening for the actual source increments, including zero work -/

set_option autoImplicit false
noncomputable section

namespace NField.ResetForests.ExactCost

open scoped BigOperators Matrix
open RecordGeometry PrefixGeometry

theorem source_prefix_signed_loss {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (b : ι → ℝ) (J : ℕ → Finset ι)
    (h0 : J 0 = ∅) (c : Fin N → ℝ) (L : ℕ) (hL : J L = Finset.univ) :
    let v := prefixIncrement G hG A J c
    let e := fun r => sourceWork G (v r) (v r)
    let d := fun r => finalReadout A b (v r)
    let S := (Finset.range L).filter (fun r => 0 < e r)
    (∑ r ∈ Finset.range L, e r) * prefixCost G hG A b J c L - (finalReadout A b c)^2 =
      ∑ r ∈ S, ∑ s ∈ S.filter (fun s => r < s),
        e r * e s * (d r / e r - d s / e s)^2 := by
  dsimp only
  let e := fun r => sourceWork G (prefixIncrement G hG A J c r) (prefixIncrement G hG A J c r)
  let d := fun r => finalReadout A b (prefixIncrement G hG A J c r)
  let S := (Finset.range L).filter (fun r => 0 < e r)
  have hz (r : ℕ) (hr : r ∈ Finset.range L) (hn : r ∉ S) : e r = 0 := by
    have hnp : ¬0 < e r := fun h => hn (Finset.mem_filter.mpr ⟨hr,h⟩)
    exact le_antisymm (le_of_not_gt hnp) (source_work_nonnegative G hG _)
  have he : (∑ r ∈ S, e r) = ∑ r ∈ Finset.range L, e r :=
    Finset.sum_subset (Finset.filter_subset _ _) hz
  have hd : (∑ r ∈ S, d r) = finalReadout A b c := by
    rw [prefix_readout_sum G hG A b J h0 c L hL]
    exact Finset.sum_subset (Finset.filter_subset _ _)
      (fun r hr hn => (zero_increment_readout G hG A b J c r (hz r hr hn)).2)
  have hR : Core.readoutCost S e d = prefixCost G hG A b J c L :=
    (prefix_cost_positive_terms G hG A b J c L).symm
  have h := Core.signed_cost_loss S e d (fun r hr => (Finset.mem_filter.mp hr).2)
  rw [he, hd, hR] at h
  exact h

end NField.ResetForests.ExactCost

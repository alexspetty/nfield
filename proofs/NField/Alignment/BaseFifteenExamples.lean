/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.BaseFifteenActualEnergy

/-! # Exact finite base-fifteen ledgers and endpoints -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.BaseFifteenExamples
open CarryBoundarySpectra
open scoped BigOperators

def baseFifteenUnits : Finset ℕ := {1, 2, 4, 7, 8, 11, 13, 14}

theorem base_fifteen_units :
    (Finset.range 15).filter (fun c => c.Coprime 15) = baseFifteenUnits := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_fifteen_unit_boundary : ∀ x : Fin 225, x.val.Coprime 225 →
    baseFifteenBoundaryWeight x =
      ∑ c ∈ baseFifteenUnits,
        ((if x.val = 16 * c - 15 then 1 else 0) -
          (if x.val = 16 * c then 1 else 0) : ℤ) := by decide

theorem base_fifteen_reflection {c : ℕ} (hc : c ∈ baseFifteenUnits) :
    16 * (15 - c) - 15 = 225 - 16 * c := by
  have : c ∈ ({1, 2, 4, 7, 8, 11, 13, 14} : Finset ℕ) := hc
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_fifteen_diagonal_ledger :
    baseFifteenDiagonalLedger 1 = 0 ∧
    baseFifteenDiagonalLedger 3 = 0 ∧
    baseFifteenDiagonalLedger 5 = 0 ∧
    baseFifteenDiagonalLedger 9 = 4 ∧
    baseFifteenDiagonalLedger 15 = 0 ∧
    baseFifteenDiagonalLedger 25 = 12 ∧
    baseFifteenDiagonalLedger 45 = 16 ∧
    baseFifteenDiagonalLedger 75 = 16 ∧
    baseFifteenDiagonalLedger 225 = 16 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_fifteen_antipodal_ledger :
    ∀ e ∈ ({1, 3, 5, 9, 15, 25, 45, 75, 225} : Finset ℕ),
      baseFifteenAntipodalLedger e = -baseFifteenDiagonalLedger e := by decide

set_option maxRecDepth 100000 in
theorem base_fifteen_pushdown_nine :
    baseFifteenPushdown 9 1 = -1 ∧ baseFifteenPushdown 9 2 = 0 ∧
    baseFifteenPushdown 9 4 = 1 ∧ baseFifteenPushdown 9 5 = -1 ∧
    baseFifteenPushdown 9 7 = 0 ∧ baseFifteenPushdown 9 8 = 1 := by decide

theorem base_fifteen_endpoint_reductions :
    (([1, 2, 4, 7, 8, 11, 13, 14] : Multiset ℕ).map (fun c => 16 * c % 9)) =
      {1, 1, 2, 4, 5, 5, 7, 8} ∧
    (([1, 2, 4, 7, 8, 11, 13, 14] : Multiset ℕ).map (fun c => (16 * c - 15) % 9)) =
      {1, 2, 4, 4, 5, 7, 8, 8} := by decide

theorem base_fifteen_endpoint_inverse :
    ∀ e ∈ ({25, 45, 75, 225} : Finset ℕ), Int.ModEq e ((16 : ℤ) * (-14)) 1 := by decide

end NField.Alignment.BaseFifteenExamples

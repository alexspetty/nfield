/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.BaseFifteenExamples

/-! # The endpoint coincidences used to derive the base-fifteen ledger -/

set_option autoImplicit false
namespace NField.Alignment.BaseFifteenEndpointDetails
open BaseFifteenExamples

theorem endpoint_inverse_every_divisor {e : ℕ} (he : e ∣ 225) :
    Int.ModEq e ((16 : ℤ) * (-14)) 1 := by
  rw [Int.modEq_iff_dvd]
  norm_num
  exact_mod_cast he

theorem cross_sign_congruences :
    (∀ c ∈ baseFifteenUnits, ∀ c' ∈ baseFifteenUnits,
      Nat.ModEq 25 (16 * c) (16 * c' - 15) ↔ Int.ModEq 25 ((c : ℤ) - c') 10) ∧
    (∀ e ∈ ({45, 75, 225} : Finset ℕ),
      ∀ c ∈ baseFifteenUnits, ∀ c' ∈ baseFifteenUnits,
        Nat.ModEq e (16 * c) (16 * c' - 15) ↔ Int.ModEq e ((c : ℤ) - c') (-15)) := by
  decide

theorem endpoint_coincidences :
    (∀ c ∈ baseFifteenUnits, ∀ c' ∈ baseFifteenUnits,
      Nat.ModEq 25 (16 * c) (16 * c' - 15) ↔
        (c = 11 ∧ c' = 1) ∨ (c = 14 ∧ c' = 4)) ∧
    (∀ e ∈ ({45, 75, 225} : Finset ℕ),
      ∀ c ∈ baseFifteenUnits, ∀ c' ∈ baseFifteenUnits,
        ¬Nat.ModEq e (16 * c) (16 * c' - 15)) := by decide

theorem same_sign_endpoints_distinct :
    ∀ e ∈ ({25, 45, 75, 225} : Finset ℕ),
      ∀ c ∈ baseFifteenUnits, ∀ c' ∈ baseFifteenUnits,
        (Nat.ModEq e (16 * c) (16 * c') ↔ c = c') ∧
        (Nat.ModEq e (16 * c - 15) (16 * c' - 15) ↔ c = c') := by decide

end NField.Alignment.BaseFifteenEndpointDetails

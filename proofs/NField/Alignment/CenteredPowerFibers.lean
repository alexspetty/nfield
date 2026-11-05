/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.GeneralNeutrality

/-! # Exact power-modulus fiber sizes and the printed centering denominator -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.CenteredPowerFibers
open scoped BigOperators
open CollisionCharacterStructure CenteredCollisionSum NeutralityTheorem GeneralNeutrality

theorem totient_power_succ (b k : ℕ) (hb : 0 < b) :
    (b ^ (k + 1)).totient = b ^ k * b.totient := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := Nat.totient_gcd_mul_totient_mul b (b ^ (k + 1))
    rw [Nat.gcd_eq_left (dvd_pow_self b (by omega : k + 1 ≠ 0)), ← pow_succ', ih] at h
    apply Nat.eq_of_mul_eq_mul_left (Nat.totient_pos.mpr hb)
    calc
      _ = b.totient * (b ^ k * b.totient) * b := h
      _ = _ := by rw [pow_succ]; ring

theorem coarseUnitReduction_fiber_card (b ell : ℕ) [NeZero b]
    [NeZero (allLagModulus b ell)] (u : UnitClass b) :
    Fintype.card (Fiber (coarseUnitReduction b ell) u) = b ^ ell := by
  have hd : b ∣ allLagModulus b ell := dvd_pow_self b (by omega : ell + 1 ≠ 0)
  change Fintype.card (Fiber (unitReduction hd) u) = _
  rw [unitReduction_fiber_card, allLagModulus, totient_power_succ b ell (NeZero.pos b),
    Nat.mul_div_cancel _ (Nat.totient_pos.mpr (NeZero.pos b))]

theorem coarse_fiberMean (b ell : ℕ) [NeZero b] [NeZero (allLagModulus b ell)]
    (T : UnitClass (allLagModulus b ell) → ℂ) (u : UnitClass b) :
    fiberMean (coarseUnitReduction b ell) T u =
      (b ^ ell : ℂ)⁻¹ * ∑ a : Fiber (coarseUnitReduction b ell) u, T a := by
  rw [fiberMean, coarseUnitReduction_fiber_card, Nat.cast_pow]

end NField.Alignment.CenteredPowerFibers

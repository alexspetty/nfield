/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionPrimeLimits

/-! # The actual reduced-remainder signal and its prime harmonic drift -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000

namespace NField.Alignment.CollisionPrimeLimits

open Filter Finset
open scoped BigOperators Topology
open NField.Alignment.PrimePeriodicLimits
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionFluctuationSum

def remainderClassSignal (b : ℕ) [NeZero b] (u : UnitClass b) : ℂ :=
  ((u.val.val : ℂ) - 1) / b

theorem remainderClassSignal_mean {b : ℕ} [NeZero b] (hb : 2 ≤ b) :
    (b.totient : ℂ)⁻¹ * ∑ u : UnitClass b, remainderClassSignal b u =
      1 / 2 - 1 / (b : ℂ) := by
  letI : Fact (1 < b) := ⟨by omega⟩
  let e : UnitClass b ≃ UnitClass b :=
    { toFun := fun u => -u, invFun := fun u => -u,
      left_inv := by intro u; simp, right_inv := by intro u; simp }
  have hpair (u : UnitClass b) :
      (u.val.val : ℚ) + ((e u).val.val : ℚ) = (b : ℚ) := by
    change (u.val.val : ℚ) + ((-u.val).val : ℚ) = (b : ℚ)
    rw [ZMod.neg_val, if_neg (Units.ne_zero u), Nat.cast_sub (Nat.le_of_lt u.val.val_lt)]
    ring
  have h := remainder_mean_of_complement e (fun u : UnitClass b => (u.val.val : ℚ))
    (b : ℚ) (by exact_mod_cast NeZero.ne b) hpair
  rw [ZMod.card_units_eq_totient] at h
  have hc := congrArg (fun z : ℚ => (z : ℂ)) h
  simpa only [Rat.cast_mul, Rat.cast_inv, Rat.cast_natCast, Rat.cast_sum,
    Rat.cast_div, Rat.cast_sub, Rat.cast_one, Rat.cast_ofNat, remainderClassSignal] using hc

theorem remainder_prime_reciprocal_drift {b : ℕ} [NeZero b] (hb : 2 ≤ b) :
    ∃ L : ℂ, Tendsto (fun x : ℝ => weightedPrimeReciprocalSum (remainderClassSignal b) x -
      (1 / 2 - 1 / (b : ℂ)) * (Real.log (Real.log x) : ℂ)) atTop (𝓝 L) := by
  obtain ⟨L, hL⟩ := periodic_prime_reciprocal_residual_limit (remainderClassSignal b)
  exact ⟨L, by simpa only [remainderClassSignal_mean hb] using hL⟩

theorem unitExtension_remainder_eq {b n : ℕ} [NeZero b]
    (hunit : IsUnit (n : ZMod b)) :
    unitExtension (remainderClassSignal b) n = ((n % b : ℕ) - 1 : ℂ) / b := by
  simp only [unitExtension, dif_pos hunit, remainderClassSignal,
    hunit.unit_spec, ZMod.val_natCast]

end NField.Alignment.CollisionPrimeLimits

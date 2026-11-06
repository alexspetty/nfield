/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.UnitFiberMeans

/-! # The four limiting decimal prime means in the fluctuation manuscript -/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionPrimeLimits

open Filter
open scoped BigOperators Topology
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.UnitFiberMeans

local instance : NeZero (allLagModulus 10 1) := ⟨by norm_num [allLagModulus]⟩

def decimalConstructiveTarget (r : ℕ) : ℝ :=
  if r = 1 then -17 / 10 else if r = 3 then -11 / 10 else
    if r = 7 then -7 / 10 else -1 / 10

theorem decimal_unit_values (u : UnitClass 10) :
    u.val.val = 1 ∨ u.val.val = 3 ∨ u.val.val = 7 ∨ u.val.val = 9 := by
  have hcop : u.val.val.Coprime 10 := by
    apply (ZMod.isUnit_iff_coprime _ _).mp
    rw [ZMod.natCast_zmod_val]
    exact u.isUnit
  have hcheck : ∀ r ∈ Finset.range 10, r.Coprime 10 →
      r = 1 ∨ r = 3 ∨ r = 7 ∨ r = 9 := by decide +kernel
  exact hcheck _ (Finset.mem_range.mpr u.val.val_lt) hcop

/-- Title: `The four decimal constructive means are exact rational targets`. -/
theorem decimal_coarse_constructive_means (u : UnitClass 10) :
    coarseConstructiveMean (ell := 1) u = decimalConstructiveTarget u.val.val := by
  rcases decimal_lag_one_column_totals with ⟨_, hs1, _, hs3, _, hs7, _, hs9⟩
  rw [coarseConstructiveMean, real_fiber_mean_eq_table (by decide : 2 ≤ 10)]
  rcases decimal_unit_values u with h | h | h | h <;>
    norm_num [h, hs1, hs3, hs7, hs9, decimalConstructiveTarget]

/-- Title: `Actual decimal prime class averages converge to the four printed means`. -/
theorem decimal_class_prime_mean_limits (u : UnitClass 10) :
    Tendsto (fun x : ℝ =>
      realPrimeTailSum (fun p => if (p : ZMod 10) = u then
        lagOneConstructiveFluctuation 10 p else 0) 11 x /
          coarsePrimeCount u 11 x) atTop (𝓝 (decimalConstructiveTarget u.val.val)) := by
  have h := constructive_class_prime_mean_limit (ell := 1) (by decide : 2 ≤ 10)
    (by decide : 1 ≤ 1) u 11 (by decide)
  simpa only [constructiveFluctuation_lag_one, decimal_coarse_constructive_means] using h

/-- Title: `All four limiting decimal prime class means are strictly negative`. -/
theorem decimal_limiting_means_negative (u : UnitClass 10) :
    decimalConstructiveTarget u.val.val < 0 := by
  unfold decimalConstructiveTarget
  split_ifs <;> norm_num

end NField.Alignment.CollisionPrimeLimits

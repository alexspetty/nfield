/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimePowerGcdDescent

/-!
# Complete prime-power bounds with the actual gcd factor

Induction removes a common prime factor only when both phase parameters
are nonunits. Canonical representatives give the exact gcd recurrence.
Zero parameters are included, as required for later CRT assembly.
-/

set_option autoImplicit false
namespace NField.Alignment.PrimePowerGcdBound
open scoped BigOperators Classical
open SquareZeroUnitShift UnitSumStationaryPhase InverseAdditiveCompletion
  PrimitivePrimePowerBound PrimePowerGcdDescent KloostermanPrimePowerStationary

/-- Keep the odd-prime constant two and the single exceptional constant at two. -/
def localConstant (p : ℕ) : ℝ := if p=2 then 8 else 2

/-- The local constant is always at least one. -/
theorem one_le_localConstant (p : ℕ) : 1≤localConstant p := by
  unfold localConstant
  split_ifs <;> norm_num

/-- The triangle inequality bounds any actual unit sum by the full modulus. -/
theorem norm_unitSum_le_modulus (q : ℕ) [NeZero q] (a b : ZMod q) :
    ‖unitSum ZMod.stdAddChar a b‖≤(q:ℝ) := by
  unfold unitSum
  calc
    _ ≤ ∑ u : (ZMod q)ˣ, ‖ZMod.stdAddChar (phase a b u)‖ := norm_sum_le _ _
    _ = (q.totient:ℝ) := by simp [AddChar.norm_apply,ZMod.card_units_eq_totient]
    _ ≤ _ := by exact_mod_cast Nat.totient_le q

/-- A zero inverse-phase parameter satisfies the same gcd-shaped bound. -/
theorem zero_right_gcd_bound (q : ℕ) [NeZero q] (C : ℝ) (hC : 1≤C) (a : ZMod q) :
    ‖unitSum ZMod.stdAddChar a 0‖≤C*Real.sqrt (q:ℝ)*Real.sqrt (Nat.gcd (0:ZMod q).val q:ℝ) := by
  rw [ZMod.val_zero,Nat.gcd_zero_left]
  have hs := Real.mul_self_sqrt (Nat.cast_nonneg q)
  have he : C*Real.sqrt (q:ℝ)*Real.sqrt q=C*q := by rw [mul_assoc,hs]
  rw [he]
  exact (norm_unitSum_le_modulus q a 0).trans (by nlinarith [Nat.cast_nonneg (α := ℝ) q])

/-- The full local gcd estimate for all phase parameters and every exponent. -/
theorem prime_power_unitSum_gcd_bound (p : ℕ) [Fact p.Prime] (k : ℕ)
    (a b : ZMod (p^k)) :
    ‖unitSum ZMod.stdAddChar a b‖≤
      localConstant p*Real.sqrt ((p^k:ℕ):ℝ)*Real.sqrt (Nat.gcd b.val (p^k):ℝ) := by
  induction k with
  | zero =>
      haveI : Subsingleton (ZMod (p^0)) := by rw [pow_zero]; infer_instance
      have hb : b=0 := Subsingleton.elim _ _
      subst b
      exact zero_right_gcd_bound (p^0) (localConstant p) (one_le_localConstant p) a
  | succ k ih =>
      by_cases hb0 : b=0
      · subst b
        exact zero_right_gcd_bound (p^(k+1)) (localConstant p) (one_le_localConstant p) a
      by_cases hab : IsUnit a ∨ IsUnit b
      · have hb := prime_power_unitSum_bound p (k+1) (by omega) a b hab
        change ‖unitSum ZMod.stdAddChar a b‖≤localConstant p*Real.sqrt ((p^(k+1):ℕ):ℝ) at hb
        have hg : 1≤Real.sqrt (Nat.gcd b.val (p^(k+1)):ℝ) := by
          apply Real.one_le_sqrt.mpr
          exact_mod_cast Nat.gcd_pos_of_pos_right b.val (pow_pos (Fact.out : p.Prime).pos (k+1))
        have hc : 0≤localConstant p*Real.sqrt ((p^(k+1):ℕ):ℝ) :=
          mul_nonneg (le_trans (by norm_num) (one_le_localConstant p)) (Real.sqrt_nonneg _)
        exact hb.trans (by nlinarith [mul_le_mul_of_nonneg_left hg hc])
      · have ha : p∣a.val := prime_dvd_val_of_nonunit p (k+1) (by omega) a
          (fun h => hab (Or.inl h))
        have hb : p∣b.val := prime_dvd_val_of_nonunit p (k+1) (by omega) b
          (fun h => hab (Or.inr h))
        have hk := positive_lower_exponent p k b hb0 hb
        rw [norm_prime_descent p k hk a b ha hb,gcd_quotient p k b hb]
        have hi := ih (a.val/p:ZMod (p^k)) (b.val/p:ZMod (p^k))
        calc
          _ ≤ (p:ℝ)*(localConstant p*Real.sqrt ((p^k:ℕ):ℝ)*
              Real.sqrt (Nat.gcd (b.val/p:ZMod (p^k)).val (p^k):ℝ)) :=
            mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg p)
          _ = localConstant p*((p:ℝ)*(Real.sqrt ((p^k:ℕ):ℝ)*
              Real.sqrt (Nat.gcd (b.val/p:ZMod (p^k)).val (p^k):ℝ))) := by ring
          _ = _ := by rw [sqrt_gcd_descent_factor,mul_assoc]

/-- Multiplying by an actual unit preserves the gcd of the canonical representative. -/
theorem gcd_val_mul_unit (q : ℕ) [NeZero q] (x y : ZMod q) (hy : IsUnit y) :
    Nat.gcd (x*y).val q=Nat.gcd x.val q := by
  rw [ZMod.val_mul,(Nat.mod_modEq (x.val*y.val) q).gcd_eq]
  apply Nat.Coprime.gcd_mul_right_cancel x.val
  apply (ZMod.isUnit_iff_coprime y.val q).mp
  simpa only [ZMod.natCast_zmod_val] using hy

/-- Coprime natural multiplication preserves the printed frequency gcd. -/
theorem gcd_val_mul_coprime (q : ℕ) [NeZero q] (j : ZMod q) (r : ℕ) (hr : r.Coprime q) :
    Nat.gcd (j*r).val q=Nat.gcd j.val q :=
  gcd_val_mul_unit q j r ((ZMod.isUnit_iff_coprime r q).mpr hr)

/-- The original complete inverse sum has its full prime-power gcd bound,
including zero j and zero t. -/
theorem complete_inverse_prime_power_gcd_bound (p : ℕ) [Fact p.Prime] (k : ℕ)
    (r : ℕ) (j t : ZMod (p^k)) (hr : r.Coprime (p^k)) :
    ‖completeInverseSum r j t‖≤
      localConstant p*Real.sqrt ((p^k:ℕ):ℝ)*Real.sqrt (Nat.gcd j.val (p^k):ℝ) := by
  rw [complete_inverse_eq_unitSum]
  have hb := prime_power_unitSum_gcd_bound p k (-t) (j*r)
  rwa [gcd_val_mul_coprime (p^k) j r hr] at hb

end NField.Alignment.PrimePowerGcdBound

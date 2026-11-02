/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimePowerContentReduction

/-!
# Canonical prime division and exact gcd descent

Nonunit residues supply prime-divisible canonical representatives.
Their quotients lie in the smaller residue ring, so removing one common
prime factor gives exact norm and gcd identities with no valuation input.
-/

set_option autoImplicit false
namespace NField.Alignment.PrimePowerGcdDescent
open scoped BigOperators Classical
open SquareZeroUnitShift UnitSumStationaryPhase PrimePowerContentReduction

/-- At positive exponent, a nonunit has prime-divisible canonical representative. -/
theorem prime_dvd_val_of_nonunit (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 0<k)
    (x : ZMod (p^k)) (hx : ¬IsUnit x) : p∣x.val := by
  by_contra hd
  have hu := (ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) hk).mpr hd
  exact hx (by simpa only [ZMod.natCast_zmod_val] using hu)

/-- Dividing a canonical representative by p fits strictly in the lower modulus. -/
theorem quotient_val_lt (p : ℕ) [Fact p.Prime] (k : ℕ) (x : ZMod (p^(k+1))) :
    x.val/p<p^k := by
  apply (Nat.div_lt_iff_lt_mul (Fact.out : p.Prime).pos).mpr
  simpa only [pow_succ] using x.val_lt

/-- The original residue is exactly p times its canonical quotient when divisible. -/
theorem residue_eq_prime_mul_quotient (p : ℕ) [Fact p.Prime] (k : ℕ)
    (x : ZMod (p^(k+1))) (hx : p∣x.val) :
    x=(p:ZMod (p^(k+1)))*(x.val/p:ZMod (p^(k+1))) := by
  rw [← Nat.cast_mul,Nat.mul_div_cancel' hx,ZMod.natCast_zmod_val]

/-- The canonical representative of the quotient in the smaller ring has no wrap. -/
theorem reduced_quotient_val (p : ℕ) [Fact p.Prime] (k : ℕ)
    (x : ZMod (p^(k+1))) : (x.val/p:ZMod (p^k)).val=x.val/p :=
  ZMod.val_natCast_of_lt (quotient_val_lt p k x)

/-- The actual gcd loses exactly one factor p under canonical division. -/
theorem gcd_quotient (p : ℕ) [Fact p.Prime] (k : ℕ)
    (x : ZMod (p^(k+1))) (hx : p∣x.val) :
    Nat.gcd x.val (p^(k+1))=p*Nat.gcd (x.val/p:ZMod (p^k)).val (p^k) := by
  rw [reduced_quotient_val]
  calc
    _ = Nat.gcd (p*(x.val/p)) (p*p^k) := by
      rw [Nat.mul_div_cancel' hx,← pow_succ']
    _ = _ := Nat.gcd_mul_left _ _ _

/-- A nonzero residue divisible by p cannot occur at exponent one. -/
theorem positive_lower_exponent (p : ℕ) [Fact p.Prime] (k : ℕ)
    (x : ZMod (p^(k+1))) (hx : x≠0) (hd : p∣x.val) : 1≤k := by
  by_contra hk
  have hk0 : k=0 := by omega
  have hlt : x.val<p := by simpa only [hk0,zero_add,pow_one] using x.val_lt
  exact hx ((ZMod.val_eq_zero x).mp (Nat.eq_zero_of_dvd_of_lt hd hlt))

/-- One common prime factor gives the exact actual norm recurrence. -/
theorem norm_prime_descent (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 1≤k)
    (a b : ZMod (p^(k+1))) (ha : p∣a.val) (hb : p∣b.val) :
    ‖unitSum ZMod.stdAddChar a b‖=(p:ℝ)*
      ‖unitSum ZMod.stdAddChar (a.val/p:ZMod (p^k)) (b.val/p:ZMod (p^k))‖ := by
  have h := norm_content_reduction p (k+1) k hk (by omega)
    (a.val/p:ZMod (p^(k+1))) (b.val/p:ZMod (p^(k+1)))
  simp only [show k+1-k=1 by omega,pow_one,map_natCast] at h
  rwa [← residue_eq_prime_mul_quotient p k a ha,
    ← residue_eq_prime_mul_quotient p k b hb] at h

/-- Square-root multiplication absorbs the exact prime factor in the norm recurrence. -/
theorem sqrt_gcd_descent_factor (p k g : ℕ) :
    (p:ℝ)*(Real.sqrt ((p^k:ℕ):ℝ)*Real.sqrt (g:ℝ))=
      Real.sqrt ((p^(k+1):ℕ):ℝ)*Real.sqrt ((p*g:ℕ):ℝ) := by
  simp only [Nat.cast_pow,Nat.cast_mul]
  rw [pow_succ' (p:ℝ) k,Real.sqrt_mul (Nat.cast_nonneg p),
    Real.sqrt_mul (Nat.cast_nonneg p)]
  have hs := Real.mul_self_sqrt (Nat.cast_nonneg p)
  calc
    _ = (Real.sqrt (p:ℝ)*Real.sqrt p)*(Real.sqrt ((p:ℝ)^k)*Real.sqrt g) := by rw [hs]
    _ = _ := by ring

end NField.Alignment.PrimePowerGcdDescent

/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Exact additive lifts between residue rings

Multiplication by m embeds ZMod n additively into ZMod q when m*n=q
and m is nonzero. Its standard additive character is exactly the
standard character modulo n, with no unproved normalization factor.
-/

set_option autoImplicit false
namespace NField.Alignment.ScaledResidueLift

/-- Integer multiplication followed by reduction modulo q. -/
def intScale (m q : ℕ) : ℤ →+ ZMod q where
  toFun z := (m:ZMod q)*(z:ZMod q)
  map_zero' := by simp
  map_add' x y := by simp [mul_add]

/-- The canonical additive lift z -> m*z, for q=m*n. -/
def scaledLift (m n q : ℕ) (hq : m*n=q) : ZMod n →+ ZMod q :=
  ZMod.lift n ⟨intScale m q,by
    change (m:ZMod q)*((n:ℤ):ZMod q)=0
    simpa only [Int.cast_natCast,← Nat.cast_mul,hq] using ZMod.natCast_self q⟩

/-- Integer representatives give the literal multiplication formula. -/
theorem scaledLift_intCast (m n q : ℕ) (hq : m*n=q) (z : ℤ) :
    scaledLift m n q hq (z:ZMod n)=(m:ZMod q)*(z:ZMod q) := by
  exact ZMod.lift_coe _ _ z

/-- Natural representatives give the same exact lift. -/
theorem scaledLift_natCast (m n q : ℕ) (hq : m*n=q) (z : ℕ) :
    scaledLift m n q hq (z:ZMod n)=(m:ZMod q)*(z:ZMod q) := by
  simpa only [Int.cast_natCast] using scaledLift_intCast m n q hq (z:ℤ)

/-- The canonical representative formula, useful for explicit unit shifts. -/
theorem scaledLift_val (m n q : ℕ) [NeZero n] (hq : m*n=q) (z : ZMod n) :
    scaledLift m n q hq z=(m:ZMod q)*(z.val:ZMod q) := by
  simpa only [ZMod.natCast_zmod_val] using scaledLift_natCast m n q hq z.val

/-- The additive lift is injective, proved by cancellation in integer
congruences rather than a choice of representatives. -/
theorem scaledLift_injective (m n q : ℕ) (hm : m≠0) (hq : m*n=q) :
    Function.Injective (scaledLift m n q hq) := by
  unfold scaledLift
  rw [ZMod.lift_injective]
  intro z hz
  change (m:ZMod q)*(z:ZMod q)=0 at hz
  have hmZ : (m:ℤ)≠0 := by exact_mod_cast hm
  have hd : (q:ℤ) ∣ (m:ℤ)*z := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simpa using hz
  have hqZ : (q:ℤ)=(m:ℤ)*(n:ℤ) := by exact_mod_cast hq.symm
  rw [hqZ,mul_dvd_mul_iff_left hmZ] at hd
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd z n).mpr hd

/-- The standard character on the lifted residue is exactly the smaller
standard character; the factor m cancels in the exponential argument. -/
theorem stdAddChar_scaledLift (m n q : ℕ) [NeZero m] [NeZero n] [NeZero q]
    (hq : m*n=q) (z : ZMod n) :
    ZMod.stdAddChar (scaledLift m n q hq z)=ZMod.stdAddChar z := by
  obtain ⟨z,rfl⟩ := ZMod.intCast_surjective z
  rw [scaledLift_intCast]
  have hmC : (m:ℂ)≠0 := by exact_mod_cast NeZero.ne m
  have hnC : (n:ℂ)≠0 := by exact_mod_cast NeZero.ne n
  have hqC : (q:ℂ)=(m:ℂ)*(n:ℂ) := by exact_mod_cast hq.symm
  rw [show (m:ZMod q)*(z:ZMod q)=(((m:ℤ)*z:ℤ):ZMod q) by push_cast; rfl]
  rw [ZMod.stdAddChar_coe,ZMod.stdAddChar_coe]
  congr 1
  push_cast
  rw [hqC]
  field_simp

/-- Reducing a lifted residue modulo m gives zero. -/
theorem reduce_scaledLift_zero (m n q : ℕ) [NeZero n] (hq : m*n=q) (z : ZMod n) :
    ZMod.castHom (show m∣q from hq ▸ dvd_mul_right m n) (ZMod m)
      (scaledLift m n q hq z)=0 := by
  rw [scaledLift_val,map_mul,map_natCast,map_natCast,ZMod.natCast_self,zero_mul]

/-- Lifting the reduction of x is exactly m*x in the original ring. -/
theorem scaledLift_reduction (m n q : ℕ) (hq : m*n=q) (x : ZMod q) :
    scaledLift m n q hq
      (ZMod.castHom (show n∣q from hq ▸ dvd_mul_left n m) (ZMod n) x) = (m:ZMod q)*x := by
  obtain ⟨x,rfl⟩ := ZMod.intCast_surjective x
  rw [map_intCast,scaledLift_intCast]

/-- A phase divisible by m has the exact standard character at modulus
n=q/m, evaluated on the reduced residual phase. -/
theorem stdAddChar_scaled_phase (m n q : ℕ) [NeZero m] [NeZero n] [NeZero q]
    (hq : m*n=q) (x : ZMod q) :
    ZMod.stdAddChar ((m:ZMod q)*x) =
      ZMod.stdAddChar (ZMod.castHom (show n∣q from hq ▸ dvd_mul_left n m) (ZMod n) x) := by
  rw [← scaledLift_reduction m n q hq x,stdAddChar_scaledLift]

end NField.Alignment.ScaledResidueLift

/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimePowerGcdBound
import Mathlib.Algebra.Group.Prod

/-!
# Exact CRT factorization with the standard-character twists

Bezout coefficients give the literal character factorization. The actual
unit-group equivalence then factors the finite sum. Both twists are units,
so their gcd factors agree with the untwisted reduced frequencies.
-/

set_option autoImplicit false
namespace NField.Alignment.KloostermanCRT
open scoped BigOperators Classical
open SquareZeroUnitShift UnitSumStationaryPhase ScaledResidueLift PrimePowerGcdBound

/-- Left and right actual residue reductions. -/
def leftReduction (m n : ℕ) : ZMod (m*n) →+* ZMod m :=
  ZMod.castHom (dvd_mul_right m n) _
def rightReduction (m n : ℕ) : ZMod (m*n) →+* ZMod n :=
  ZMod.castHom (dvd_mul_left n m) _

/-- The inverse-modulus twists given by integer Bezout coefficients. -/
def leftTwist (m n : ℕ) : ZMod m := (Nat.gcdB m n:ZMod m)
def rightTwist (m n : ℕ) : ZMod n := (Nat.gcdA m n:ZMod n)

private theorem bezout_relation {R : Type*} [CommRing R] (m n : ℕ) (h : m.Coprime n) :
    (m:R)*(Nat.gcdA m n:R)+(n:R)*(Nat.gcdB m n:R)=1 := by
  have hz : (m:ℤ)*Nat.gcdA m n+(n:ℤ)*Nat.gcdB m n=1 := by
    rw [← Nat.gcd_eq_gcd_ab,h.gcd_eq_one]
    rfl
  have hr := congrArg (fun z : ℤ => (z:R)) hz
  push_cast at hr
  exact hr

/-- The left character twist is a unit, with inverse n modulo m. -/
theorem leftTwist_isUnit (m n : ℕ) (h : m.Coprime n) : IsUnit (leftTwist m n) := by
  have he := bezout_relation (R := ZMod m) m n h
  simp only [ZMod.natCast_self,zero_mul,zero_add] at he
  exact IsUnit.of_mul_eq_one (n:ZMod m) (by simpa only [leftTwist,mul_comm] using he)

/-- The right character twist is a unit, with inverse m modulo n. -/
theorem rightTwist_isUnit (m n : ℕ) (h : m.Coprime n) : IsUnit (rightTwist m n) := by
  have he := bezout_relation (R := ZMod n) m n h
  simp only [ZMod.natCast_self,zero_mul,add_zero] at he
  exact IsUnit.of_mul_eq_one (m:ZMod n) (by simpa only [rightTwist,mul_comm] using he)

/-- Exact factorization of the standard additive character, retaining both twists. -/
theorem standard_character_crt (m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n)
    (x : ZMod (m*n)) :
    ZMod.stdAddChar x=
      ZMod.stdAddChar (leftTwist m n*leftReduction m n x)*
      ZMod.stdAddChar (rightTwist m n*rightReduction m n x) := by
  have he := bezout_relation (R := ZMod (m*n)) m n h
  have hx : x=(n:ZMod (m*n))*((Nat.gcdB m n:ZMod (m*n))*x)+
      (m:ZMod (m*n))*((Nat.gcdA m n:ZMod (m*n))*x) := by
    linear_combination -x*he
  calc
    ZMod.stdAddChar x = ZMod.stdAddChar
        ((n:ZMod (m*n))*((Nat.gcdB m n:ZMod (m*n))*x)+
          (m:ZMod (m*n))*((Nat.gcdA m n:ZMod (m*n))*x)) := congrArg _ hx
    _ = _ := by
      rw [AddChar.map_add_eq_mul,
        stdAddChar_scaled_phase n m (m*n) (Nat.mul_comm n m),
        stdAddChar_scaled_phase m n (m*n) rfl]
      simp only [map_mul,map_intCast,leftTwist,rightTwist,leftReduction,rightReduction]

/-- The actual CRT equivalence on units, followed by the product-unit equivalence. -/
def unitEquiv (m n : ℕ) (h : m.Coprime n) :
    (ZMod (m*n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans MulEquiv.prodUnits

/-- The first CRT unit component is actual unit reduction modulo m. -/
theorem unitEquiv_fst (m n : ℕ) (h : m.Coprime n) (u : (ZMod (m*n))ˣ) :
    (unitEquiv m n h u).1=ZMod.unitsMap (dvd_mul_right m n) u := by
  apply Units.ext
  change (ZMod.cast (u:ZMod (m*n)):ZMod m × ZMod n).1=ZMod.cast (u:ZMod (m*n))
  exact Prod.fst_zmod_cast _

/-- The second CRT unit component is actual unit reduction modulo n. -/
theorem unitEquiv_snd (m n : ℕ) (h : m.Coprime n) (u : (ZMod (m*n))ˣ) :
    (unitEquiv m n h u).2=ZMod.unitsMap (dvd_mul_left n m) u := by
  apply Units.ext
  change (ZMod.cast (u:ZMod (m*n)):ZMod m × ZMod n).2=ZMod.cast (u:ZMod (m*n))
  exact Prod.snd_zmod_cast _

private theorem phase_cast (q d : ℕ) (hd : d∣q) (a b : ZMod q) (u : (ZMod q)ˣ) :
    ZMod.castHom hd (ZMod d) (phase a b u)=
      phase (ZMod.castHom hd (ZMod d) a) (ZMod.castHom hd (ZMod d) b) (ZMod.unitsMap hd u) := by
  simp only [phase,map_add,map_mul]
  rw [← map_inv]
  rfl

/-- The actual phase character splits into the two twisted local phase characters. -/
theorem phase_character_crt (m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n)
    (a b : ZMod (m*n)) (u : (ZMod (m*n))ˣ) :
    ZMod.stdAddChar (phase a b u)=
      ZMod.stdAddChar (phase (leftTwist m n*leftReduction m n a)
        (leftTwist m n*leftReduction m n b) (unitEquiv m n h u).1)*
      ZMod.stdAddChar (phase (rightTwist m n*rightReduction m n a)
        (rightTwist m n*rightReduction m n b) (unitEquiv m n h u).2) := by
  rw [standard_character_crt m n h,unitEquiv_fst,unitEquiv_snd]
  unfold leftReduction rightReduction
  rw [phase_cast,phase_cast]
  congr 1 <;> congr 1 <;> unfold phase <;> ring

/-- Exact CRT product formula for the literal finite unit sum. -/
theorem unitSum_crt (m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n)
    (a b : ZMod (m*n)) :
    unitSum ZMod.stdAddChar a b=
      unitSum ZMod.stdAddChar (leftTwist m n*leftReduction m n a) (leftTwist m n*leftReduction m n b)*
      unitSum ZMod.stdAddChar (rightTwist m n*rightReduction m n a) (rightTwist m n*rightReduction m n b) := by
  unfold unitSum
  simp_rw [phase_character_crt m n h]
  let f := fun v : (ZMod m)ˣ × (ZMod n)ˣ =>
    ZMod.stdAddChar (phase (leftTwist m n*leftReduction m n a)
      (leftTwist m n*leftReduction m n b) v.1)*
    ZMod.stdAddChar (phase (rightTwist m n*rightReduction m n a)
      (rightTwist m n*rightReduction m n b) v.2)
  change (∑ u, f (unitEquiv m n h u))=_
  calc
    _ = ∑ v, f v := Equiv.sum_comp (unitEquiv m n h).toEquiv f
    _ = _ := by
      dsimp only [f]
      rw [Fintype.sum_prod_type,Finset.sum_mul_sum]

/-- The exact norm also factors across coprime moduli. -/
theorem norm_unitSum_crt (m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n)
    (a b : ZMod (m*n)) :
    ‖unitSum ZMod.stdAddChar a b‖=
      ‖unitSum ZMod.stdAddChar (leftTwist m n*leftReduction m n a) (leftTwist m n*leftReduction m n b)‖*
      ‖unitSum ZMod.stdAddChar (rightTwist m n*rightReduction m n a) (rightTwist m n*rightReduction m n b)‖ := by
  rw [unitSum_crt m n h,norm_mul]

/-- The left CRT twist preserves the actual local frequency gcd. -/
theorem left_twist_gcd (m n : ℕ) [NeZero m] (h : m.Coprime n) (b : ZMod (m*n)) :
    Nat.gcd (leftTwist m n*leftReduction m n b).val m=Nat.gcd (leftReduction m n b).val m := by
  rw [mul_comm]
  exact gcd_val_mul_unit m _ _ (leftTwist_isUnit m n h)

/-- The right CRT twist preserves the actual local frequency gcd. -/
theorem right_twist_gcd (m n : ℕ) [NeZero n] (h : m.Coprime n) (b : ZMod (m*n)) :
    Nat.gcd (rightTwist m n*rightReduction m n b).val n=Nat.gcd (rightReduction m n b).val n := by
  rw [mul_comm]
  exact gcd_val_mul_unit n _ _ (rightTwist_isUnit m n h)

end NField.Alignment.KloostermanCRT

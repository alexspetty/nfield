/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.SquareZeroUnitShift
import Mathlib.Data.ZMod.Basic

/-!
# Exact quadratic inverse phases under cube-zero shifts

The degree-two inverse expansion is exact when the increment cubed is
zero. At odd prime-power exponents, p^h increments have this property
modulo p^(2h+1) for h>=1, retaining the residual quadratic phase.
-/

set_option autoImplicit false
namespace NField.Alignment.CubeZeroUnitShift
variable {R : Type*} [CommRing R]

private theorem shifted_mul_inverse (u : Rˣ) (d : R) (hd : d^3=0) :
    ((u:R)+d)*(((u⁻¹:Rˣ):R)-d*((u⁻¹:Rˣ):R)^2+d^2*((u⁻¹:Rˣ):R)^3)=1 := by
  have huv : (u:R)*((u⁻¹:Rˣ):R)=1 := u.val_inv
  linear_combination (1-d*((u⁻¹:Rˣ):R)+d^2*((u⁻¹:Rˣ):R)^2)*huv + ((u⁻¹:Rˣ):R)^3*hd

/-- The actual shifted unit, with its inverse through degree two. -/
def shift (u : Rˣ) (d : R) (hd : d^3=0) : Rˣ where
  val := (u:R)+d
  inv := ((u⁻¹:Rˣ):R)-d*((u⁻¹:Rˣ):R)^2+d^2*((u⁻¹:Rˣ):R)^3
  val_inv := shifted_mul_inverse u d hd
  inv_val := by rw [mul_comm]; exact shifted_mul_inverse u d hd

@[simp] theorem shift_val (u : Rˣ) (d : R) (hd : d^3=0) :
    (shift u d hd:R)=(u:R)+d := rfl

/-- The inverse expansion has no cubic remainder. -/
theorem shift_inverse (u : Rˣ) (d : R) (hd : d^3=0) :
    (((shift u d hd)⁻¹:Rˣ):R)=
      ((u⁻¹:Rˣ):R)-d*((u⁻¹:Rˣ):R)^2+d^2*((u⁻¹:Rˣ):R)^3 := rfl

/-- The literal inverse-additive phase retains its exact quadratic term. -/
theorem phase_shift (a b : R) (u : Rˣ) (d : R) (hd : d^3=0) :
    SquareZeroUnitShift.phase a b (shift u d hd) =
      SquareZeroUnitShift.phase a b u+d*(a-b*((u⁻¹:Rˣ):R)^2)+
        d^2*(b*((u⁻¹:Rˣ):R)^3) := by
  change a*((u:R)+d)+b*(((u⁻¹:Rˣ):R)-d*((u⁻¹:Rˣ):R)^2+d^2*((u⁻¹:Rˣ):R)^3) = _
  unfold SquareZeroUnitShift.phase
  ring

/-- A p^h multiple has cube zero modulo p^(2h+1) for every h>=1. -/
theorem power_cube_zero (p h : ℕ) (hh : 1≤h) (z : ZMod (p^(2*h+1))) :
    ((p:ZMod (p^(2*h+1)))^h*z)^3=0 := by
  rw [mul_pow,← pow_mul]
  have hc : (p:ZMod (p^(2*h+1)))^(h*3)=0 := by
    rw [← Nat.cast_pow]
    exact (CharP.cast_eq_zero_iff _ _ _).mpr (Nat.pow_dvd_pow p (by omega))
  rw [hc,zero_mul]

/-- The exact quadratic phase formula at the actual odd-exponent
modulus, with the cube-zero condition discharged. -/
theorem odd_exponent_phase_shift (p h : ℕ) (hh : 1≤h)
    (a b z : ZMod (p^(2*h+1))) (u : (ZMod (p^(2*h+1)))ˣ) :
    SquareZeroUnitShift.phase a b
      (shift u ((p:ZMod (p^(2*h+1)))^h*z) (power_cube_zero p h hh z)) =
    SquareZeroUnitShift.phase a b u+
      ((p:ZMod (p^(2*h+1)))^h*z)*(a-b*((u⁻¹:(ZMod (p^(2*h+1)))ˣ):ZMod (p^(2*h+1)))^2)+
      ((p:ZMod (p^(2*h+1)))^h*z)^2*
        (b*((u⁻¹:(ZMod (p^(2*h+1)))ˣ):ZMod (p^(2*h+1)))^3) :=
  phase_shift a b u _ (power_cube_zero p h hh z)

end NField.Alignment.CubeZeroUnitShift

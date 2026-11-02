/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib.Algebra.Ring.Units
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Tactic

/-!
# Exact inverse phases under square-zero unit shifts

A square-zero increment preserves units and makes the reciprocal phase
exactly linear. The inverse and the translation permutation are explicit;
no division by a nonunit is used.
-/

set_option autoImplicit false
namespace NField.Alignment.SquareZeroUnitShift
variable {R : Type*} [CommRing R]

/-- Multiplying the explicit shifted unit by its inverse gives one. -/
theorem shifted_mul_inverse (u : Rˣ) (d : R) (hd : d^2=0) :
    ((u:R)+d)*((u⁻¹:Rˣ):R)-((u:R)+d)*(d*((u⁻¹:Rˣ):R)^2)=1 := by
  have huv : (u:R)*((u⁻¹:Rˣ):R)=1 := u.val_inv
  linear_combination (1-d*((u⁻¹:Rˣ):R))*huv - ((u⁻¹:Rˣ):R)^2*hd

/-- The actual unit u+d, with its exact reciprocal for d squared zero. -/
def shift (u : Rˣ) (d : R) (hd : d^2=0) : Rˣ where
  val := (u:R)+d
  inv := ((u⁻¹:Rˣ):R)-d*((u⁻¹:Rˣ):R)^2
  val_inv := by rw [mul_sub]; exact shifted_mul_inverse u d hd
  inv_val := by rw [mul_comm,mul_sub]; exact shifted_mul_inverse u d hd

@[simp] theorem shift_val (u : Rˣ) (d : R) (hd : d^2=0) :
    (shift u d hd : R) = (u:R)+d := rfl

/-- The reciprocal formula is the inverse of the constructed unit. -/
theorem shift_inverse (u : Rˣ) (d : R) (hd : d^2=0) :
    (((shift u d hd)⁻¹ : Rˣ) : R) =
      ((u⁻¹:Rˣ):R)-d*((u⁻¹:Rˣ):R)^2 := rfl

/-- Addition of a square-zero increment is a permutation of all units. -/
def shiftEquiv (d : R) (hd : d^2=0) : Rˣ ≃ Rˣ where
  toFun u := shift u d hd
  invFun u := shift u (-d) (by simpa using hd)
  left_inv u := by apply Units.ext; simp
  right_inv u := by apply Units.ext; simp

@[simp] theorem shiftEquiv_apply (d : R) (hd : d^2=0) (u : Rˣ) :
    shiftEquiv d hd u = shift u d hd := rfl

/-- The inverse-additive phase on actual units. -/
def phase (a b : R) (u : Rˣ) : R := a*(u:R)+b*((u⁻¹:Rˣ):R)

/-- The exact first-order formula has no remainder because d squared is zero. -/
theorem phase_shift (a b : R) (u : Rˣ) (d : R) (hd : d^2=0) :
    phase a b (shift u d hd) = phase a b u+d*(a-b*((u⁻¹:Rˣ):R)^2) := by
  change a*((u:R)+d)+b*(((u⁻¹:Rˣ):R)-d*((u⁻¹:Rˣ):R)^2) = _
  unfold phase
  ring

/-- Multiplication by the square of a unit clears the inverse in the
critical equation without changing its zero set. -/
theorem critical_iff (a b c : R) (u : Rˣ) :
    c*(a-b*((u⁻¹:Rˣ):R)^2)=0 ↔ c*(a*(u:R)^2-b)=0 := by
  have huv : (u:R)*((u⁻¹:Rˣ):R)=1 := u.val_inv
  have h1 : c*(a-b*((u⁻¹:Rˣ):R)^2)*(u:R)^2=c*(a*(u:R)^2-b) := by
    calc
      _ = c*(a*(u:R)^2-b*((u:R)*((u⁻¹:Rˣ):R))^2) := by ring
      _ = _ := by rw [huv]; ring
  have h2 : c*(a*(u:R)^2-b)*((u⁻¹:Rˣ):R)^2=c*(a-b*((u⁻¹:Rˣ):R)^2) := by
    calc
      _ = c*(a*((u:R)*((u⁻¹:Rˣ):R))^2-b*((u⁻¹:Rˣ):R)^2) := by ring
      _ = _ := by rw [huv]; ring
  exact ⟨fun h => by rw [← h1,h,zero_mul],fun h => by rw [← h2,h,zero_mul]⟩

end NField.Alignment.SquareZeroUnitShift

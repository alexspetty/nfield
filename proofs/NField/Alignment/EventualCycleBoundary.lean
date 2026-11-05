/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.FiniteStateOrbitBoundary
import Mathlib.Dynamics.PeriodicPts.Defs

/-! # The actual eventual cycle and its predecessor map

The cycle consists of the iterates of the repeated state. Its permutation is
the original transition restricted to those states, not an unrelated bijection.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.EventualCycleBoundary
open FiniteStateOrbitBoundary
open scoped BigOperators

abbrev OrbitState {α : Type*} (T : α → α) (x : α) :=
  {y : α // ∃ n : ℕ, T^[n] x = y}

theorem orbitState_periodic {α : Type*} {T : α → α} {x : α} {p : ℕ}
    (hx : Function.IsPeriodicPt T p x) (y : OrbitState T x) :
    Function.IsPeriodicPt T p y.val := by
  obtain ⟨n, hn⟩ := y.property
  rw [← hn]
  exact hx.apply_iterate n

def orbitPermutation {α : Type*} {T : α → α} {x : α} {p : ℕ}
    (hp : 0 < p) (hx : Function.IsPeriodicPt T p x) : OrbitState T x ≃ OrbitState T x where
  toFun y := ⟨T y.val, by
    obtain ⟨n, hn⟩ := y.property
    exact ⟨n + 1, by rw [Function.iterate_succ_apply', hn]⟩⟩
  invFun y := ⟨T^[p - 1] y.val, by
    obtain ⟨n, hn⟩ := y.property
    exact ⟨p - 1 + n, by rw [Function.iterate_add_apply, hn]⟩⟩
  left_inv y := by
    apply Subtype.ext
    change T^[p - 1] (T y.val) = y.val
    rw [← Function.iterate_succ_apply, Nat.succ_eq_add_one, Nat.sub_add_cancel hp]
    exact orbitState_periodic hx y
  right_inv y := by
    apply Subtype.ext
    change T (T^[p - 1] y.val) = y.val
    rw [← Function.iterate_succ_apply' T, Nat.succ_eq_add_one, Nat.sub_add_cancel hp]
    exact orbitState_periodic hx y

theorem orbitPermutation_apply {α : Type*} {T : α → α} {x : α} {p : ℕ}
    (hp : 0 < p) (hx : Function.IsPeriodicPt T p x) (y : OrbitState T x) :
    (orbitPermutation hp hx y).val = T y.val := rfl

theorem orbitPermutation_predecessor {α : Type*} {T : α → α} {x : α} {p : ℕ}
    (hp : 0 < p) (hx : Function.IsPeriodicPt T p x) (y : OrbitState T x) :
    T ((orbitPermutation hp hx).symm y).val = y.val := by
  exact congrArg Subtype.val ((orbitPermutation hp hx).apply_symm_apply y)

theorem finiteTrajectory_enters_actual_cycle {α : Type*} [Fintype α]
    (T : α → α) (x : α) :
    ∃ start p : ℕ, ∃ hp : 0 < p, ∃ hx : Function.IsPeriodicPt T p (T^[start] x),
      ∀ y : OrbitState T (T^[start] x),
        (orbitPermutation hp hx y).val = T y.val := by
  obtain ⟨start, p, hp, h⟩ := finiteTrajectory_eventuallyPeriodic T x
  have hx : Function.IsPeriodicPt T p (T^[start] x) := by
    change T^[p] (T^[start] x) = T^[start] x
    rw [← Function.iterate_add_apply]
    simpa [Nat.add_comm] using h 0
  exact ⟨start, p, hp, hx, fun _ => rfl⟩

theorem actual_cycle_boundary {α A : Type*} [Fintype α] [AddCommGroup A]
    {T : α → α} {x : α} {p : ℕ} (hp : 0 < p)
    (hx : Function.IsPeriodicPt T p x) (w : OrbitState T x → A) :
    letI : Fintype (OrbitState T x) := Fintype.ofFinite _
    ∑ y : OrbitState T x, dynamicalBoundary (orbitPermutation hp hx) w y = 0 := by
  letI : Fintype (OrbitState T x) := Fintype.ofFinite _
  exact dynamicalBoundary_sum_zero (orbitPermutation hp hx) w

theorem emittedDigit_lt_base (b q : ℕ) [NeZero q] (hb : 0 < b) (R : (ZMod q)ˣ) :
    emittedDigit b q R < b := by
  rw [emittedDigit, Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero (NeZero.ne q))]
  simpa [Nat.mul_comm] using Nat.mul_lt_mul_of_pos_left (ZMod.val_lt R.val) hb

end NField.Alignment.EventualCycleBoundary

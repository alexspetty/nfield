/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.DenominatorSplit
import Mathlib.GroupTheory.OrderOfElement

/-! # Exact periods and cosets of reduced rational remainder orbits -/

set_option autoImplicit false
namespace NField.Alignment.RationalRemainderOrbit
open DenominatorSplit

theorem reduced_numerator_coprime_part {n q : ℕ} (b : ℕ) (hq : q ≠ 0)
    (hnq : n.Coprime q) : n.Coprime (coprimePart b q) :=
  hnq.of_dvd_right (coprimePart_dvd b hq)

theorem remainderCRT_recursion (b : ℕ) {q : ℕ} (hq : q ≠ 0) (R : ZMod q) :
    remainderCRT b hq ((b : ZMod q) * R) =
      ((b : ZMod (supportedPart b q)) * (remainderCRT b hq R).1,
       (b : ZMod (coprimePart b q)) * (remainderCRT b hq R).2) := by
  rw [map_mul, remainderCRT_natCast]
  rfl

theorem remainderCRT_after_burnIn (b : ℕ) {q : ℕ} (hq : q ≠ 0) (k n : ℕ) :
    remainderCRT b hq ((b ^ (burnIn b q + k) * n : ℕ) : ZMod q) =
      (0, ((b ^ (burnIn b q + k) * n : ℕ) : ZMod (coprimePart b q))) := by
  rw [remainderCRT_natCast, supportedPart_eventually_zero]

/-- Multiplication by the base is an equivalence on the surviving unit group. -/
def unitTransition {q : ℕ} (b : ℕ) (hbq : b.Coprime q) : (ZMod q)ˣ ≃ (ZMod q)ˣ :=
  Equiv.mulLeft (ZMod.unitOfCoprime b hbq)

theorem unitTransition_val {q : ℕ} (b : ℕ) (hbq : b.Coprime q) (R : (ZMod q)ˣ) :
    (unitTransition b hbq R).val = (b : ZMod q) * R.val := by
  simp [unitTransition, ZMod.coe_unitOfCoprime]

theorem unitTransition_iterate {q : ℕ} (b : ℕ) (hbq : b.Coprime q)
    (R : (ZMod q)ˣ) (k : ℕ) :
    (unitTransition b hbq)^[k] R = ZMod.unitOfCoprime b hbq ^ k * R := by
  exact mul_left_iterate_apply _ _

theorem return_iff_order_dvd {q : ℕ} (b : ℕ) (hbq : b.Coprime q)
    (R : (ZMod q)ˣ) (k : ℕ) :
    (unitTransition b hbq)^[k] R = R ↔ orderOf (ZMod.unitOfCoprime b hbq) ∣ k := by
  rw [unitTransition_iterate, mul_eq_right]
  exact orderOf_dvd_iff_pow_eq_one.symm

theorem exact_positive_period {q : ℕ} [NeZero q] (b : ℕ) (hbq : b.Coprime q)
    (R : (ZMod q)ˣ) :
    0 < orderOf (ZMod.unitOfCoprime b hbq) ∧
    (unitTransition b hbq)^[orderOf (ZMod.unitOfCoprime b hbq)] R = R ∧
    ∀ k : ℕ, 0 < k → (unitTransition b hbq)^[k] R = R →
      orderOf (ZMod.unitOfCoprime b hbq) ≤ k := by
  refine ⟨orderOf_pos _, (return_iff_order_dvd b hbq R _).mpr (dvd_refl _), ?_⟩
  intro k hk hreturn
  exact Nat.le_of_dvd hk ((return_iff_order_dvd b hbq R k).mp hreturn)

theorem orbit_is_coset {q : ℕ} [NeZero q] (b : ℕ) (hbq : b.Coprime q)
    (R : (ZMod q)ˣ) :
    Set.range (fun k : ℕ => (unitTransition b hbq)^[k] R) =
      (fun u => R * u) '' (Subgroup.zpowers (ZMod.unitOfCoprime b hbq) : Set (ZMod q)ˣ) := by
  simp only [unitTransition_iterate]
  rw [← powers_eq_zpowers]
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨ZMod.unitOfCoprime b hbq ^ k, ⟨k, rfl⟩, mul_comm _ _⟩
  · rintro ⟨u, ⟨k, rfl⟩, rfl⟩
    exact ⟨k, mul_comm _ _⟩

end NField.Alignment.RationalRemainderOrbit

/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.GroupTheory.Index
import Mathlib.Tactic

/-!
# Quadratic unit-root counts from cyclic unit groups

A nonempty quadratic root set with a unit phase parameter is an actual
fiber of the square map on units. Its size is at most two when that unit
group is cyclic. Odd prime-power rings supply the required instance.
-/

set_option autoImplicit false
namespace NField.Alignment.CyclicUnitQuadraticRoots
open scoped BigOperators Classical

/-- Every square-map fiber in a finite cyclic commutative group has at
most two elements, including fibers outside the image. -/
theorem card_square_fiber_le_two {G : Type*} [CommGroup G] [Fintype G]
    [DecidableEq G] [IsCyclic G] (v : G) :
    (Finset.univ.filter (fun u : G => u^2=v)).card ≤ 2 := by
  by_cases hv : ∃ u : G, u^2=v
  · have he := MonoidHom.card_fiber_eq_of_mem_range (powMonoidHom (α := G) 2)
      hv (show (1:G) ∈ Set.range (powMonoidHom (α := G) 2) from ⟨1,by simp⟩)
    change (Finset.univ.filter (fun u : G => u^2=v)).card =
      (Finset.univ.filter (fun u : G => u^2=1)).card at he
    rw [he]
    exact IsCyclic.card_pow_eq_one_le (by decide : 0<2)
  · have he : Finset.univ.filter (fun u : G => u^2=v) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro u hu
      exact hv ⟨u,(Finset.mem_filter.mp hu).2⟩
    rw [he]
    simp

/-- With at least one unit phase parameter, the actual quadratic unit
root set in a ring with cyclic units has at most two elements. -/
theorem card_quadratic_units_le_two {R : Type*} [CommRing R] [Fintype R]
    [DecidableEq R] [IsCyclic Rˣ] (a b : R) (hab : IsUnit a ∨ IsUnit b) :
    (Finset.univ.filter (fun u : Rˣ => a*(u:R)^2=b)).card ≤ 2 := by
  by_cases hr : ∃ u : Rˣ, a*(u:R)^2=b
  · obtain ⟨u0,hu0⟩ := hr
    have ha : IsUnit a := hab.elim id (fun hb =>
      (IsUnit.mul_iff.mp (show IsUnit (a*(u0:R)^2) from hu0.symm ▸ hb)).1)
    have he : Finset.univ.filter (fun u : Rˣ => a*(u:R)^2=b) =
        Finset.univ.filter (fun u : Rˣ => u^2=u0^2) := by
      ext u
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · intro hu
        apply Units.ext
        exact ha.mul_left_cancel (hu.trans hu0.symm)
      · intro hu
        have hv := congrArg (fun z : Rˣ => (z:R)) hu
        simpa only [Units.val_pow_eq_pow_val] using (congrArg (fun z : R => a*z) hv).trans hu0
    rw [he]
    exact card_square_fiber_le_two (u0^2)
  · have he : Finset.univ.filter (fun u : Rˣ => a*(u:R)^2=b) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro u hu
      exact hr ⟨u,(Finset.mem_filter.mp hu).2⟩
    rw [he]
    simp

/-- Odd prime-power unit groups are cyclic, so the literal quadratic
unit-root count is at most two at every exponent. -/
theorem odd_prime_power_quadratic_count (p : ℕ) [Fact p.Prime] (hp : p≠2)
    (m : ℕ) (a b : ZMod (p^m)) (hab : IsUnit a ∨ IsUnit b) :
    (Finset.univ.filter (fun u : (ZMod (p^m))ˣ => a*(u:ZMod (p^m))^2=b)).card ≤ 2 := by
  letI := ZMod.isCyclic_units_of_prime_pow p (Fact.out : p.Prime) hp m
  exact card_quadratic_units_le_two a b hab

/-- If precisely one phase parameter is a unit, there are no quadratic
unit roots; this fact does not require cyclicity or odd characteristic. -/
theorem no_quadratic_units_of_unit_mismatch {R : Type*} [CommRing R]
    (a b : R) (hab : (IsUnit a ∧ ¬IsUnit b) ∨ (¬IsUnit a ∧ IsUnit b)) :
    ∀ u : Rˣ, a*(u:R)^2≠b := by
  intro u hu
  have he : IsUnit a ↔ IsUnit b := by
    rw [← hu,IsUnit.mul_iff]
    exact ⟨fun ha => ⟨ha,u.isUnit.pow 2⟩,And.left⟩
  rcases hab with h | h
  · exact h.2 (he.mp h.1)
  · exact h.1 (he.mpr h.2)

end NField.Alignment.CyclicUnitQuadraticRoots

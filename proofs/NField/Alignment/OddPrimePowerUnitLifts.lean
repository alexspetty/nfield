/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ScaledResidueLift
import NField.Alignment.CubeZeroUnitShift
import NField.Alignment.PrimePowerUnitFibers

/-!
# Actual additive parametrization of odd-exponent unit fibers

The injective scaled residue map and cube-zero unit shifts give a map
into the actual reduction fiber. Its known exact cardinality proves
surjectivity. The resulting equivalence rewrites the literal fiber sum.
-/

set_option autoImplicit false
namespace NField.Alignment.OddPrimePowerUnitLifts
open scoped BigOperators Classical
open ScaledResidueLift PrimePowerUnitFibers

/-- The exact factorization of the odd-exponent modulus. -/
theorem half_product (p h : ℕ) : p^h*p^(h+1)=p^(2*h+1) := by
  rw [← pow_add]
  congr 1
  omega

/-- The actual additive p^h lift into modulus p^(2h+1). -/
def delta (p h : ℕ) : ZMod (p^(h+1)) →+ ZMod (p^(2*h+1)) :=
  scaledLift (p^h) (p^(h+1)) (p^(2*h+1)) (half_product p h)

/-- The scaled lift agrees with the canonical natural representative. -/
theorem delta_val (p : ℕ) [Fact p.Prime] (h : ℕ) (z : ZMod (p^(h+1))) :
    delta p h z=(p:ZMod (p^(2*h+1)))^h*(z.val:ZMod (p^(2*h+1))) := by
  rw [delta,scaledLift_val,Nat.cast_pow]

/-- Every actual lift increment is cube zero for h>=1. -/
theorem delta_cube_zero (p : ℕ) [Fact p.Prime] (h : ℕ) (hh : 1≤h)
    (z : ZMod (p^(h+1))) : (delta p h z)^3=0 := by
  rw [delta_val]
  exact CubeZeroUnitShift.power_cube_zero p h hh _

/-- The explicit lift of a unit along an additive residue. -/
def unitLift (p : ℕ) [Fact p.Prime] (h : ℕ) (hh : 1≤h)
    (u : (ZMod (p^(2*h+1)))ˣ) (z : ZMod (p^(h+1))) : (ZMod (p^(2*h+1)))ˣ :=
  CubeZeroUnitShift.shift u (delta p h z) (delta_cube_zero p h hh z)

/-- The unit reduction map from the odd-exponent ring to its h-th level. -/
def unitReduction (p h : ℕ) : (ZMod (p^(2*h+1)))ˣ →* (ZMod (p^h))ˣ :=
  ZMod.unitsMap (Nat.pow_dvd_pow p (by omega : h≤2*h+1))

/-- The explicit lift lies in the actual reduction fiber of u. -/
theorem unitLift_reduces (p : ℕ) [Fact p.Prime] (h : ℕ) (hh : 1≤h)
    (u : (ZMod (p^(2*h+1)))ˣ) (z : ZMod (p^(h+1))) :
    unitReduction p h (unitLift p h hh u z)=unitReduction p h u := by
  apply Units.ext
  change ZMod.castHom (Nat.pow_dvd_pow p (by omega : h≤2*h+1)) (ZMod (p^h))
    ((u:ZMod (p^(2*h+1)))+delta p h z) = _
  rw [map_add]
  have hz := reduce_scaledLift_zero (p^h) (p^(h+1)) (p^(2*h+1)) (half_product p h) z
  change ZMod.castHom _ (ZMod (p^h)) (delta p h z)=0 at hz
  rw [hz,add_zero]
  rfl

/-- Distinct additive residues give distinct actual unit lifts. -/
theorem unitLift_injective (p : ℕ) [Fact p.Prime] (h : ℕ) (hh : 1≤h)
    (u : (ZMod (p^(2*h+1)))ˣ) : Function.Injective (unitLift p h hh u) := by
  intro z w he
  have hv := congrArg (fun v : (ZMod (p^(2*h+1)))ˣ => (v:ZMod (p^(2*h+1)))) he
  change (u:ZMod (p^(2*h+1)))+delta p h z=(u:ZMod (p^(2*h+1)))+delta p h w at hv
  apply scaledLift_injective (p^h) (p^(h+1)) (p^(2*h+1))
    (pow_ne_zero h (Fact.out : p.Prime).ne_zero) (half_product p h)
  exact add_left_cancel hv

/-- The actual fiber is in bijection with the additive lift residues.
Surjectivity follows from the proved exact cardinality, not a hypothesis. -/
noncomputable def unitFiberEquiv (p : ℕ) [Fact p.Prime] (h : ℕ) (hh : 1≤h)
    (u : (ZMod (p^(2*h+1)))ˣ) :
    ZMod (p^(h+1)) ≃ {v : (ZMod (p^(2*h+1)))ˣ // unitReduction p h v=unitReduction p h u} :=
  Equiv.ofBijective (fun z => ⟨unitLift p h hh u z,unitLift_reduces p h hh u z⟩) (by
    apply (Fintype.bijective_iff_injective_and_card _).mpr
    constructor
    · intro z w he
      exact unitLift_injective p h hh u (congrArg Subtype.val he)
    · rw [ZMod.card,Fintype.card_subtype]
      have hc := card_unit_fiber p (2*h+1) h hh (by omega) (unitReduction p h u)
      simpa only [show 2*h+1-h=h+1 by omega,unitReduction] using hc.symm)

/-- The explicit bijection rewrites the literal sum over the unit fiber. -/
theorem sum_unit_fiber (p : ℕ) [Fact p.Prime] (h : ℕ) (hh : 1≤h)
    (u : (ZMod (p^(2*h+1)))ˣ) (f : (ZMod (p^(2*h+1)))ˣ → ℂ) :
    (∑ v ∈ Finset.univ.filter (fun v => unitReduction p h v=unitReduction p h u), f v) =
      ∑ z : ZMod (p^(h+1)), f (unitLift p h hh u z) := by
  rw [Finset.sum_subtype _ (p := fun v => unitReduction p h v=unitReduction p h u)
    (fun v => by simp)]
  exact (Equiv.sum_comp (unitFiberEquiv p h hh u) (fun v => f v.val)).symm

end NField.Alignment.OddPrimePowerUnitLifts

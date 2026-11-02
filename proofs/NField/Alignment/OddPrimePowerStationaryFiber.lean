/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.OddPrimePowerFiberGauss

/-!
# Stationary fiber norms with the arithmetic conditions discharged

The reduced stationary congruence supplies the derivative factor. A unit
inverse-phase coefficient supplies the nonzero prime-field quadratic
coefficient. Neither is left as an extra analytic assumption.
-/

set_option autoImplicit false
namespace NField.Alignment.OddPrimePowerStationaryFiber
open scoped BigOperators Classical
open SquareZeroUnitShift OddPrimePowerUnitLifts OddPrimePowerFiberGauss

/-- Zero under reduction means literal divisibility in the original ring. -/
theorem exists_factor_of_reduction_zero (m q : ℕ) [NeZero q] (hm : m∣q)
    (x : ZMod q) (hx : ZMod.castHom hm (ZMod m) x=0) :
    ∃ z : ZMod q, x=(m:ZMod q)*z := by
  rw [ZMod.castHom_apply,ZMod.cast_eq_val,CharP.cast_eq_zero_iff] at hx
  obtain ⟨z,hz⟩ := hx
  refine ⟨(z:ZMod q),?_⟩
  calc
    x = (x.val:ZMod q) := (ZMod.natCast_zmod_val x).symm
    _ = _ := by rw [hz,Nat.cast_mul]

/-- The ring reduction underlying the actual unit-fiber map. -/
def halfReduction (p h : ℕ) : ZMod (p^(2*h+1)) →+* ZMod (p^h) :=
  ZMod.castHom (Nat.pow_dvd_pow p (by omega : h≤2*h+1)) _

/-- The cleared stationary equation gives the required p^h derivative factor. -/
theorem stationary_derivative_factor (p : ℕ) [Fact p.Prime] (h : ℕ)
    (a b : ZMod (p^(2*h+1))) (u : (ZMod (p^(2*h+1)))ˣ)
    (hcrit : halfReduction p h a*(unitReduction p h u:ZMod (p^h))^2=
      halfReduction p h b) :
    ∃ ℓ : ZMod (p^(2*h+1)),
      a-b*((u⁻¹:(ZMod (p^(2*h+1)))ˣ):ZMod (p^(2*h+1)))^2=
        (p:ZMod (p^(2*h+1)))^h*ℓ := by
  have hc : halfReduction p h
      (a-b*((u⁻¹:(ZMod (p^(2*h+1)))ˣ):ZMod (p^(2*h+1)))^2)=0 := by
    have hz : (1:ZMod (p^h))*(halfReduction p h a*
        (unitReduction p h u:ZMod (p^h))^2-halfReduction p h b)=0 := by rw [hcrit]; ring
    have hd := (critical_iff (halfReduction p h a) (halfReduction p h b) 1
      (unitReduction p h u)).mpr hz
    rw [← map_inv] at hd
    simpa only [one_mul,map_sub,map_mul,map_pow,halfReduction,unitReduction,
      ZMod.unitsMap_val,ZMod.castHom_apply] using hd
  obtain ⟨ℓ,hℓ⟩ := exists_factor_of_reduction_zero (p^h) (p^(2*h+1)) _ _ hc
  exact ⟨ℓ,by simpa only [Nat.cast_pow] using hℓ⟩

/-- A unit phase coefficient remains nonzero in the prime-field quadratic term. -/
theorem quadratic_coefficient_ne_zero (p : ℕ) [Fact p.Prime] (h : ℕ)
    (b : ZMod (p^(2*h+1))) (hb : IsUnit b) (u : (ZMod (p^(2*h+1)))ˣ) :
    primeReduction p (2*h) (b*((u⁻¹:(ZMod (p^(2*h+1)))ˣ):ZMod (p^(2*h+1)))^3)≠0 := by
  exact (hb.mul ((u⁻¹).isUnit.pow 3)).map (primeReduction p (2*h)) |>.ne_zero

/-- The actual stationary fiber has exact norm p^h*sqrt(p) for odd p and
unit b; the reduced root equation discharges all auxiliary conditions. -/
theorem norm_stationary_fiber (p : ℕ) [Fact p.Prime] (hp : p≠2)
    (h : ℕ) (hh : 1≤h) (a b : ZMod (p^(2*h+1))) (hb : IsUnit b)
    (u : (ZMod (p^(2*h+1)))ˣ)
    (hcrit : halfReduction p h a*(unitReduction p h u:ZMod (p^h))^2=
      halfReduction p h b) :
    ‖∑ v ∈ Finset.univ.filter (fun v => unitReduction p h v=unitReduction p h u),
      ZMod.stdAddChar (phase a b v)‖ = (p:ℝ)^h*Real.sqrt p := by
  obtain ⟨ℓ,hℓ⟩ := stationary_derivative_factor p h a b u hcrit
  exact norm_unit_fiber p hp h hh a b ℓ u hℓ (quadratic_coefficient_ne_zero p h b hb u)

end NField.Alignment.OddPrimePowerStationaryFiber

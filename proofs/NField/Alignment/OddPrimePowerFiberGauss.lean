/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.OddPrimePowerUnitLifts
import NField.Alignment.ResidueReductionSum
import NField.Alignment.QuadraticAdditiveGauss

/-!
# Exact quadratic Gauss identification on odd-exponent unit fibers

An explicit factor of the stationary derivative gives the linear Gauss
coefficient. The actual additive lift parametrization and standard
character identity retain the exact multiplicity of the residual sum.
-/

set_option autoImplicit false
namespace NField.Alignment.OddPrimePowerFiberGauss
open scoped BigOperators Classical
open SquareZeroUnitShift OddPrimePowerUnitLifts ScaledResidueLift ResidueReductionSum
  QuadraticAdditiveGauss

/-- Reduction from a positive prime-power exponent to the prime field. -/
def primeReduction (p k : ℕ) : ZMod (p^(k+1)) →+* ZMod p :=
  ZMod.castHom (by simpa using Nat.pow_dvd_pow p (Nat.le_add_left 1 k)) _

/-- Each actual lifted phase is a fixed unit-modulus factor times the
literal quadratic standard character over the prime field. -/
theorem character_unitLift (p : ℕ) [Fact p.Prime] (h : ℕ) (hh : 1≤h)
    (a b ℓ : ZMod (p^(2*h+1))) (u : (ZMod (p^(2*h+1)))ˣ)
    (hder : a-b*((u⁻¹:(ZMod (p^(2*h+1)))ˣ):ZMod (p^(2*h+1)))^2=
      (p:ZMod (p^(2*h+1)))^h*ℓ) (z : ZMod (p^(h+1))) :
    ZMod.stdAddChar (phase a b (unitLift p h hh u z)) =
      ZMod.stdAddChar (phase a b u)*ZMod.stdAddChar
        (primeReduction p (2*h) (b*((u⁻¹:(ZMod (p^(2*h+1)))ˣ):ZMod (p^(2*h+1)))^3)*
          (primeReduction p h z)^2+primeReduction p (2*h) ℓ*primeReduction p h z) := by
  have he : phase a b (unitLift p h hh u z) = phase a b u+
      (p:ZMod (p^(2*h+1)))^(2*h)*
        ((b*((u⁻¹:(ZMod (p^(2*h+1)))ˣ):ZMod (p^(2*h+1)))^3)*(z.val:ZMod (p^(2*h+1)))^2+
          ℓ*(z.val:ZMod (p^(2*h+1)))) := by
    rw [unitLift,CubeZeroUnitShift.phase_shift,hder,delta_val]
    rw [show (p:ZMod (p^(2*h+1)))^(2*h)=((p:ZMod (p^(2*h+1)))^h)^2 by
      rw [← pow_mul]; congr 1; omega]
    ring
  rw [he,AddChar.map_add_eq_mul]
  congr 1
  have hq : p^(2*h)*p=p^(2*h+1) := (pow_succ p (2*h)).symm
  have hc := stdAddChar_scaled_phase (p^(2*h)) p (p^(2*h+1)) hq
    ((b*((u⁻¹:(ZMod (p^(2*h+1)))ˣ):ZMod (p^(2*h+1)))^3)*(z.val:ZMod (p^(2*h+1)))^2+
      ℓ*(z.val:ZMod (p^(2*h+1))))
  rw [Nat.cast_pow] at hc
  rw [hc]
  congr 1
  have hz : primeReduction p h z=(z.val:ZMod p) := by
    exact ZMod.cast_eq_val z
  rw [hz]
  simp only [map_add,map_mul,map_pow,map_natCast,primeReduction]

/-- The literal unit-fiber sum equals the prime-field quadratic Gauss
sum with the exact factor p^h and original constant phase. -/
theorem sum_unit_fiber_eq_gauss (p : ℕ) [Fact p.Prime] (h : ℕ) (hh : 1≤h)
    (a b ℓ : ZMod (p^(2*h+1))) (u : (ZMod (p^(2*h+1)))ˣ)
    (hder : a-b*((u⁻¹:(ZMod (p^(2*h+1)))ˣ):ZMod (p^(2*h+1)))^2=
      (p:ZMod (p^(2*h+1)))^h*ℓ) :
    (∑ v ∈ Finset.univ.filter (fun v => unitReduction p h v=unitReduction p h u),
      ZMod.stdAddChar (phase a b v)) =
      ZMod.stdAddChar (phase a b u)*(p:ℂ)^h*
        quadraticSum ZMod.stdAddChar
          (primeReduction p (2*h) (b*((u⁻¹:(ZMod (p^(2*h+1)))ˣ):ZMod (p^(2*h+1)))^3))
          (primeReduction p (2*h) ℓ) := by
  rw [sum_unit_fiber p h hh]
  simp_rw [character_unitLift p h hh a b ℓ u hder]
  rw [← Finset.mul_sum]
  have hs := sum_reduction (p^h) p (p^(h+1)) ((pow_succ p h).symm)
    (fun z : ZMod p => ZMod.stdAddChar
      (primeReduction p (2*h) (b*((u⁻¹:(ZMod (p^(2*h+1)))ˣ):ZMod (p^(2*h+1)))^3)*z^2+
        primeReduction p (2*h) ℓ*z))
  change (∑ z : ZMod (p^(h+1)), ZMod.stdAddChar
    (primeReduction p (2*h) (b*((u⁻¹:(ZMod (p^(2*h+1)))ˣ):ZMod (p^(2*h+1)))^3)*
      (primeReduction p h z)^2+primeReduction p (2*h) ℓ*primeReduction p h z)) = _ at hs
  rw [hs,Nat.cast_pow,mul_assoc]
  rfl

/-- A nonzero reduced quadratic coefficient gives the exact norm of the
actual stationary fiber, not merely a bound on an auxiliary Gauss sum. -/
theorem norm_unit_fiber (p : ℕ) [Fact p.Prime] (hp : p≠2) (h : ℕ) (hh : 1≤h)
    (a b ℓ : ZMod (p^(2*h+1))) (u : (ZMod (p^(2*h+1)))ˣ)
    (hder : a-b*((u⁻¹:(ZMod (p^(2*h+1)))ˣ):ZMod (p^(2*h+1)))^2=
      (p:ZMod (p^(2*h+1)))^h*ℓ)
    (hc : primeReduction p (2*h) (b*((u⁻¹:(ZMod (p^(2*h+1)))ˣ):ZMod (p^(2*h+1)))^3)≠0) :
    ‖∑ v ∈ Finset.univ.filter (fun v => unitReduction p h v=unitReduction p h u),
      ZMod.stdAddChar (phase a b v)‖ = (p:ℝ)^h*Real.sqrt p := by
  rw [sum_unit_fiber_eq_gauss p h hh a b ℓ u hder,norm_mul,norm_mul,
    AddChar.norm_apply,one_mul,norm_pow,Complex.norm_natCast,
    norm_prime_quadratic_sum p hp _ _ hc]

end NField.Alignment.OddPrimePowerFiberGauss

/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.OddPrimePowerStationaryFiber
import NField.Alignment.CyclicUnitQuadraticRoots

/-!
# Primitive odd-exponent Kloosterman bounds at odd primes

Actual stationary fibers have exact quadratic Gauss norm, and the
reduced quadratic has at most two unit roots. Their combination proves
the square-root estimate with no assumed prime-power cancellation.
-/

set_option autoImplicit false
namespace NField.Alignment.KloostermanOddPrimePowerBound
open scoped BigOperators Classical
open SquareZeroUnitShift UnitSumStationaryPhase KloostermanPrimePowerStationary
  OddPrimePowerUnitLifts OddPrimePowerStationaryFiber CyclicUnitQuadraticRoots
  InverseAdditiveCompletion

/-- Group the exact stationary sum into literal fibers over its reduced roots. -/
theorem unitSum_stationary_fibers (p : ℕ) [Fact p.Prime] (h : ℕ)
    (a b : ZMod (p^(2*h+1))) :
    unitSum ZMod.stdAddChar a b =
      ∑ v ∈ Finset.univ.filter (fun v : (ZMod (p^h))ˣ =>
        halfReduction p h a*(v:ZMod (p^h))^2=halfReduction p h b),
        ∑ u ∈ Finset.univ.filter (fun u => unitReduction p h u=v),
          ZMod.stdAddChar (phase a b u) := by
  let P := fun v : (ZMod (p^h))ˣ =>
    halfReduction p h a*(v:ZMod (p^h))^2=halfReduction p h b
  have hs := sum_eq_critical ZMod.stdAddChar
    (ZMod.isPrimitive_stdAddChar (p^(2*h+1))) a b
    ((p:ZMod (p^(2*h+1)))^(h+1)) (power_square_zero p (2*h+1) (h+1) (by omega))
  have hcancel (x : ZMod (p^(2*h+1))) :
      (p:ZMod (p^(2*h+1)))^(h+1)*x=0 ↔ halfReduction p h x=0 := by
    have hq : p^(h+1)*p^h=p^(2*h+1) := by rw [mul_comm]; exact half_product p h
    rw [← Nat.cast_pow,← ScaledResidueLift.scaledLift_reduction _ _ _ hq]
    change ScaledResidueLift.scaledLift _ _ _ hq (halfReduction p h x)=0 ↔ _
    constructor
    · intro hx
      apply ScaledResidueLift.scaledLift_injective _ _ _
        (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) hq
      simpa only [map_zero] using hx
    · intro hx
      rw [hx,map_zero]
  simp_rw [hcancel,map_sub,map_mul,map_pow,sub_eq_zero] at hs
  have hs' : unitSum ZMod.stdAddChar a b =
      ∑ u : (ZMod (p^(2*h+1)))ˣ,
        if P (unitReduction p h u) then ZMod.stdAddChar (phase a b u) else 0 := by
    rw [hs]
    apply Finset.sum_congr rfl
    intro u _
    congr 1
  rw [hs']
  have hf := Finset.sum_fiberwise_eq_sum_filter (Finset.univ : Finset (ZMod (p^(2*h+1)))ˣ)
    (Finset.univ.filter P) (unitReduction p h)
    (fun u => ZMod.stdAddChar (phase a b u))
  simpa only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.sum_filter] using hf.symm

/-- Summing at most two exact Gauss fiber norms bounds the actual unit sum. -/
theorem norm_unitSum_le (p : ℕ) [Fact p.Prime] (hp : p≠2)
    (h : ℕ) (hh : 1≤h) (a b : ZMod (p^(2*h+1))) (hb : IsUnit b) :
    ‖unitSum ZMod.stdAddChar a b‖ ≤ 2*((p:ℝ)^h*Real.sqrt p) := by
  rw [unitSum_stationary_fibers]
  let S := Finset.univ.filter (fun v : (ZMod (p^h))ˣ =>
    halfReduction p h a*(v:ZMod (p^h))^2=halfReduction p h b)
  have hn (v : (ZMod (p^h))ˣ) (hv : v∈S) :
      ‖∑ u ∈ Finset.univ.filter (fun u => unitReduction p h u=v),
        ZMod.stdAddChar (phase a b u)‖ = (p:ℝ)^h*Real.sqrt p := by
    obtain ⟨u,hu⟩ := ZMod.unitsMap_surjective (Nat.pow_dvd_pow p (by omega : h≤2*h+1)) v
    change unitReduction p h u=v at hu
    rw [← hu]
    apply norm_stationary_fiber p hp h hh a b hb u
    rw [hu]
    exact (Finset.mem_filter.mp hv).2
  have hc := odd_prime_power_quadratic_count p hp h
    (halfReduction p h a) (halfReduction p h b) (Or.inr (hb.map (halfReduction p h)))
  have hcR : (S.card:ℝ)≤2 := by exact_mod_cast hc
  calc
    _ ≤ ∑ v ∈ S, ‖∑ u ∈ Finset.univ.filter (fun u => unitReduction p h u=v),
        ZMod.stdAddChar (phase a b u)‖ := norm_sum_le _ _
    _ = (S.card:ℝ)*((p:ℝ)^h*Real.sqrt p) := by
      rw [Finset.sum_congr rfl hn,Finset.sum_const,nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcR (by positivity)

/-- The odd-exponent norm factor is exactly the square root of the modulus. -/
theorem odd_sqrt_factor (p h : ℕ) :
    (p:ℝ)^h*Real.sqrt p=Real.sqrt ((p^(2*h+1):ℕ):ℝ) := by
  rw [Nat.cast_pow,pow_succ,Real.sqrt_mul (pow_nonneg (Nat.cast_nonneg p) (2*h))]
  rw [show (p:ℝ)^(2*h)=((p:ℝ)^h)^2 by rw [← pow_mul]; congr 1; omega,
    Real.sqrt_sq (pow_nonneg (Nat.cast_nonneg p) h)]

/-- Primitive inverse phase gives the square-root bound at odd exponents >=3. -/
theorem odd_prime_power_bound (p : ℕ) [Fact p.Prime] (hp : p≠2)
    (h : ℕ) (hh : 1≤h) (r : ℕ) (j t : ZMod (p^(2*h+1))) (hb : IsUnit (j*r)) :
    ‖completeInverseSum r j t‖ ≤ 2*Real.sqrt ((p^(2*h+1):ℕ):ℝ) := by
  rw [complete_inverse_eq_unitSum]
  simpa only [odd_sqrt_factor] using norm_unitSum_le p hp h hh (-t) (j*r) hb

/-- Unit frequency and the manuscript coprimality cover every completion frequency. -/
theorem odd_prime_power_bound_unit_frequency (p : ℕ) [Fact p.Prime] (hp : p≠2)
    (h : ℕ) (hh : 1≤h) (r : ℕ) (j t : ZMod (p^(2*h+1)))
    (hr : r.Coprime (p^(2*h+1))) (hj : IsUnit j) :
    ‖completeInverseSum r j t‖ ≤ 2*Real.sqrt ((p^(2*h+1):ℕ):ℝ) :=
  odd_prime_power_bound p hp h hh r j t
    (hj.mul ((ZMod.isUnit_iff_coprime r (p^(2*h+1))).mpr hr))

end NField.Alignment.KloostermanOddPrimePowerBound

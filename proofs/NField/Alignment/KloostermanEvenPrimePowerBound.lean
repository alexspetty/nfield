/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CyclicUnitQuadraticRoots
import NField.Alignment.PrimePowerUnitFibers

/-!
# Primitive even-exponent Kloosterman bounds at odd primes

The exact stationary filter and lift multiplicity combine with the
proved two-root bound. This supplies the square-root estimate for even
exponents with at least one unit phase parameter. Odd exponents and
common nonunit content remain distinct obligations.
-/

set_option autoImplicit false
namespace NField.Alignment.KloostermanEvenPrimePowerBound
open scoped BigOperators Classical
open CyclicUnitQuadraticRoots KloostermanPrimePowerStationary PrimePowerUnitFibers
  InverseAdditiveCompletion

/-- At odd primes, a unit reduced phase parameter bounds the actual
stationary count by two and the complete sum by 2*p^s. -/
theorem odd_prime_power_stationary_bound (p : ℕ) [Fact p.Prime] (hp : p≠2)
    (k s : ℕ) (hs : s<k) (hk : k≤2*s) (r : ℕ) (j t : ZMod (p^k))
    (hab : IsUnit (reduction p k s (-t)) ∨ IsUnit (reduction p k s (j*r))) :
    ‖completeInverseSum r j t‖ ≤ 2*(p:ℝ)^s := by
  have h := complete_inverse_norm_le_reduced_count p k s hs hk r j t
  have hc := odd_prime_power_quadratic_count p hp (k-s)
    (reduction p k s (-t)) (reduction p k s (j*r)) hab
  have hcR : ((Finset.univ.filter (fun v : (ZMod (p^(k-s)))ˣ =>
      reduction p k s (-t)*(v:ZMod (p^(k-s)))^2=reduction p k s (j*r))).card:ℝ) ≤ 2 := by
    exact_mod_cast hc
  exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left hcR (pow_nonneg (Nat.cast_nonneg p) s)])

/-- Units remain units under the actual reduction map. No nonzero-to-unit
shortcut is used in the prime-power ring. -/
theorem odd_prime_power_stationary_bound_of_unit (p : ℕ) [Fact p.Prime] (hp : p≠2)
    (k s : ℕ) (hs : s<k) (hk : k≤2*s) (r : ℕ) (j t : ZMod (p^k))
    (hab : IsUnit (-t) ∨ IsUnit (j*r)) :
    ‖completeInverseSum r j t‖ ≤ 2*(p:ℝ)^s := by
  apply odd_prime_power_stationary_bound p hp k s hs hk r j t
  exact hab.elim (fun h => Or.inl (h.map (reduction p k s)))
    (fun h => Or.inr (h.map (reduction p k s)))

/-- The complete inverse sum at every positive even exponent of an odd
prime satisfies the square-root bound when at least one phase parameter
is a unit. -/
theorem even_prime_power_bound (p : ℕ) [Fact p.Prime] (hp : p≠2)
    (h : ℕ) (hh : 0<h) (r : ℕ) (j t : ZMod (p^(2*h)))
    (hab : IsUnit (-t) ∨ IsUnit (j*r)) :
    ‖completeInverseSum r j t‖ ≤ 2*Real.sqrt ((p^(2*h):ℕ):ℝ) := by
  have hb := odd_prime_power_stationary_bound_of_unit p hp (2*h) h (by omega)
    (by omega) r j t hab
  have hs : Real.sqrt ((p^(2*h):ℕ):ℝ)=(p:ℝ)^h := by
    rw [Nat.cast_pow,mul_comm 2 h,pow_mul,Real.sqrt_sq (pow_nonneg (Nat.cast_nonneg p) h)]
  rwa [hs]

/-- For the manuscript's coprime multiplier r, a unit frequency j is
enough; every completion frequency t, including zero, is covered. -/
theorem even_prime_power_bound_unit_frequency (p : ℕ) [Fact p.Prime] (hp : p≠2)
    (h : ℕ) (hh : 0<h) (r : ℕ) (j t : ZMod (p^(2*h)))
    (hr : r.Coprime (p^(2*h))) (hj : IsUnit j) :
    ‖completeInverseSum r j t‖ ≤ 2*Real.sqrt ((p^(2*h):ℕ):ℝ) := by
  apply even_prime_power_bound p hp h hh r j t
  exact Or.inr (hj.mul ((ZMod.isUnit_iff_coprime r (p^(2*h))).mpr hr))

/-- If exactly one reduced phase parameter is a unit, the stationary set
is empty and the original sum is zero, including characteristic two. -/
theorem complete_inverse_zero_of_reduced_unit_mismatch (p : ℕ) [Fact p.Prime]
    (k s : ℕ) (hs : s≤k) (hk : k≤2*s) (r : ℕ) (j t : ZMod (p^k))
    (hab : (IsUnit (reduction p k s (-t)) ∧ ¬IsUnit (reduction p k s (j*r))) ∨
      (¬IsUnit (reduction p k s (-t)) ∧ IsUnit (reduction p k s (j*r)))) :
    completeInverseSum r j t=0 := by
  rw [complete_inverse_stationary p k s hs hk r j t]
  apply Finset.sum_eq_zero
  intro u _
  apply if_neg
  have h := no_quadratic_units_of_unit_mismatch (reduction p k s (-t))
    (reduction p k s (j*r)) hab (ZMod.unitsMap (Nat.pow_dvd_pow p (Nat.sub_le k s)) u)
  simpa only [ZMod.unitsMap_val,reduction,ZMod.castHom_apply] using h

end NField.Alignment.KloostermanEvenPrimePowerBound

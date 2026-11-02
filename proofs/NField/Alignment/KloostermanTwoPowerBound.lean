/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.TwoPowerUnitQuadraticRoots
import NField.Alignment.PrimePowerUnitFibers

/-!
# Primitive complete inverse-sum bounds at powers of two

The uniform four-root count and half-exponent stationary filter suffice
at the fixed prime 2. The resulting absolute constant is independent of
the exponent; characteristic-two Gauss cancellation is not assumed.
-/

set_option autoImplicit false
namespace NField.Alignment.KloostermanTwoPowerBound
open scoped BigOperators Classical
open TwoPowerUnitQuadraticRoots KloostermanPrimePowerStationary PrimePowerUnitFibers
  InverseAdditiveCompletion

/-- The stationary root count gives an actual norm bound at powers of two. -/
theorem two_power_stationary_bound (k s : ℕ) (hs : s<k) (hk : k≤2*s)
    (r : ℕ) (j t : ZMod (2^k))
    (hab : IsUnit (reduction 2 k s (-t)) ∨ IsUnit (reduction 2 k s (j*r))) :
    ‖completeInverseSum r j t‖ ≤ 4*(2:ℝ)^s := by
  have hb := complete_inverse_norm_le_reduced_count 2 k s hs hk r j t
  norm_num only [Nat.cast_ofNat] at hb
  have hc := two_power_quadratic_count (k-s)
    (reduction 2 k s (-t)) (reduction 2 k s (j*r)) hab
  have hcR : ((Finset.univ.filter (fun v : (ZMod (2^(k-s)))ˣ =>
      reduction 2 k s (-t)*(v:ZMod (2^(k-s)))^2=reduction 2 k s (j*r))).card:ℝ)≤4 := by
    exact_mod_cast hc
  exact hb.trans (by nlinarith [mul_le_mul_of_nonneg_left hcR (by positivity : (0:ℝ)≤2^s)])

/-- The half-exponent loss is uniformly bounded at the fixed prime two. -/
theorem half_power_le_two_sqrt (k : ℕ) :
    (2:ℝ)^((k+1)/2) ≤ 2*Real.sqrt ((2^k:ℕ):ℝ) := by
  rw [Nat.cast_pow,Nat.cast_ofNat]
  have he : ((2:ℝ)^((k+1)/2))^2 ≤ (2:ℝ)^(k+1) := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  rw [pow_succ (2:ℝ) k] at he
  have hs := Real.sq_sqrt (by positivity : (0:ℝ)≤2^k)
  have hn := Real.sqrt_nonneg ((2:ℝ)^k)
  nlinarith [pow_pos (by norm_num : (0:ℝ)<2) k,
    pow_nonneg (by norm_num : (0:ℝ)≤2) ((k+1)/2)]

/-- The actual primitive complete sum modulo 2^k has a uniform square-root bound. -/
theorem two_power_bound (k : ℕ) (hk : 2≤k) (r : ℕ) (j t : ZMod (2^k))
    (hab : IsUnit (-t) ∨ IsUnit (j*r)) :
    ‖completeInverseSum r j t‖ ≤ 8*Real.sqrt ((2^k:ℕ):ℝ) := by
  have hb := two_power_stationary_bound k ((k+1)/2) (by omega) (by omega) r j t
    (hab.elim (fun h => Or.inl (h.map (reduction 2 k ((k+1)/2))))
      (fun h => Or.inr (h.map (reduction 2 k ((k+1)/2)))))
  have hs := half_power_le_two_sqrt k
  linarith

/-- Unit frequency and coprime r retain every completion frequency at powers of two. -/
theorem two_power_bound_unit_frequency (k : ℕ) (hk : 2≤k) (r : ℕ) (j t : ZMod (2^k))
    (hr : r.Coprime (2^k)) (hj : IsUnit j) :
    ‖completeInverseSum r j t‖ ≤ 8*Real.sqrt ((2^k:ℕ):ℝ) :=
  two_power_bound k hk r j t
    (Or.inr (hj.mul ((ZMod.isUnit_iff_coprime r (2^k)).mpr hr)))

end NField.Alignment.KloostermanTwoPowerBound

/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.UnitSumStationaryPhase
import NField.Alignment.InverseAdditiveCompletion

/-!
# Exact stationary congruence for the actual prime-power inverse sum

All parameters and zero completion frequency are retained. Square-zero
translation and primitive character orthogonality give an exact filter
through reduction to a smaller prime-power ring. No root-count or
square-root estimate is assumed or asserted here.
-/

set_option autoImplicit false
namespace NField.Alignment.KloostermanPrimePowerStationary
open scoped BigOperators Classical
open SquareZeroUnitShift UnitSumStationaryPhase InverseAdditiveCompletion

/-- The original completion sum is the literal unit sum with A=-t, B=j*r. -/
theorem complete_inverse_eq_unitSum {q : ℕ} [NeZero q]
    (r : ℕ) (j t : ZMod q) :
    completeInverseSum r j t = unitSum ZMod.stdAddChar (-t) (j*r) := by
  rw [complete_inverse_sum_eq_units]
  unfold unitSum
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  unfold phase
  ring

/-- The p^s increment has square zero modulo p^k whenever k<=2s. -/
theorem power_square_zero (p k s : ℕ) (hs : k≤2*s) :
    ((p : ZMod (p^k))^s)^2=0 := by
  rw [← pow_mul,← Nat.cast_pow]
  apply (CharP.cast_eq_zero_iff (ZMod (p^k)) (p^k) (p^(s*2))).mpr
  exact Nat.pow_dvd_pow p (by omega)

/-- The canonical reduction to modulus p^(k-s). -/
def reduction (p k s : ℕ) : ZMod (p^k) →+* ZMod (p^(k-s)) :=
  ZMod.castHom (Nat.pow_dvd_pow p (Nat.sub_le k s)) _

/-- Annihilation by p^s is exactly zero after reduction modulo p^(k-s). -/
theorem annihilator_iff_reduction_zero (p : ℕ) [Fact p.Prime]
    (k s : ℕ) (hs : s≤k) (x : ZMod (p^k)) :
    (p : ZMod (p^k))^s*x=0 ↔ reduction p k s x=0 := by
  have hx : (p : ZMod (p^k))^s*x=((p^s*x.val : ℕ):ZMod (p^k)) := by simp
  have hpows : p^k=p^s*p^(k-s) := by rw [← pow_add,Nat.add_sub_of_le hs]
  rw [hx,CharP.cast_eq_zero_iff]
  change p^k ∣ p^s*x.val ↔ (ZMod.castHom _ _ x)=0
  rw [ZMod.castHom_apply,ZMod.cast_eq_val,CharP.cast_eq_zero_iff]
  conv_lhs => lhs; rw [hpows]
  exact Nat.mul_dvd_mul_iff_left (pow_pos (Fact.out : p.Prime).pos s)

/-- The cleared critical equation is an exact quadratic congruence in
the smaller residue ring, with no invertibility requirement on a or b. -/
theorem critical_iff_reduced (p : ℕ) [Fact p.Prime]
    (k s : ℕ) (hs : s≤k) (a b : ZMod (p^k)) (u : (ZMod (p^k))ˣ) :
    (p : ZMod (p^k))^s*(a*(u:ZMod (p^k))^2-b)=0 ↔
      reduction p k s a*(reduction p k s (u:ZMod (p^k)))^2=reduction p k s b := by
  rw [annihilator_iff_reduction_zero p k s hs,map_sub,map_mul,map_pow,sub_eq_zero]

/-- Exact prime-power stationary-phase identity for the literal complete
inverse sum. The critical congruence is -t*u^2=j*r after reduction. -/
theorem complete_inverse_stationary (p : ℕ) [Fact p.Prime]
    (k s : ℕ) (hs : s≤k) (hk : k≤2*s) (r : ℕ) (j t : ZMod (p^k)) :
    completeInverseSum r j t =
      ∑ u : (ZMod (p^k))ˣ,
        if reduction p k s (-t)*(reduction p k s (u:ZMod (p^k)))^2=
            reduction p k s (j*r)
        then ZMod.stdAddChar (phase (-t) (j*r) u) else 0 := by
  rw [complete_inverse_eq_unitSum,
    sum_eq_critical _ (ZMod.isPrimitive_stdAddChar (p^k)) _ _ _ (power_square_zero p k s hk)]
  simp_rw [critical_iff_reduced p k s hs]

/-- The exact count of stationary units bounds the actual complete sum. -/
theorem complete_inverse_norm_le_critical_count (p : ℕ) [Fact p.Prime]
    (k s : ℕ) (hs : s≤k) (hk : k≤2*s) (r : ℕ) (j t : ZMod (p^k)) :
    ‖completeInverseSum r j t‖ ≤
      ((Finset.univ.filter (fun u : (ZMod (p^k))ˣ =>
        reduction p k s (-t)*(reduction p k s (u:ZMod (p^k)))^2=
          reduction p k s (j*r))).card:ℝ) := by
  rw [complete_inverse_eq_unitSum]
  have h := norm_le_critical_count ZMod.stdAddChar (ZMod.isPrimitive_stdAddChar (p^k))
    (-t) (j*r) ((p : ZMod (p^k))^s) (power_square_zero p k s hk)
  simpa only [critical_iff_reduced p k s hs] using h

/-- The automatic half-exponent choice discharges the square-zero and
reduction conditions for every nontrivial prime-power exponent. -/
theorem complete_inverse_half_stationary (p : ℕ) [Fact p.Prime]
    (k : ℕ) (hk : 1≤k) (r : ℕ) (j t : ZMod (p^k)) :
    completeInverseSum r j t =
      ∑ u : (ZMod (p^k))ˣ,
        if reduction p k ((k+1)/2) (-t)*(reduction p k ((k+1)/2) (u:ZMod (p^k)))^2=
            reduction p k ((k+1)/2) (j*r)
        then ZMod.stdAddChar (phase (-t) (j*r) u) else 0 :=
  complete_inverse_stationary p k ((k+1)/2) (by omega) (by omega) r j t

end NField.Alignment.KloostermanPrimePowerStationary

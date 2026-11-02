/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimitivePrimePowerBound
import NField.Alignment.ScaledResidueLift

/-!
# Exact common-content reduction for prime-power unit sums

A common prime-power factor in the phase is removed by the actual
standard-character identity and the exact multiplicity of unit
reduction. The result retains both parameters and zero frequencies.
-/

set_option autoImplicit false
namespace NField.Alignment.PrimePowerContentReduction
open scoped BigOperators Classical
open SquareZeroUnitShift UnitSumStationaryPhase ScaledResidueLift PrimePowerUnitFibers
  PrimitivePrimePowerBound

/-- Actual reduction of the residue ring to a smaller prime-power modulus. -/
def ringReduction (p k m : ℕ) (hmk : m≤k) : ZMod (p^k) →+* ZMod (p^m) :=
  ZMod.castHom (Nat.pow_dvd_pow p hmk) _

/-- Actual reduction of units to the smaller prime-power modulus. -/
def unitReduction (p k m : ℕ) (hmk : m≤k) : (ZMod (p^k))ˣ →* (ZMod (p^m))ˣ :=
  ZMod.unitsMap (Nat.pow_dvd_pow p hmk)

/-- Pulling a unit sum back under reduction gives exactly p^(k-m) copies. -/
theorem sum_unit_reduction (p : ℕ) [Fact p.Prime] (k m : ℕ)
    (hm : 1 ≤ m) (hmk : m≤k) (f : (ZMod (p^m))ˣ → ℂ) :
    (∑ u : (ZMod (p^k))ˣ, f (unitReduction p k m hmk u)) =
      (p:ℂ)^(k-m)*∑ v : (ZMod (p^m))ˣ, f v := by
  let r := unitReduction p k m hmk
  have hs := Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ) (t := Finset.univ) (g := r)
    (fun _ _ => Finset.mem_univ _) (fun u => f (r u))
  rw [← hs,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  calc
    _ = ∑ _u ∈ Finset.univ.filter (fun u : (ZMod (p^k))ˣ => r u=v), f v := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [(Finset.mem_filter.mp hu).2]
    _ = (p:ℂ)^(k-m)*f v := by
      rw [Finset.sum_const,nsmul_eq_mul]
      change ((Finset.univ.filter (fun u => ZMod.unitsMap (Nat.pow_dvd_pow p hmk) u=v)).card:ℂ)*f v=_
      rw [card_unit_fiber p k m hm hmk v,Nat.cast_pow]

/-- Ring reduction of the actual phase is the phase of the reduced unit and parameters. -/
theorem phase_reduction (p k m : ℕ) (hmk : m≤k)
    (a b : ZMod (p^k)) (u : (ZMod (p^k))ˣ) :
    ringReduction p k m hmk (phase a b u)=
      phase (ringReduction p k m hmk a) (ringReduction p k m hmk b)
        (unitReduction p k m hmk u) := by
  simp only [phase,map_add,map_mul]
  rw [← map_inv]
  rfl

/-- Removing a common phase factor gives exactly the smaller standard character. -/
theorem character_scaled_phase (p : ℕ) [Fact p.Prime] (k m : ℕ) (hmk : m≤k)
    (a b : ZMod (p^k)) (u : (ZMod (p^k))ˣ) :
    ZMod.stdAddChar (phase ((p:ZMod (p^k))^(k-m)*a) ((p:ZMod (p^k))^(k-m)*b) u)=
      ZMod.stdAddChar (phase (ringReduction p k m hmk a) (ringReduction p k m hmk b)
        (unitReduction p k m hmk u)) := by
  have hq : p^(k-m)*p^m=p^k := by rw [← pow_add,Nat.sub_add_cancel hmk]
  have he : phase ((p:ZMod (p^k))^(k-m)*a) ((p:ZMod (p^k))^(k-m)*b) u=
      (p:ZMod (p^k))^(k-m)*phase a b u := by unfold phase; ring
  rw [he,← Nat.cast_pow,stdAddChar_scaled_phase _ _ _ hq]
  change ZMod.stdAddChar (ringReduction p k m hmk (phase a b u))=_
  rw [phase_reduction]

/-- Exact common-content reduction for the actual unit exponential sum. -/
theorem unitSum_content_reduction (p : ℕ) [Fact p.Prime] (k m : ℕ)
    (hm : 1 ≤ m) (hmk : m≤k) (a b : ZMod (p^k)) :
    unitSum ZMod.stdAddChar ((p:ZMod (p^k))^(k-m)*a) ((p:ZMod (p^k))^(k-m)*b)=
      (p:ℂ)^(k-m)*unitSum ZMod.stdAddChar
        (ringReduction p k m hmk a) (ringReduction p k m hmk b) := by
  unfold unitSum
  simp_rw [character_scaled_phase p k m hmk]
  exact sum_unit_reduction p k m hm hmk
    (fun u => ZMod.stdAddChar (phase (ringReduction p k m hmk a) (ringReduction p k m hmk b) u))

/-- The exact content multiplicity also factors out of the norm. -/
theorem norm_content_reduction (p : ℕ) [Fact p.Prime] (k m : ℕ)
    (hm : 1 ≤ m) (hmk : m≤k) (a b : ZMod (p^k)) :
    ‖unitSum ZMod.stdAddChar ((p:ZMod (p^k))^(k-m)*a) ((p:ZMod (p^k))^(k-m)*b)‖=
      (p:ℝ)^(k-m)*‖unitSum ZMod.stdAddChar
        (ringReduction p k m hmk a) (ringReduction p k m hmk b)‖ := by
  rw [unitSum_content_reduction p k m hm hmk,norm_mul,norm_pow,Complex.norm_natCast]

/-- Exact content extraction plus the proved primitive estimate bounds the actual sum. -/
theorem content_bound (p : ℕ) [Fact p.Prime] (k m : ℕ)
    (hm : 1 ≤ m) (hmk : m≤k) (a b : ZMod (p^k))
    (hab : IsUnit (ringReduction p k m hmk a) ∨ IsUnit (ringReduction p k m hmk b)) :
    ‖unitSum ZMod.stdAddChar ((p:ZMod (p^k))^(k-m)*a) ((p:ZMod (p^k))^(k-m)*b)‖≤
      (p:ℝ)^(k-m)*((if p=2 then 8 else 2)*Real.sqrt ((p^m:ℕ):ℝ)) := by
  rw [norm_content_reduction p k m hm hmk]
  exact mul_le_mul_of_nonneg_left
    (prime_power_unitSum_bound p m hm _ _ hab) (by positivity)

/-- The extracted-content norm factor has exactly the expected square-root form. -/
theorem sqrt_content_factor (p k m : ℕ) (hmk : m≤k) :
    (p:ℝ)^(k-m)*Real.sqrt ((p^m:ℕ):ℝ)=
      Real.sqrt ((p^k:ℕ):ℝ)*Real.sqrt ((p^(k-m):ℕ):ℝ) := by
  simp only [Nat.cast_pow]
  have he : (p:ℝ)^k=(p:ℝ)^(k-m)*(p:ℝ)^m := by
    rw [← pow_add,Nat.sub_add_cancel hmk]
  rw [he,Real.sqrt_mul (pow_nonneg (Nat.cast_nonneg p) (k-m))]
  have hs := Real.mul_self_sqrt (pow_nonneg (Nat.cast_nonneg p) (k-m))
  nlinarith [congrArg (fun x : ℝ => x*Real.sqrt ((p:ℝ)^m)) hs]

/-- A specified common factor with primitive residual phase gives the full local square-root shape. -/
theorem content_bound_sqrt (p : ℕ) [Fact p.Prime] (k m : ℕ)
    (hm : 1 ≤ m) (hmk : m≤k) (a b : ZMod (p^k))
    (hab : IsUnit (ringReduction p k m hmk a) ∨ IsUnit (ringReduction p k m hmk b)) :
    ‖unitSum ZMod.stdAddChar ((p:ZMod (p^k))^(k-m)*a) ((p:ZMod (p^k))^(k-m)*b)‖≤
      (if p=2 then 8 else 2)*Real.sqrt ((p^k:ℕ):ℝ)*Real.sqrt ((p^(k-m):ℕ):ℝ) := by
  have hb := content_bound p k m hm hmk a b hab
  calc
    _ ≤ (p:ℝ)^(k-m)*((if p=2 then 8 else 2)*Real.sqrt ((p^m:ℕ):ℝ)) := hb
    _ = (if p=2 then 8 else 2)*((p:ℝ)^(k-m)*Real.sqrt ((p^m:ℕ):ℝ)) := by ring
    _ = _ := by rw [sqrt_content_factor p k m hmk,mul_assoc]

end NField.Alignment.PrimePowerContentReduction

/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionPrimeLimits

/-! # Prime limits expressed through the intrinsic digit-collision count -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000

namespace NField.Alignment.CollisionPrimeLimits

open Filter Finset
open scoped BigOperators Topology
open NField.Alignment.PrimePeriodicLimits
open NField.Alignment.CollisionTransform
open NField.Alignment.CollisionTransformStrip
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionFluctuationSum
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.CenteredCollisionClosure
open NField.Alignment.NeutralityTheorem

theorem unit_table_eq_direct_deviation
    {b ell n : ℕ} [NeZero (allLagModulus b ell)] (hb : 2 ≤ b) (hell : 1 ≤ ell)
    (hunit : IsUnit (n : ZMod (allLagModulus b ell))) :
    allLagUnitTable b ell hunit.unit = (directAllLagDeviation b ell n : ℂ) := by
  let q := allLagModulus b ell
  have hq2 : 1 < q := Nat.one_lt_pow (by omega) (by omega)
  have hcop : n.Coprime q := (ZMod.isUnit_iff_coprime n q).mp hunit
  have hmod : (n % q).Coprime q := (ZMod.coprime_mod_iff_coprime n q).mpr hcop
  have ha : 1 ≤ n % q := by
    by_contra h
    have hz : n % q = 0 := by omega
    rw [hz] at hmod
    simp only [Nat.coprime_zero_left] at hmod
    omega
  have halt : n % q < q := Nat.mod_lt n (by omega)
  have hrep : n = q * (n / q) + n % q := by
    have h := Nat.mod_add_div n q
    omega
  have ht := directAllLagDeviation_eq_allLagTable (t := n / q) hb hell ha halt hmod
  change directAllLagDeviation b ell (q * (n / q) + n % q) = _ at ht
  rw [← hrep] at ht
  unfold allLagUnitTable
  rw [hunit.unit_spec, ZMod.val_natCast]
  exact_mod_cast ht.symm

def directCenteredCollisionValue (b ell : ℕ) [NeZero b] [NeZero (allLagModulus b ell)]
    (n : ℕ) : ℂ :=
  if h : IsUnit (n : ZMod (allLagModulus b ell)) then
    (directAllLagDeviation b ell n : ℂ) -
      fiberMean (coarseUnitReduction b ell) (allLagUnitTable b ell)
        (coarseUnitReduction b ell h.unit)
  else 0

theorem directCenteredCollisionValue_eq_unitExtension
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb : 2 ≤ b) (hell : 1 ≤ ell) (n : ℕ) :
    directCenteredCollisionValue b ell n = unitExtension (centeredCollisionTransform b ell) n := by
  by_cases h : IsUnit (n : ZMod (allLagModulus b ell))
  · simp only [directCenteredCollisionValue, unitExtension, dif_pos h,
      centeredCollisionTransform, centeredSignal, unit_table_eq_direct_deviation hb hell h]
  · simp only [directCenteredCollisionValue, unitExtension, dif_neg h]

/-- Title: `Direct centered collision harmonic limit`.
The summands use the literal digit-collision count and its coarse-fiber mean.
Primes not coprime to the base are excluded by the explicit zero extension. -/
theorem direct_centered_collision_harmonic_limit
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb : 2 ≤ b) (hell : 1 ≤ ell) :
    ∃ L : ℂ, Tendsto (fun x : ℝ =>
      ∑ p ∈ Finset.Ioc 0 ⌊x⌋₊,
        if p.Prime then directCenteredCollisionValue b ell p / (p : ℂ) else 0)
      atTop (𝓝 L) := by
  obtain ⟨L, hL⟩ := centered_collision_prime_reciprocal_limit (b := b) (ell := ell)
  refine ⟨L, hL.congr' (Filter.Eventually.of_forall ?_)⟩
  intro x
  unfold weightedPrimeReciprocalSum
  apply Finset.sum_congr rfl
  intro p _
  rw [directCenteredCollisionValue_eq_unitExtension hb hell]

/-- Title: `Direct centered collision prime count limit`. -/
theorem direct_centered_collision_prime_count_limit
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb : 2 ≤ b) (hell : 1 ≤ ell) :
    Tendsto (fun x : ℝ =>
      (∑ p ∈ Finset.Ioc 0 ⌊x⌋₊, if p.Prime then directCenteredCollisionValue b ell p else 0) /
        (x / Real.log x : ℝ)) atTop (𝓝 0) := by
  apply (centered_collision_prime_count_limit (b := b) (ell := ell)).congr'
  apply Filter.Eventually.of_forall
  intro x
  unfold weightedPrimeCountSum
  apply congrArg (fun z : ℂ => z / (x / Real.log x : ℝ))
  apply Finset.sum_congr rfl
  intro p _
  rw [directCenteredCollisionValue_eq_unitExtension hb hell]

end NField.Alignment.CollisionPrimeLimits

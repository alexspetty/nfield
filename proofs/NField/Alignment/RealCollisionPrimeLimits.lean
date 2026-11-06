/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.DirectCollisionPrimeLimits
import NField.Alignment.PrimeFiniteCutoffs

/-! # The real centered collision limits with the manuscript's cutoff -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000

namespace NField.Alignment.CollisionPrimeLimits

open Filter Finset
open scoped BigOperators Topology
open NField.Alignment.PrimePeriodicLimits
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.NeutralityTheorem
open NField.Alignment.CollisionTransformStrip

def realUnitCollisionTable (b ell : ℕ) [NeZero (allLagModulus b ell)]
    (u : UnitClass (allLagModulus b ell)) : ℝ := allLagTable b ell u.val.val

theorem ofReal_fiberMean {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (ρ : α → β) (T : α → ℝ) (u : β) :
    ((fiberMean ρ T u : ℝ) : ℂ) = fiberMean ρ (fun a => (T a : ℂ)) u := by
  simp only [fiberMean, Complex.ofReal_mul, Complex.ofReal_inv,
    Complex.ofReal_natCast, Complex.ofReal_sum]

def realDirectCenteredCollisionValue (b ell : ℕ) [NeZero b]
    [NeZero (allLagModulus b ell)] (n : ℕ) : ℝ :=
  if h : IsUnit (n : ZMod (allLagModulus b ell)) then
    (directAllLagDeviation b ell n : ℝ) -
      fiberMean (coarseUnitReduction b ell) (realUnitCollisionTable b ell)
        (coarseUnitReduction b ell h.unit)
  else 0

theorem ofReal_realDirectCenteredCollisionValue {b ell : ℕ} [NeZero b]
    [NeZero (allLagModulus b ell)] (n : ℕ) :
    (realDirectCenteredCollisionValue b ell n : ℂ) = directCenteredCollisionValue b ell n := by
  by_cases h : IsUnit (n : ZMod (allLagModulus b ell))
  · simp only [realDirectCenteredCollisionValue, directCenteredCollisionValue, dif_pos h,
      Complex.ofReal_sub, Complex.ofReal_intCast, ofReal_fiberMean,
      realUnitCollisionTable, allLagUnitTable]
    rfl
  · simp only [realDirectCenteredCollisionValue, directCenteredCollisionValue, dif_neg h,
      Complex.ofReal_zero]

def realPrimeTailSum (F : ℕ → ℝ) (c : ℕ) (x : ℝ) : ℝ :=
  ∑ p ∈ Finset.Ioc c ⌊x⌋₊, if p.Prime then F p else 0

theorem ofReal_realPrimeTailSum (F : ℕ → ℝ) (c : ℕ) (x : ℝ) :
    (realPrimeTailSum F c x : ℂ) =
      ∑ p ∈ Finset.Ioc c ⌊x⌋₊, if p.Prime then (F p : ℂ) else 0 := by
  simp only [realPrimeTailSum, Complex.ofReal_sum, apply_ite, Complex.ofReal_zero]

/-- Title: `Real centered harmonic limit at the manuscript cutoff`. -/
theorem real_centered_collision_harmonic_limit
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb : 2 ≤ b) (hell : 1 ≤ ell) :
    ∃ K : ℝ, Tendsto
      (realPrimeTailSum (fun p => realDirectCenteredCollisionValue b ell p / p)
        (allLagModulus b ell)) atTop (𝓝 K) := by
  obtain ⟨L, hL⟩ := direct_centered_collision_harmonic_limit hb hell
  have ht := sum_Ioc_cutoff_limit
    (fun p => if p.Prime then directCenteredCollisionValue b ell p / (p : ℂ) else 0)
    (allLagModulus b ell) hL
  have hcast (x : ℝ) :
      (realPrimeTailSum (fun p => realDirectCenteredCollisionValue b ell p / p)
        (allLagModulus b ell) x : ℂ) =
      ∑ p ∈ Finset.Ioc (allLagModulus b ell) ⌊x⌋₊,
        if p.Prime then directCenteredCollisionValue b ell p / (p : ℂ) else 0 := by
    simp only [ofReal_realPrimeTailSum, Complex.ofReal_div,
      ofReal_realDirectCenteredCollisionValue, Complex.ofReal_natCast]
  have hr := Complex.continuous_re.continuousAt.tendsto.comp ht
  refine ⟨(L - ∑ n ∈ Finset.Ioc 0 (allLagModulus b ell),
    if n.Prime then directCenteredCollisionValue b ell n / (n : ℂ) else 0).re, ?_⟩
  apply hr.congr'
  apply Filter.Eventually.of_forall
  intro x
  change (∑ p ∈ Finset.Ioc (allLagModulus b ell) ⌊x⌋₊,
    if p.Prime then directCenteredCollisionValue b ell p / (p : ℂ) else 0).re = _
  rw [← hcast, Complex.ofReal_re]

/-- Title: `Real centered prime sum divided by the prime count`. -/
theorem real_centered_collision_prime_pi_limit
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb : 2 ≤ b) (hell : 1 ≤ ell) :
    Tendsto (fun x : ℝ =>
      realPrimeTailSum (realDirectCenteredCollisionValue b ell) (allLagModulus b ell) x /
        (Nat.primeCounting ⌊x⌋₊ : ℝ)) atTop (𝓝 0) := by
  have ht := sum_Ioc_cutoff_pi_limit
    (fun p => if p.Prime then directCenteredCollisionValue b ell p else 0)
    (allLagModulus b ell)
    (prime_count_zero_normalized_by_pi (direct_centered_collision_prime_count_limit hb hell))
  have hcast (x : ℝ) :
      (realPrimeTailSum (realDirectCenteredCollisionValue b ell) (allLagModulus b ell) x : ℂ) =
      ∑ p ∈ Finset.Ioc (allLagModulus b ell) ⌊x⌋₊,
        if p.Prime then directCenteredCollisionValue b ell p else 0 := by
    simp only [ofReal_realPrimeTailSum, ofReal_realDirectCenteredCollisionValue]
  have hr : Tendsto (fun x : ℝ =>
      ((∑ p ∈ Finset.Ioc (allLagModulus b ell) ⌊x⌋₊,
        if p.Prime then directCenteredCollisionValue b ell p else 0) /
          (Nat.primeCounting ⌊x⌋₊ : ℂ)).re) atTop (𝓝 0) :=
    Complex.continuous_re.continuousAt.tendsto.comp ht
  apply hr.congr'
  apply Filter.Eventually.of_forall
  intro x
  dsimp only
  rw [← hcast, ← Complex.ofReal_natCast, ← Complex.ofReal_div, Complex.ofReal_re]

/-- Title: `Centered prime sum is little o of the prime count`. -/
theorem real_centered_collision_prime_littleO
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb : 2 ≤ b) (hell : 1 ≤ ell) :
    Asymptotics.IsLittleO atTop
      (realPrimeTailSum (realDirectCenteredCollisionValue b ell) (allLagModulus b ell))
      (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ)) := by
  apply (Asymptotics.isLittleO_iff_tendsto ?_).mpr
    (real_centered_collision_prime_pi_limit hb hell)
  intro x hx
  have hsmall : ⌊x⌋₊ ≤ 1 := Nat.primeCounting_eq_zero_iff.mp (by exact_mod_cast hx)
  apply Finset.sum_eq_zero
  intro p hp
  have hp_le : p ≤ 1 := (Finset.mem_Ioc.mp hp).2.trans hsmall
  have hnp : ¬p.Prime := fun hp => by have := hp.two_le; omega
  simp only [hnp, ↓reduceIte]

end NField.Alignment.CollisionPrimeLimits

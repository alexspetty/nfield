/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimePeriodicCounting
import NField.Alignment.GeneralNeutrality
import NField.Alignment.CenteredCollisionClosure

/-!
# Unconditional prime limits for the actual collision table and its channels

The existing finite table, centering map and CRT channels are used directly.
The analytic inputs are now proved by the fixed-modulus progression theorems.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionPrimeLimits

open Filter Finset
open scoped BigOperators Topology
open NField.Alignment.PrimePeriodicLimits
open NField.Alignment.CollisionTransform
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionFluctuationSum
open NField.Alignment.CollisionTransformStrip
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.CenteredCollisionClosure
open NField.Alignment.NeutralityTheorem
open NField.Alignment.GeneralNeutrality

/-- Title: `Centered collision reciprocal prime convergence`.
The weights are the manuscript's actual all-lag naturally centered table. -/
theorem centered_collision_prime_reciprocal_limit
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)] :
    ∃ L : ℂ, Tendsto (weightedPrimeReciprocalSum (centeredCollisionTransform b ell))
      atTop (𝓝 L) :=
  centered_periodic_prime_reciprocal_limit _ centeredCollisionTransform_sum_zero

/-- Title: `Centered collision ordinary prime limit`. -/
theorem centered_collision_prime_count_limit
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)] :
    Tendsto (fun x : ℝ => weightedPrimeCountSum (centeredCollisionTransform b ell) x /
      (x / Real.log x : ℝ)) atTop (𝓝 0) :=
  centered_periodic_prime_count_limit _ centeredCollisionTransform_sum_zero

/-- The raw table has mean exactly `-1/2`, so its logarithmic drift is literal. -/
theorem raw_collision_prime_reciprocal_drift
    {b ell : ℕ} [NeZero (allLagModulus b ell)] (hb : 2 ≤ b) (hell : 1 ≤ ell) :
    ∃ L : ℂ, Tendsto (fun x : ℝ => weightedPrimeReciprocalSum (allLagUnitTable b ell) x +
      (1 / 2 : ℂ) * (Real.log (Real.log x) : ℂ)) atTop (𝓝 L) := by
  have hmean := allLagUnitTable_grand_mean hb hell
  rw [ZMod.card_units_eq_totient] at hmean
  obtain ⟨L, hL⟩ := periodic_prime_reciprocal_residual_limit (allLagUnitTable b ell)
  refine ⟨L, ?_⟩
  simpa only [hmean, neg_div, neg_mul, sub_neg_eq_add] using hL

def restrictedUnitSignal {q : ℕ} (f : UnitClass q → ℂ)
    (P : UnitClass q → Prop) [DecidablePred P] : UnitClass q → ℂ :=
  fun a => if P a then f a else 0

theorem restrictedUnitSignal_sum {q : ℕ} [NeZero q] (f : UnitClass q → ℂ)
    (P : UnitClass q → Prop) [DecidablePred P] [Fintype (Subtype P)] :
    (∑ a, restrictedUnitSignal f P a) = ∑ a : Subtype P, f a.val := by
  classical
  simp only [restrictedUnitSignal]
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) f

theorem neutral_restricted_channel_converges {q : ℕ} [NeZero q]
    (f : UnitClass q → ℂ) (P : UnitClass q → Prop) [DecidablePred P]
    [Fintype (Subtype P)] (hzero : ∑ a : Subtype P, f a.val = 0) :
    ∃ L : ℂ, Tendsto (weightedPrimeReciprocalSum (restrictedUnitSignal f P))
      atTop (𝓝 L) := by
  apply centered_periodic_prime_reciprocal_limit
  rw [restrictedUnitSignal_sum]
  exact hzero

/-- Each actual CRT channel is independently convergent, with no Mertens premise. -/
theorem coprime_true_channel_prime_limit
    {m q : ℕ} [NeZero m] [NeZero q] [NeZero (m * q)]
    (hcop : m.Coprime q) (r : UnitClass q)
    {β : Type*} [Fintype β] [DecidableEq β]
    (ρ : UnitClass m → β) (T : UnitClass m → ℂ) (hsurj : Function.Surjective ρ) :
    ∃ L : ℂ, Tendsto (weightedPrimeReciprocalSum
      (restrictedUnitSignal
        (fun A : UnitClass (m * q) => centeredSignal ρ T ((generalCrtUnitEquiv hcop A).1))
        (fun A => (generalCrtUnitEquiv hcop A).2 = r))) atTop (𝓝 L) := by
  apply neutral_restricted_channel_converges
  exact generalCarryChannel_centered_sum_zero hcop r ρ T hsurj

/-- Simultaneous squarefree true channels use the actual generalized CRT fiber. -/
theorem squarefree_true_channel_prime_limit
    {b ell Q : ℕ} [NeZero b] [NeZero Q] [NeZero (allLagModulus b ell)]
    [NeZero (Nat.lcm (allLagModulus b ell) Q)]
    [NeZero (Nat.gcd (allLagModulus b ell) Q)]
    (hQ : Squarefree Q) (r : UnitClass Q) :
    ∃ L : ℂ, Tendsto (weightedPrimeReciprocalSum
      (restrictedUnitSignal
        (fun A : UnitClass (Nat.lcm (allLagModulus b ell) Q) =>
          centeredSignal (coarseUnitReduction b ell) (allLagUnitTable b ell)
            (unitReduction (Nat.dvd_lcm_left (allLagModulus b ell) Q) A))
        (fun A => unitReduction (Nat.dvd_lcm_right (allLagModulus b ell) Q) A = r)))
      atTop (𝓝 L) := by
  apply neutral_restricted_channel_converges
  exact simultaneous_squarefree_channel_neutral hQ r

end NField.Alignment.CollisionPrimeLimits

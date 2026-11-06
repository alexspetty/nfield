/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionHolomorphicContinuation
import NField.Alignment.PrimeHigherPowers
import NField.Alignment.EulerLogNormalization

/-! # Analytic statements for the intrinsic centered collision prime series -/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionPrimeAnalyticModel

open scoped BigOperators Topology
open Filter Set
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionTransform
open NField.Alignment.CollisionTransformStrip
open NField.Alignment.CollisionPrimeLimits
open NField.Alignment.ComplexPrimeCharacterExpansion
open NField.Alignment.CollisionHolomorphicContinuation
open NField.Alignment.PrimeEulerLog

def directSeries (b ell : ℕ) [NeZero b] [NeZero (allLagModulus b ell)] (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, if allLagModulus b ell < (p : ℕ) then
    directCenteredCollisionValue b ell p / (p : ℂ) ^ s else 0

theorem directSeries_eq_periodicPrimeSeries {b ell : ℕ}
    [NeZero b] [NeZero (allLagModulus b ell)]
    (hb : 2 ≤ b) (hell : 1 ≤ ell) (s : ℂ) :
    directSeries b ell s =
      periodicPrimeSeries (centeredCollisionTransform b ell) (allLagModulus b ell) s := by
  unfold directSeries periodicPrimeSeries
  apply tsum_congr
  intro p
  simp only [directCenteredCollisionValue_eq_unitExtension hb hell, periodicPrimeTerm,
    Complex.cpow_neg, div_eq_mul_inv]

/-- Title: `The intrinsic collision prime series converges absolutely to the right of one`. -/
theorem directSeries_summable {b ell : ℕ}
    [NeZero b] [NeZero (allLagModulus b ell)]
    (hb : 2 ≤ b) (hell : 1 ≤ ell) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : Nat.Primes => if allLagModulus b ell < (p : ℕ) then
      directCenteredCollisionValue b ell p / (p : ℂ) ^ s else 0) := by
  simpa only [directCenteredCollisionValue_eq_unitExtension hb hell, periodicPrimeTerm,
    Complex.cpow_neg, div_eq_mul_inv] using
      periodicPrimeSeries_summable (centeredCollisionTransform b ell) (allLagModulus b ell) hs

theorem centered_principal_coefficient_zero {b ell : ℕ}
    [NeZero b] [NeZero (allLagModulus b ell)] (hb : 2 ≤ b) (hell : 1 ≤ ell) :
    collisionCoefficient (centeredCollisionTransform b ell) 1 = 0 := by
  apply centeredCollisionTransform_even_zero hb hell
  exact MulChar.one_apply isUnit_neg_one

/-- Title: `The intrinsic collision prime series has the exact Euler-product decomposition`. -/
theorem directSeries_euler_expansion {b ell : ℕ}
    [NeZero b] [NeZero (allLagModulus b ell)]
    (hb : 2 ≤ b) (hell : 1 ≤ ell) {s : ℂ} (hs : 1 < s.re) :
    directSeries b ell s =
      (∑ χ ∈ activeCharacters (centeredCollisionTransform b ell),
        collisionCoefficient (centeredCollisionTransform b ell) χ * eulerLog χ s) -
      (∑ χ ∈ activeCharacters (centeredCollisionTransform b ell),
        collisionCoefficient (centeredCollisionTransform b ell) χ * higherPowerSum χ s) -
      finiteCorrection (centeredCollisionTransform b ell) (allLagModulus b ell) s := by
  rw [directSeries_eq_periodicPrimeSeries hb hell]
  exact periodicPrimeSeries_euler_expansion _ _ hs

/-- Title: `The intrinsic collision prime series continues on every permitted active zero-free domain`. -/
theorem directSeries_continuation {b ell : ℕ}
    [NeZero b] [NeZero (allLagModulus b ell)]
    (hb : 2 ≤ b) (hell : 1 ≤ ell)
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsSimplyConnected U)
    (hhalf : U ⊆ {s : ℂ | (1 / 2 : ℝ) < s.re})
    (hconnected : IsPreconnected (U ∩ {s : ℂ | 1 < s.re}))
    (hmeets : (U ∩ {s : ℂ | 1 < s.re}).Nonempty)
    (hzero : ∀ χ ∈ activeCharacters (centeredCollisionTransform b ell),
      ∀ s ∈ U, χ.LFunction s ≠ 0) :
    ∃ T : ℂ → ℂ, AnalyticOnNhd ℂ T U ∧
      EqOn T (directSeries b ell) (U ∩ {s : ℂ | 1 < s.re}) := by
  obtain ⟨T, hT, heq⟩ := exists_collision_continuation (centeredCollisionTransform b ell)
    (allLagModulus b ell) (centered_principal_coefficient_zero hb hell)
    hU hUc hhalf hconnected hmeets hzero
  refine ⟨T, hT, ?_⟩
  intro s hs
  rw [directSeries_eq_periodicPrimeSeries hb hell]
  exact heq hs

/-- Title: `The actual collision reciprocal-prime boundary has an ordinary ordered limit`. -/
theorem direct_harmonic_boundary {b ell : ℕ}
    [NeZero b] [NeZero (allLagModulus b ell)]
    (hb : 2 ≤ b) (hell : 1 ≤ ell) :
    ∃ K : ℝ, Tendsto (fun x : ℝ =>
      ∑ p ∈ Finset.Ioc (allLagModulus b ell) ⌊x⌋₊,
        if p.Prime then directCenteredCollisionValue b ell p / (p : ℂ) else 0)
      atTop (𝓝 (K : ℂ)) := by
  obtain ⟨K, hK, _⟩ := centered_harmonic_character_formula hb hell
  refine ⟨K, ?_⟩
  have h := (Complex.continuous_ofReal.tendsto K).comp hK
  simpa only [Function.comp_def, ofReal_realPrimeTailSum,
    Complex.ofReal_div, ofReal_realDirectCenteredCollisionValue,
    Complex.ofReal_natCast] using h

end NField.Alignment.CollisionPrimeAnalyticModel

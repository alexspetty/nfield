/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimeSquareCubicEnergy
import NField.Alignment.PrimeSquareMagnitudeMixedMoment
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!+# Actual cubic-energy and square-magnitude limits

The index is the complete set of odd primes, filtered by increasing base.
Its filter is nontrivial by infinitude of primes. The quantitative cubic law
for the concrete carry energy proves the normalized energy limit; no
asymptotic estimate is supplied as a hypothesis. The exact family moments
then give the limit clauses of Corollary 6 of Magnitude Decorrelation.

The stronger secondary-term expansions in that corollary are separate.
-/

set_option autoImplicit false

namespace NField.Alignment.MagnitudeCubicLimits

open scoped Topology
open Filter
open NField.Alignment.PrimeSquareCubicEnergy
open NField.Alignment.PrimeCarryEnergyBridge
open NField.Alignment.PrimeSquareMagnitudeFamily
open NField.Alignment.MagnitudeMomentArithmetic
open NField.Alignment.SpectralRepulsion
open NField.Alignment.FiniteMagnitudeDecorrelation

abbrev OddPrimeBase := {p : ℕ // p.Prime ∧ p ≠ 2}

abbrev oddPrimeAtTop : Filter OddPrimeBase :=
  Filter.comap (fun p : OddPrimeBase => p.val) atTop

instance (p : OddPrimeBase) : NeZero p.val := ⟨p.property.1.ne_zero⟩

instance (p : OddPrimeBase) : NeZero (p.val^2) :=
  ⟨pow_ne_zero 2 p.property.1.ne_zero⟩

/-- The growing-prime limit is nonvacuous. -/
theorem oddPrimeAtTop_neBot : Filter.NeBot oddPrimeAtTop := by
  apply Filter.comap_neBot
  intro t ht
  obtain ⟨N, hN⟩ := Filter.mem_atTop_sets.mp ht
  obtain ⟨p, hNp, hp⟩ := Nat.exists_infinite_primes (max N 3)
  have hp3 : 3 ≤ p := (le_max_right N 3).trans hNp
  refine ⟨⟨p, hp, by omega⟩, hN p ?_⟩
  exact (le_max_left N 3).trans hNp

theorem base_tendsto_atTop :
    Tendsto (fun p : OddPrimeBase => (p.val : ℝ)) oddPrimeAtTop atTop :=
  tendsto_natCast_atTop_atTop.comp Filter.tendsto_comap

theorem reciprocal_base_limit :
    Tendsto (fun p : OddPrimeBase => 1/(p.val : ℝ)) oddPrimeAtTop (𝓝 0) := by
  simpa only [one_div, Function.comp_def] using
    (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).comp
      base_tendsto_atTop

/-- The actual energy has a uniform normalized error, for every odd prime. -/
theorem normalized_cubic_error (p : OddPrimeBase) :
    |primeCarryEnergy p.property.1 / (p.val : ℝ)^3 - 1| ≤
      96 * (Real.log (p.val : ℝ))^2 / p.val := by
  have hp0 : (0 : ℝ) < p.val := by exact_mod_cast p.property.1.pos
  have hpow : (0 : ℝ) < (p.val : ℝ)^3 := pow_pos hp0 3
  have heq : primeCarryEnergy p.property.1 / (p.val : ℝ)^3 - 1 =
      (primeCarryEnergy p.property.1 - (p.val : ℝ)^3) / (p.val : ℝ)^3 := by
    field_simp
  rw [heq, abs_div, abs_of_pos hpow]
  calc
    _ ≤ (96 * (p.val : ℝ)^2 * (Real.log (p.val : ℝ))^2) / (p.val : ℝ)^3 :=
      div_le_div_of_nonneg_right
        (primeCarryEnergy_cubic_pureLog_bound p.property.1 p.property.2) hpow.le
    _ = _ := by field_simp

theorem normalized_cubic_limit :
    Tendsto (fun p : OddPrimeBase =>
      primeCarryEnergy p.property.1 / (p.val : ℝ)^3) oddPrimeAtTop (𝓝 1) := by
  have hlog : Tendsto (fun x : ℝ => (Real.log x)^2/x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  have hbound : Tendsto (fun p : OddPrimeBase =>
      96*(Real.log (p.val : ℝ))^2/p.val) oddPrimeAtTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_div_assoc, mul_zero] using
      (hlog.comp base_tendsto_atTop).const_mul 96
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _) (fun p => by
    simpa only [Real.norm_eq_abs] using normalized_cubic_error p) hbound

theorem cubic_energy_error_isBigO :
    Asymptotics.IsBigO oddPrimeAtTop
      (fun p : OddPrimeBase => primeCarryEnergy p.property.1 - (p.val : ℝ)^3)
      (fun p : OddPrimeBase => (p.val : ℝ)^2 * (Real.log (p.val : ℝ))^2) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨96, Filter.Eventually.of_forall ?_⟩
  intro p
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]
  simpa only [mul_assoc] using
    primeCarryEnergy_cubic_pureLog_bound p.property.1 p.property.2

theorem marginal_l_limit :
    Tendsto (fun p : OddPrimeBase => marginalL p.val)
      oddPrimeAtTop (𝓝 (Real.pi^2/6)) := by
  have hpow := reciprocal_base_limit.pow 2
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub hpow).const_mul (Real.pi^2/6)
  simpa [marginalL, div_pow] using h

theorem energy_square_ratio_limit :
    Tendsto (fun p : OddPrimeBase => squareRatio p.val (primeCarryEnergy p.property.1))
      oddPrimeAtTop (𝓝 3) :=
  square_ratio_limit_from_cubic _ _
    (fun p => Nat.cast_ne_zero.mpr p.property.1.ne_zero)
    reciprocal_base_limit normalized_cubic_limit

theorem l_magnitude_second_moment_limit :
    Tendsto (fun p : OddPrimeBase =>
      uniformAverage (fun χ : PrimitiveOddFamily p.val => lMagnitude p.val χ^2))
      oddPrimeAtTop (𝓝 (Real.pi^2/6)) := by
  apply marginal_l_limit.congr'
  exact Filter.Eventually.of_forall fun p =>
    (l_magnitude_second_moment p.property.1 p.property.2).symm

/-- The literal complete-family ratio tends to three, without an energy
limit or secondary-term theorem as an input. -/
theorem mixed_magnitude_square_ratio_limit :
    Tendsto (fun p : OddPrimeBase =>
      uniformAverage (fun χ : PrimitiveOddFamily p.val =>
          shortMagnitude p.val χ^2 * lMagnitude p.val χ^2) /
        (uniformAverage (fun χ : PrimitiveOddFamily p.val => shortMagnitude p.val χ^2) *
         uniformAverage (fun χ : PrimitiveOddFamily p.val => lMagnitude p.val χ^2)))
      oddPrimeAtTop (𝓝 3) := by
  apply energy_square_ratio_limit.congr'
  exact Filter.Eventually.of_forall fun p =>
    (mixed_magnitude_square_ratio p.property.1 p.property.2).symm

theorem mixed_magnitude_second_moment_limit :
    Tendsto (fun p : OddPrimeBase =>
      uniformAverage (fun χ : PrimitiveOddFamily p.val =>
        shortMagnitude p.val χ^2 * lMagnitude p.val χ^2))
      oddPrimeAtTop (𝓝 (Real.pi^2/2)) := by
  have heq : (fun p : OddPrimeBase =>
      uniformAverage (fun χ : PrimitiveOddFamily p.val =>
        shortMagnitude p.val χ^2 * lMagnitude p.val χ^2)) =
      (fun p : OddPrimeBase =>
        squareRatio p.val (primeCarryEnergy p.property.1) * marginalL p.val) := by
    funext p
    rw [mixed_magnitude_second_moment p.property.1 p.property.2]
    change mixedSquare p.val (primeCarryEnergy p.property.1) = _
    have hp1 : (1 : ℝ) < p.val := by exact_mod_cast p.property.1.one_lt
    exact (div_eq_iff (marginal_positive p.val hp1).ne').mp
      (mixed_square_ratio p.val (primeCarryEnergy p.property.1) hp1)
  rw [heq]
  have h := energy_square_ratio_limit.mul marginal_l_limit
  have hlim : (3 : ℝ) * (Real.pi^2/6) = Real.pi^2/2 := by ring
  rw [hlim] at h
  exact h

/-- The exact covariance identity in the proof of Corollary 6. -/
theorem square_magnitude_covariance {p : ℕ} [NeZero p] [NeZero (p^2)]
    (hp : p.Prime) (hpodd : p ≠ 2) :
    magnitudeCovariance (fun χ : PrimitiveOddFamily p => shortMagnitude p χ^2)
      (fun χ : PrimitiveOddFamily p => lMagnitude p χ^2) =
      uniformAverage (fun χ : PrimitiveOddFamily p =>
        shortMagnitude p χ^2 * lMagnitude p χ^2) - marginalL p := by
  rw [magnitudeCovariance, short_magnitude_second_moment hp hpodd,
    l_magnitude_second_moment hp hpodd, one_mul]
  rfl

theorem square_magnitude_covariance_limit :
    Tendsto (fun p : OddPrimeBase =>
      magnitudeCovariance
        (fun χ : PrimitiveOddFamily p.val => shortMagnitude p.val χ^2)
        (fun χ : PrimitiveOddFamily p.val => lMagnitude p.val χ^2))
      oddPrimeAtTop (𝓝 (Real.pi^2/3)) := by
  have h := mixed_magnitude_second_moment_limit.sub marginal_l_limit
  have heq : Real.pi^2/2 - Real.pi^2/6 = Real.pi^2/3 := by ring
  rw [heq] at h
  apply h.congr'
  exact Filter.Eventually.of_forall fun p =>
    (square_magnitude_covariance p.property.1 p.property.2).symm

end NField.Alignment.MagnitudeCubicLimits

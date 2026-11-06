/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionPrimeAbsoluteConvergence
import NField.Alignment.TrueChannelPrimeLimits

/-! # Literal component limits and divergence in the prime-sum manuscripts -/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionPrimeLimits

open Filter Finset
open scoped BigOperators Topology
open NField.Alignment.PrimePeriodicLimits
open NField.Alignment.CollisionFluctuationSum
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.CollisionTransformStrip
open NField.Alignment.BinDerangementsClosure

theorem directAllLagDeviation_lag_one (b p : ℕ) :
    directAllLagDeviation b 1 p = directIntegerDeviation b p := by
  simp only [directAllLagDeviation, directIntegerDeviation,
    directAllLagCollisionCount, directLagOneCollisionCount, pow_one]

/-- Title: `The raw collision sum has drift negative one half`. -/
theorem lag_one_raw_prime_drift {b : ℕ} [NeZero b]
    [NeZero (allLagModulus b 1)] (hb : 2 ≤ b) :
    ∃ K : ℝ, Tendsto (fun x : ℝ =>
      realPrimeTailSum (fun p => (directIntegerDeviation b p : ℝ) / p) (b + 1) x +
        (1 / 2 : ℝ) * Real.log (Real.log x)) atTop (𝓝 K) := by
  obtain ⟨L, hL⟩ := raw_collision_tail_residual_limit (ell := 1) hb (by omega) (b + 1)
  have h := Complex.continuous_re.continuousAt.tendsto.comp hL
  refine ⟨L.re, h.congr' (Filter.Eventually.of_forall ?_)⟩
  intro x
  have hs : (∑ p ∈ Ioc (b + 1) ⌊x⌋₊,
      if p.Prime then unitExtension (allLagUnitTable b 1) p / (p : ℂ) else 0) =
      (realPrimeTailSum (fun p => (directIntegerDeviation b p : ℝ) / p) (b + 1) x : ℂ) := by
    rw [ofReal_realPrimeTailSum]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hprime : p.Prime
    · have hu := prime_unit_at_all_lag_modulus (ell := 1) (by omega : 0 < b)
        hprime (by have := (mem_Ioc.mp hp).1; omega)
      simp only [hprime, ↓reduceIte, unitExtension, dif_pos hu,
        unit_table_eq_direct_deviation hb (by omega) hu, directAllLagDeviation_lag_one,
        Complex.ofReal_div, Complex.ofReal_intCast, Complex.ofReal_natCast]
    · simp [hprime]
  change ((∑ p ∈ Ioc (b + 1) ⌊x⌋₊,
    if p.Prime then unitExtension (allLagUnitTable b 1) p / (p : ℂ) else 0) -
      (-1 / 2 : ℂ) * (Real.log (Real.log x) : ℂ)).re = _
  rw [hs]
  simp
  <;> ring

def constructiveCorrection (b p : ℕ) : ℝ :=
  (constructiveMeanValue b ((p - 1) / b) ((p - 1) % b) : ℝ) - ((p - 1) / b : ℕ)

/-- Title: `The constructive correction has the exact reciprocal prime drift`. -/
theorem lag_one_correction_prime_drift {b : ℕ} [NeZero b]
    [NeZero (allLagModulus b 1)] (hb : 2 ≤ b) :
    ∃ K : ℝ, Tendsto (fun x : ℝ =>
      realPrimeTailSum (fun p => constructiveCorrection b p / p) (b + 1) x -
        (1 / 2 - 1 / (b : ℝ)) * Real.log (Real.log x)) atTop (𝓝 K) := by
  obtain ⟨S, hS⟩ := lag_one_raw_prime_drift hb
  obtain ⟨D, hD⟩ := lag_one_constructive_prime_drift hb
  refine ⟨S - D, (hS.sub hD).congr' (Filter.Eventually.of_forall ?_)⟩
  intro x
  have hs : realPrimeTailSum (fun p => (directIntegerDeviation b p : ℝ) / p) (b + 1) x -
      realPrimeTailSum (fun p => lagOneConstructiveFluctuation b p / p) (b + 1) x =
      realPrimeTailSum (fun p => constructiveCorrection b p / p) (b + 1) x := by
    simp only [realPrimeTailSum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : p.Prime
    · simp only [hp, ↓reduceIte, directIntegerDeviation, Int.cast_sub,
        Int.cast_natCast, lagOneConstructiveFluctuation, constructiveCorrection]
      ring
    · simp [hp]
  have hbne : (b : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne b
  rw [show ((b : ℝ) - 1) / b = 1 - 1 / (b : ℝ) by rw [sub_div, div_self hbne]]
  linarith

/-- Title: `The collision fluctuation sum tends to negative infinity`. -/
theorem lag_one_prime_sum_tendsto_atBot {b : ℕ} [NeZero b]
    [NeZero (allLagModulus b 1)] (hb : 2 ≤ b) :
    Tendsto (realPrimeTailSum (fun p => lagOneConstructiveFluctuation b p / p) (b + 1))
      atTop atBot := by
  obtain ⟨K, hK⟩ := lag_one_constructive_prime_drift hb
  have hpos : 0 < ((b : ℝ) - 1) / b := by
    have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
    exact div_pos (by linarith) (by linarith)
  have hg : Tendsto (fun x : ℝ => -(((b : ℝ) - 1) / b) * Real.log (Real.log x))
      atTop atBot := tendsto_const_nhds.neg_mul_atTop (neg_neg_of_pos hpos)
        (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)
  convert hK.add_atBot hg using 1
  ext x
  ring

/-- Title: `Each true residue three channel converges separately`. -/
theorem residue_three_real_prime_channel_limit
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    [NeZero (Nat.lcm (allLagModulus b ell) 3)]
    [NeZero (Nat.gcd (allLagModulus b ell) 3)]
    (hb : 2 ≤ b) (hell : 1 ≤ ell) (r : (ZMod 3)ˣ) :
    ∃ L : ℝ, Tendsto (fun x : ℝ =>
      ∑ p ∈ Finset.Ioc (Nat.lcm (allLagModulus b ell) 3) ⌊x⌋₊,
        if p.Prime ∧ (p : ZMod 3) = r then
          realDirectCenteredCollisionValue b ell p / (p : ℝ) else 0) atTop (𝓝 L) :=
  squarefree_real_true_channel_limit hb hell (by decide +kernel) r

end NField.Alignment.CollisionPrimeLimits

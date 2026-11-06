/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.AllLagPrimeDrift

/-! # The lag-one fluctuation law with its exact lower prime cutoff -/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionPrimeLimits

open Filter Finset
open scoped BigOperators Topology
open NField.Alignment.PrimePeriodicLimits
open NField.Alignment.ProgressionMertens
open NField.Alignment.CollisionFluctuationSum
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.BinDerangementsClosure

theorem real_residual_change_cutoff (F : ℕ → ℝ) (c d : ℕ) (g : ℝ → ℝ)
    {L : ℝ} (hL : Tendsto (fun x : ℝ => (∑ n ∈ Finset.Ioc c ⌊x⌋₊, F n) + g x)
      atTop (𝓝 L)) :
    ∃ K : ℝ, Tendsto (fun x : ℝ => (∑ n ∈ Finset.Ioc d ⌊x⌋₊, F n) + g x)
      atTop (𝓝 K) := by
  refine ⟨L + (∑ n ∈ Finset.Ioc 0 c, F n) - (∑ n ∈ Finset.Ioc 0 d, F n), ?_⟩
  apply ((hL.add_const _).sub_const _).congr'
  filter_upwards [tendsto_nat_floor_atTop.eventually (eventually_ge_atTop (max c d))] with x hx
  have hc := Finset.sum_Ioc_consecutive F (Nat.zero_le c) ((le_max_left c d).trans hx)
  have hd := Finset.sum_Ioc_consecutive F (Nat.zero_le d) ((le_max_right c d).trans hx)
  linarith

def lagOneConstructiveFluctuation (b p : ℕ) : ℝ :=
  (directLagOneCollisionCount b p : ℝ) -
    (constructiveMeanValue b ((p - 1) / b) ((p - 1) % b) : ℝ)

theorem constructiveFluctuation_lag_one (b p : ℕ) :
    constructiveFluctuation b 1 p = lagOneConstructiveFluctuation b p := by
  simp only [constructiveFluctuation, lagOneConstructiveFluctuation,
    directAllLagCollisionCount, directLagOneCollisionCount, pow_one]

/-- Title: `The collision fluctuation law at the original prime cutoff`. -/
theorem lag_one_constructive_prime_drift {b : ℕ} [NeZero b]
    [NeZero (allLagModulus b 1)] (hb : 2 ≤ b) :
    ∃ κ : ℝ, Tendsto (fun x : ℝ =>
      realPrimeTailSum (fun p => lagOneConstructiveFluctuation b p / (p : ℝ)) (b + 1) x +
        (((b : ℝ) - 1) / b) * Real.log (Real.log x)) atTop (𝓝 κ) := by
  obtain ⟨κ, hκ⟩ := all_lag_constructive_prime_drift (ell := 1) hb (by omega)
  obtain ⟨K, hK⟩ := real_residual_change_cutoff
    (fun p => if p.Prime then constructiveFluctuation b 1 p / (p : ℝ) else 0)
    (allLagModulus b 1) (b + 1)
    (fun x => (((b : ℝ) - 1) / b) * Real.log (Real.log x)) hκ
  exact ⟨K, by simpa only [realPrimeTailSum, constructiveFluctuation_lag_one] using hK⟩

theorem ordinary_prime_harmonic_residual (c : ℕ) :
    ∃ B : ℝ, Tendsto (fun x : ℝ =>
      realPrimeTailSum (fun p => 1 / (p : ℝ)) c x - Real.log (Real.log x)) atTop (𝓝 B) := by
  have hz (n : ℕ) : (n : ZMod 1) = 0 := Subsingleton.elim _ _
  have hu : IsUnit (0 : ZMod 1) := by simpa only [Subsingleton.elim (0 : ZMod 1) 1] using isUnit_one
  obtain ⟨B, hB⟩ := real_cutoff_mertens_progression hu
  have hfull : Tendsto (fun x : ℝ =>
      realPrimeTailSum (fun p => 1 / (p : ℝ)) 0 x - Real.log (Real.log x)) atTop (𝓝 B) := by
    simpa [realPrimeTailSum, realProgressionPrimeSum, hz, one_div] using hB
  obtain ⟨K, hK⟩ := real_residual_change_cutoff
    (fun p => if p.Prime then 1 / (p : ℝ) else 0) 0 c
    (fun x => -Real.log (Real.log x)) (by simpa only [realPrimeTailSum, sub_eq_add_neg] using hfull)
  exact ⟨K, by simpa only [realPrimeTailSum, sub_eq_add_neg] using hK⟩

/-- Title: `Removing the drift gives an ordinary convergent prime series`. -/
theorem lag_one_drift_removed_limit {b : ℕ} [NeZero b]
    [NeZero (allLagModulus b 1)] (hb : 2 ≤ b) :
    ∃ L : ℝ, Tendsto
      (realPrimeTailSum (fun p =>
        (lagOneConstructiveFluctuation b p + ((b : ℝ) - 1) / b) / (p : ℝ)) (b + 1))
      atTop (𝓝 L) := by
  obtain ⟨κ, hκ⟩ := lag_one_constructive_prime_drift hb
  obtain ⟨B, hB⟩ := ordinary_prime_harmonic_residual (b + 1)
  have h := hκ.add (hB.const_mul (((b : ℝ) - 1) / b))
  refine ⟨_, h.congr' (Filter.Eventually.of_forall ?_)⟩
  intro x
  have hs : realPrimeTailSum (fun p =>
      (lagOneConstructiveFluctuation b p + ((b : ℝ) - 1) / b) / (p : ℝ)) (b + 1) x =
      realPrimeTailSum (fun p => lagOneConstructiveFluctuation b p / (p : ℝ)) (b + 1) x +
        (((b : ℝ) - 1) / b) * realPrimeTailSum (fun p => 1 / (p : ℝ)) (b + 1) x := by
    simp only [realPrimeTailSum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : p.Prime <;> simp only [hp, ↓reduceIte] <;> ring
  rw [hs]
  ring

end NField.Alignment.CollisionPrimeLimits

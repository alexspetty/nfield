/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.LagOnePrimeDrift
import Mathlib.NumberTheory.LSeries.Basic

/-! # Uniform boundedness and absolute convergence of the actual fluctuation -/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionPrimeLimits

open Filter Finset
open scoped BigOperators Topology
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionTransformStrip
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.BinDerangementsClosure

theorem prime_unit_at_all_lag_modulus {b ell p : ℕ}
    [NeZero (allLagModulus b ell)] (hb : 0 < b) (hp : p.Prime) (hbp : b < p) :
    IsUnit (p : ZMod (allLagModulus b ell)) := by
  apply (ZMod.isUnit_iff_coprime p _).mpr
  have hc : p.Coprime b := hp.coprime_iff_not_dvd.mpr (fun h => by
    have := Nat.le_of_dvd hb h
    omega)
  exact hc.pow_right (ell + 1)

/-- Title: `The actual constructive fluctuation is uniformly bounded`. -/
theorem constructive_fluctuation_uniform_bound {b ell : ℕ}
    [NeZero (allLagModulus b ell)] (hb : 2 ≤ b) (hell : 1 ≤ ell) :
    ∃ B : ℝ, 0 < B ∧ ∀ p : ℕ, p.Prime → b + 1 < p →
      |constructiveFluctuation b ell p| ≤ B := by
  classical
  let C : ℝ := ∑ a : UnitClass (allLagModulus b ell), ‖allLagUnitTable b ell a‖
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  refine ⟨C + 1, by linarith, ?_⟩
  intro p hp hbp
  have hb0 : 0 < b := by omega
  have hu := prime_unit_at_all_lag_modulus (ell := ell) hb0 hp (by omega)
  have hraw : |(directAllLagDeviation b ell p : ℝ)| ≤ C := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, Complex.ofReal_intCast,
      ← unit_table_eq_direct_deviation hb hell hu]
    exact Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ hu.unit)
  let Q := (p - 1) / b
  let R := (p - 1) % b
  have hQ : 1 ≤ Q := (Nat.le_div_iff_mul_le hb0).mpr (by omega)
  have hR : R < b := Nat.mod_lt _ hb0
  have hden : 0 < b * (Q - 1) + R := by
    rw [← quotient_correction_denominator hb0 hbp]
    omega
  obtain ⟨hl, hh⟩ := constructiveMeanValue_correction_bounds hb0 hQ hR hden
  have hl' : (0 : ℝ) ≤ (constructiveMeanValue b Q R : ℝ) - Q := by exact_mod_cast hl
  have hh' : (constructiveMeanValue b Q R : ℝ) - Q ≤ 1 := by exact_mod_cast hh
  have heq : constructiveFluctuation b ell p =
      (directAllLagDeviation b ell p : ℝ) - ((constructiveMeanValue b Q R : ℝ) - Q) := by
    simp only [constructiveFluctuation, directAllLagDeviation, Int.cast_sub, Int.cast_natCast]
    dsimp [Q, R]
    ring
  rw [heq]
  calc
    _ ≤ |(directAllLagDeviation b ell p : ℝ)| +
        |(constructiveMeanValue b Q R : ℝ) - Q| := abs_sub _ _
    _ ≤ C + 1 := add_le_add hraw (by rwa [abs_of_nonneg hl'])

def fluctuationPrimeCoefficient (b ell p : ℕ) : ℂ :=
  if p.Prime ∧ b + 1 < p then (constructiveFluctuation b ell p : ℂ) else 0

/-- Title: `The collision prime series converges absolutely above one`.
Mathlib's bounded-coefficient L-series theorem supplies the analytic comparison. -/
theorem collision_prime_series_absolute_convergence {b ell : ℕ}
    [NeZero (allLagModulus b ell)] (hb : 2 ≤ b) (hell : 1 ≤ ell)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fluctuationPrimeCoefficient b ell) s := by
  obtain ⟨B, hB, hbound⟩ := constructive_fluctuation_uniform_bound hb hell
  apply LSeriesSummable_of_bounded_of_one_lt_re (m := B) _ hs
  intro p _
  by_cases hp : p.Prime ∧ b + 1 < p
  · simpa only [fluctuationPrimeCoefficient, if_pos hp, Complex.norm_real, Real.norm_eq_abs]
      using hbound p hp.1 hp.2
  · simp only [fluctuationPrimeCoefficient, if_neg hp, norm_zero]
    exact hB.le

end NField.Alignment.CollisionPrimeLimits

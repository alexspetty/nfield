/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimeManuscriptConsequences
import NField.Alignment.CenteredSourceDetails

/-! # Literal partial sums and the raw bound in the fluctuation manuscript -/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionPrimeLimits

open scoped BigOperators
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionTransformStrip
open NField.Alignment.CollisionFluctuationSum

theorem lag_one_quotient_square_block {b t a : ℕ} (hb : 2 ≤ b) (ha : 0 < a)
    (hcop : a.Coprime (b ^ 2)) :
    (b ^ 2 * t + a - 1) / b = b * t + a / b := by
  have hsub : b ^ 2 * t + a - 1 = b * (b * t) + (a - 1) := by
    rw [Nat.add_sub_assoc (by omega : 1 ≤ a)]
    congr 1
    ring
  rw [hsub, Nat.mul_add_div (by omega : 0 < b),
    pred_div_eq_div (by omega) ha (mod_base_ne_zero_of_coprime_square hb hcop)]

/-- The literal complex partial prime sum at the manuscript's lower cutoff. -/
def collisionPartialSum (b ell : ℕ) (s : ℂ) (x : ℝ) : ℂ :=
  ∑ p ∈ Finset.Ioc (b + 1) ⌊x⌋₊,
    if p.Prime then (constructiveFluctuation b ell p : ℂ) / (p : ℂ) ^ s else 0

/-- The two quantities printed alongside the finite decimal prime sums. -/
def decimalPrimeDiagnostics (x lastPrime : ℝ) : ℝ × ℝ :=
  let value := realPrimeTailSum (fun p => lagOneConstructiveFluctuation 10 p / p) 11 x
  (value / Real.log (Real.log lastPrime), value + (9 / 10 : ℝ) * Real.log (Real.log lastPrime))

/-- Title: `The complex collision partial sum at one is the real harmonic sum`. -/
theorem lag_one_partial_sum_at_one (b : ℕ) (x : ℝ) :
    collisionPartialSum b 1 1 x =
      (realPrimeTailSum (fun p => lagOneConstructiveFluctuation b p / p) (b + 1) x : ℂ) := by
  simp only [collisionPartialSum, ofReal_realPrimeTailSum,
    constructiveFluctuation_lag_one, Complex.cpow_one,
    Complex.ofReal_div, Complex.ofReal_natCast]

/-- Title: `The raw collision deviation is bounded on every admissible prime`. -/
theorem raw_collision_uniform_bound {b ell : ℕ} [NeZero (allLagModulus b ell)]
    (hb : 2 ≤ b) (hell : 1 ≤ ell) :
    ∃ B : ℝ, 0 < B ∧ ∀ p : ℕ, p.Prime → b < p →
      |(directAllLagDeviation b ell p : ℝ)| ≤ B := by
  classical
  let C : ℝ := ∑ a : UnitClass (allLagModulus b ell), ‖allLagUnitTable b ell a‖
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  refine ⟨C + 1, by linarith, ?_⟩
  intro p hp hbp
  have hu := prime_unit_at_all_lag_modulus (ell := ell) (by omega : 0 < b) hp hbp
  have hraw : |(directAllLagDeviation b ell p : ℝ)| ≤ C := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, Complex.ofReal_intCast,
      ← unit_table_eq_direct_deviation hb hell hu]
    exact Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ hu.unit)
  linarith

end NField.Alignment.CollisionPrimeLimits

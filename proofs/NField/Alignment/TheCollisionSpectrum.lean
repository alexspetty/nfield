/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionSpectrumLandscape
import NField.Alignment.CollisionTransform

/-!
# The collision spectrum

Reusable finite Fourier, moment, and exact-ledger consequences for the Lean
companion to "The Collision Spectrum".

The concrete finite transforms and the base-five cyclotomic certificate are
inherited from `CollisionSpectrumLandscape`.  This module adds the exact
prime-base active-channel gate, the normalized-weight algebra, the
phase-separated coefficient algebra, and the declared finite-ledger counts.
-/

namespace NField.Alignment.TheCollisionSpectrum

open scoped BigOperators ComplexConjugate
open NField.Alignment.CollisionFluctuationSum
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionTransformStrip
open NField.Alignment.CollisionSpectrumLandscape
open NField.Alignment.CollisionTransform

/-! ## The concrete finite spectrum -/

/-- The centered lag-one collision signal used by the manuscript. -/
noncomputable def centeredLagOneSpectrum
    (b : ℕ) [NeZero b] [NeZero (allLagModulus b 1)] :
    UnitClass (allLagModulus b 1) → ℂ :=
  centeredCollisionTransform b 1

/-- The concrete centered lag-one signal is exactly odd under reflection. -/
theorem centeredLagOneSpectrum_odd
    {b : ℕ} [NeZero b] [NeZero (allLagModulus b 1)]
    (hb2 : 2 ≤ b) (a : UnitClass (allLagModulus b 1)) :
    centeredLagOneSpectrum b (-a) = -centeredLagOneSpectrum b a := by
  exact centeredCollisionTransform_odd hb2 (by omega) a

/-- The concrete centered lag-one signal has zero total mass. -/
theorem centeredLagOneSpectrum_sum_zero
    {b : ℕ} [NeZero b] [NeZero (allLagModulus b 1)] :
    ∑ a, centeredLagOneSpectrum b a = 0 :=
  centeredCollisionTransform_sum_zero

/-- At prime base, every nonzero channel of the actual centered lag-one
transform is primitive and odd. -/
theorem activeLagOneChannel_primitive_and_odd
    {b : ℕ} (hb : Nat.Prime b)
    [NeZero b] [NeZero (allLagModulus b 1)]
    {χ : Character (allLagModulus b 1)}
    (hactive :
      collisionCoefficient (centeredLagOneSpectrum b) χ ≠ 0) :
    χ.IsPrimitive ∧ χ.Odd := by
  apply primeBase_active_primitive_and_odd hb
  exact mem_transformActiveCharacters_iff.mpr hactive

/-- Parseval for the actual normalized lag-one collision coefficients. -/
theorem centeredLagOneSpectrum_parseval
    {b : ℕ} [NeZero b] [NeZero (allLagModulus b 1)] :
    ∑ χ : Character (allLagModulus b 1),
        ‖collisionCoefficient (centeredLagOneSpectrum b) χ‖ ^ 2 =
      ((allLagModulus b 1).totient : ℝ)⁻¹ *
        ∑ a : UnitClass (allLagModulus b 1),
          ‖centeredLagOneSpectrum b a‖ ^ 2 :=
  collisionCoefficient_parseval (centeredLagOneSpectrum b)

/-! ## Phase-separated coefficient algebra -/

/-- The Bernoulli factorization, the odd functional-equation value, and the
diagonal identity `G = 2A` combine with exactly the manuscript's sign and
normalization.  The analytic Bernoulli-to-`L(1,chi)` identity is an explicit
hypothesis here rather than an unchecked Lean declaration. -/
theorem phaseSeparated_coefficient_algebra
    (base step B epsilon L A G coefficient : ℂ)
    (hbase : base ≠ 0) (hstep : step ≠ 0)
    (hB : B = -(base / Real.pi) * epsilon * L)
    (hG : G = 2 * A)
    (hcoefficient : coefficient = -(B * star G) / (base * step)) :
    coefficient =
      (2 / (Real.pi * step)) * epsilon * L * star A := by
  have hstarG : star G = 2 * star A := by
    rw [hG]
    simp
  rw [hcoefficient, hB, hstarG]
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  field_simp [hbase, hstep, hpi]

/-! ## Exact normalized moment consequences -/

/-- Collision weights are squared diagonal magnitudes divided by their exact
total mass. -/
noncomputable def normalizedCollisionWeight
    {ι : Type*} (scale : ℝ) (diagonal : ι → ℂ) (i : ι) : ℝ :=
  Complex.normSq (diagonal i) / scale

/-- An exact diagonal second moment makes the normalized weights sum to one. -/
theorem normalizedCollisionWeight_sum_one
    {ι : Type*} [Fintype ι]
    (scale : ℝ) (diagonal : ι → ℂ) (hscale : scale ≠ 0)
    (hmoment : ∑ i, Complex.normSq (diagonal i) = scale) :
    ∑ i, normalizedCollisionWeight scale diagonal i = 1 := by
  unfold normalizedCollisionWeight
  rw [← Finset.sum_div, hmoment]
  exact div_self hscale

/-- Dividing the exact weighted special-value moment by the exact diagonal
mass gives the manuscript's normalized expectation formula. -/
theorem normalizedCollisionWeight_specialValue_mean
    {ι : Type*} [Fintype ι]
    (scale constant energy : ℝ)
    (diagonal : ι → ℂ) (specialValueSq : ι → ℝ)
    (hscale : scale ≠ 0)
    (hmoment :
      ∑ i, Complex.normSq (diagonal i) * specialValueSq i =
        constant * energy) :
    ∑ i, normalizedCollisionWeight scale diagonal i * specialValueSq i =
      constant * energy / scale := by
  unfold normalizedCollisionWeight
  calc
    (∑ i, Complex.normSq (diagonal i) / scale * specialValueSq i) =
        (∑ i, Complex.normSq (diagonal i) * specialValueSq i) / scale := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro i _
          field_simp [hscale]
    _ = constant * energy / scale := by rw [hmoment]

/-- The base-five coefficient square and Parseval normalization force the
exact fourth-moment scale.  This isolates the final algebra from the analytic
special-value input. -/
theorem baseFive_fourth_moment_from_parseval
    (fourthMoment coefficientEnergy collisionEnergy : ℝ)
    (hpi : Real.pi ≠ 0)
    (hcoefficient :
      coefficientEnergy =
        (125 / (16 * Real.pi ^ 4)) * fourthMoment)
    (hparseval : coefficientEnergy = collisionEnergy / 20) :
    fourthMoment = (4 * Real.pi ^ 4 / 625) * collisionEnergy := by
  rw [hparseval] at hcoefficient
  field_simp [hpi] at hcoefficient ⊢
  nlinarith [hcoefficient]

/-! ## Exact finite ledgers -/

/-- Odd prime bases in the manuscript's exhaustive character ledger. -/
def spectrumLedgerBases : Finset ℕ :=
  {5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71}

/-- The manuscript's primitive-odd population formula, kept as an arithmetic
ledger function.  The separate character-theoretic population theorem remains
outside this module. -/
def declaredPrimitiveOddPopulation (b : ℕ) : ℕ :=
  (b - 1) ^ 2 / 2

/-- The declared population formula sums to exactly 14,372 channels over the
eighteen ledger bases. -/
theorem spectrumLedger_declared_channel_count :
    ∑ b ∈ spectrumLedgerBases, declaredPrimitiveOddPopulation b = 14372 := by
  decide +kernel

/-- Exact integer arithmetic in the Ramanujan-sum ledger used for the
base-five fourth-power calculation. -/
theorem baseFive_ramanujan_fourth_power_ledger :
    (32 : ℤ) * 8 + 28 * 2 + 14 * (-2) + 34 * 2 + 18 * (-2) + 2 * (-8) =
      300 := by
  norm_num

/-- Multiplying the short-sum fourth-power ledger by the diagonal factor
`|2|^4` gives the displayed total 4,800. -/
theorem baseFive_diagonal_fourth_power_ledger :
    (16 : ℤ) * 300 = 4800 := by
  norm_num

end NField.Alignment.TheCollisionSpectrum

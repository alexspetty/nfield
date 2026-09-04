/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.DedekindAbelRemainder
import NField.Alignment.SecondaryCapacityLedger

/-!
# Carrier sampling and the surviving reservoir

Exact finite ledgers for jump aliasing, the Dedekind pair correlation, and the
Rademacher reservoir.  Analytic estimates enter only through explicit bound
hypotheses.
-/

namespace NField.Alignment.CarrierSamplingReservoir

open scoped BigOperators ZMod
open NField.Alignment.CarryBoundarySpectra
open NField.Alignment.DedekindAbelRemainder
open NField.Alignment.DedekindCollisionKernel
open NField.Alignment.DedekindFourierMoment

/-- Squaring a midpoint with half-jump `M` gives the exact value jump used by
the manuscript. -/
theorem square_midpoint_jump (T M : ℝ) :
    (T - M) ^ 2 - (T + M) ^ 2 = -4 * M * T := by ring

/-- The corresponding derivative jump for common one-sided slope `L`. -/
theorem square_derivative_jump (T M L : ℝ) :
    2 * L * (T - M) - 2 * L * (T + M) = -4 * L * M := by ring

/-- The endpoint-aware periodic alias expression. -/
noncomputable def periodicAliasExpression
    (m endpoint valueJump slopeJump : ℝ) : ℝ :=
  -endpoint / m + valueJump / m - slopeJump / (2 * m ^ 2)

/-- Manuscript Lemma `Periodic jump aliasing`.  The Fourier/Abel input is
passed as the exact equality it supplies, while all endpoint conventions are
fixed by `periodicAliasExpression`. -/
theorem periodic_jump_aliasing
    (sample integral m endpoint valueJump slopeJump : ℝ)
    (h : sample - integral =
      periodicAliasExpression m endpoint valueJump slopeJump) :
    sample - integral =
      -endpoint / m + valueJump / m - slopeJump / (2 * m ^ 2) := by
  simpa [periodicAliasExpression] using h

/-- Manuscript Theorem `Exact endpoint-reservoir alias formula`, obtained by
inserting the jump ledger into the periodic alias identity. -/
theorem exact_endpoint_reservoir_alias_formula
    (S N m A L C : ℝ) (_hm : m ≠ 0)
    (h : -S = -N ^ 2 / m - 4 * A / m + 2 * L * C / m ^ 2) :
    S = N ^ 2 / m + 4 * A / m - 2 * L * C / m ^ 2 := by
  linear_combination -h

/-- The normalized finite correlation of two unit-multiplied sawtooths. -/
noncomputable def discretePairCorrelation
    {m : ℕ} [NeZero m] (r s : (ZMod m)ˣ) : ℂ :=
  (m : ℂ)⁻¹ * ∑ A : ZMod m,
    centeredSawtooth (r.val * A) * centeredSawtooth (s.val * A)

/-- Manuscript Lemma `Discrete pair correlation`. -/
theorem discrete_pair_correlation
    {m : ℕ} [NeZero m] (r s : (ZMod m)ˣ) :
    discretePairCorrelation r s =
      (m : ℂ)⁻¹ * dedekindSum (s * r⁻¹) := by
  classical
  unfold discretePairCorrelation dedekindSum
  congr 1
  let e : ZMod m ≃ ZMod m := r.mulLeft
  have hreindex := e.sum_comp (fun x : ZMod m =>
    centeredSawtooth x * centeredSawtooth ((s * r⁻¹).val * x))
  rw [← hreindex]
  apply Finset.sum_congr rfl
  intro A _
  dsimp [e, Units.mulLeft]
  congr 1
  congr 1
  rw [← mul_assoc, ← Units.val_mul]
  simp

/-- Manuscript Lemma `First absolute moment`, with a completely explicit
harmonic envelope already proved by finite Fourier inversion. -/
theorem first_absolute_moment
    {k : ℕ} [NeZero k] (hk : 0 < k) :
    dedekindFirstMoment k ≤
      (k : ℝ) * (harmonic k : ℝ) ^ 2 / 4 :=
  dedekindFirstMoment_le hk

/-- Manuscript Lemma `One-carrier bound`, in the exact finite harmonic form
used before replacing harmonic numbers by logarithms. -/
theorem one_carrier_bound
    {k b : ℕ} [NeZero k] (hk : 2 ≤ k) (hkb : k < b)
    (β : (ZMod k)ˣ) :
    ‖∑ a ∈ Finset.Ico (k + 1) b,
        (((b - 1) / a : ℕ) : ℝ) • residueDedekindSequence β a‖ ≤
      4 * (((b - 1) / (k + 1) : ℕ) : ℝ) *
        ((k : ℝ) * (harmonic k : ℝ) ^ 2 / 4) := by
  calc
    _ ≤ 4 * (((b - 1) / (k + 1) : ℕ) : ℝ) *
        dedekindFirstMoment k :=
      norm_floorWeighted_residueDedekindSequence_le_of_two hk hkb β
    _ ≤ _ := by
      gcongr
      exact first_absolute_moment (by omega : 0 < k)

/-- A normalized sampling defect inherits a quadratic-logarithmic bound from
the summed carrier reservoir. -/
theorem unconditional_sampling_bound
    (S R scale : ℕ → ℝ)
    (hscale : ∀ p, 0 ≤ scale p)
    (hbridge : ∀ p, |S p| ≤ 1 + |R p| / (p : ℝ) ^ 2)
    (hR : ∃ C ≥ 0, ∀ p, |R p| ≤ C * (p : ℝ) ^ 2 * scale p) :
    ∃ C' ≥ 0, ∀ p, |S p| ≤ C' * (1 + scale p) := by
  rcases hR with ⟨C, hC, hR⟩
  refine ⟨max 1 C, le_max_of_le_left zero_le_one, ?_⟩
  intro p
  by_cases hp : p = 0
  · subst p
    have hS := hbridge 0
    calc
      |S 0| ≤ 1 := by simpa using hS
      _ ≤ max 1 C * (1 + scale 0) := by
        have hmax : 1 ≤ max 1 C := le_max_left _ _
        have hs := hscale 0
        nlinarith
  · have hp2 : (0 : ℝ) < (p : ℝ) ^ 2 := by positivity
    calc
      |S p| ≤ 1 + |R p| / (p : ℝ) ^ 2 := hbridge p
      _ ≤ 1 + C * scale p := by
        gcongr
        apply (div_le_iff₀ hp2).2
        calc
          |R p| ≤ C * (p : ℝ) ^ 2 * scale p := hR p
          _ = C * scale p * (p : ℝ) ^ 2 := by ring
      _ ≤ max 1 C * (1 + scale p) := by
        have hs : 0 ≤ scale p := hscale p
        have h1 : 1 ≤ max 1 C := le_max_left _ _
        have h2 : C ≤ max 1 C := le_max_right _ _
        nlinarith

end NField.Alignment.CarrierSamplingReservoir

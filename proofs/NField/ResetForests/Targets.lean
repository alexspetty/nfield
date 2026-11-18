/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.Sampling
import NField.ResetForests.DivisorBudget
import Mathlib
/-! # Quantitative forest estimates

These definitions state the reset-grid, complete-clock and forest inequalities.
Their proofs are `ResetGrid.reset_grid_estimate`,
`ClockRows.complete_clock_row_estimate`,
`AbsoluteForestWork.whole_forest_absolute_estimate` and
`SignedForestWork.polynomial_signed_forest_estimate` in their respective modules.
-/

noncomputable section

namespace NField.ResetForests.Core

open scoped BigOperators
open NField.Alignment
open CollisionRampEnergy DedekindReciprocity

def resetGridField (k : ℕ) (c : ℕ → ℂ) (a : ℕ) : ℂ :=
  2*∑ h ∈ Finset.Icc 1 (k-1),
    c h*(midpointRow h ((a : ℝ)/(k : ℝ)) : ℂ)

/-- The all-frequency, all-address reset-grid estimate. -/
def ResetGridEstimate : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∀ c : ℕ → ℂ,
    (1/(k : ℝ))*(∑ a ∈ Finset.range k, ‖resetGridField k c a‖^2) ≤
      (k.divisors.card : ℝ)^2*(harmonic k : ℝ)^2 *
        ∑ h ∈ Finset.Icc 1 (k-1), ‖c h‖^2

def completeCorrelation (p a d : ℕ) : ℝ :=
  (RademacherThreeTerm.arithmeticCoefficientDedekindTerm a p d : ℝ)

/-- The sharp complete-clock row estimate. -/
def CompleteClockRowEstimate : Prop :=
  ∀ p d : ℕ, p.Prime → 2 ≤ d → d < p →
    (∑ a ∈ Finset.range d, |completeCorrelation p a d|) ≤
      (d : ℝ)/4*(harmonic (d/2) : ℝ)^2

def roughPart (N k : ℕ) : ℕ :=
  ∏ p ∈ k.primeFactors.filter (fun p => ¬p ∣ N), p^(k.factorization p)

def forestMask (N D : ℕ) (k : ℕ) : Bool := decide (roughPart N k ∣ D)

def absoluteForestReading (N Q D : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 N, if forestMask N D k then
    ((N/k : ℕ) : ℝ) *
      ∑ a ∈ (Finset.Ico 1 k).filter (fun a => a.Coprime k),
        |boundaryResponse N ((a : ℝ)/(k : ℝ))*
          midpointRow Q ((a : ℝ)/(k : ℝ))|
    else 0

/-- The finite whole-forest bound. -/
def WholeForestAbsoluteEstimate : Prop :=
  ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 < C ∧ ∀ p D : ℕ,
    p.Prime → p ≠ 2 → 1 ≤ D →
      absoluteForestReading (p-1) (p^2) D ≤
        (C/2)*((p-1 : ℕ) : ℝ)^(3/2+2*η)*
          (harmonic (p-1) : ℝ)*(tripleDivisorCount D : ℝ)

/-- The signed first-power estimate at polynomial height. -/
def PolynomialForestSignedEstimate : Prop :=
  ∀ K C₀ ε : ℝ, 0 ≤ K → 0 < C₀ → 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ p D : ℕ,
      p.Prime → p ≠ 2 → 1 ≤ D → (D : ℝ) ≤ C₀*(p : ℝ)^K →
        |selectedReading (p-1) (p^2) (forestMask (p-1) D)| ≤
          C*(p : ℝ)^(1+ε)

end NField.ResetForests.Core

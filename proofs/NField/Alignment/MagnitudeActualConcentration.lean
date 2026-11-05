/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.MagnitudeShortMomentBound

/-!
# Concentration of the actual primitive odd short-sum square mass

The tail is the exact cardinality proportion in the manuscript. Indicator
averages retain the strict upper threshold and non-strict lower threshold.
Every moment limit used here is already proved for the actual family.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.MagnitudeActualConcentration
open scoped BigOperators Topology
open Filter SpectralRepulsion FiniteMagnitudeDecorrelation
  PrimeSquareMagnitudeFamily MagnitudeCubicLimits MagnitudeShortMomentBound

theorem tail_proportion_eq (p : OddPrimeBase) (ε : ℝ) :
    (Fintype.card {χ : PrimitiveOddFamily p.val // ε < shortMagnitude p.val χ} : ℝ) /
      (Fintype.card (PrimitiveOddFamily p.val) : ℝ) = tailFraction (shortMagnitude p.val) ε := by
  classical
  simp [tailFraction,uniformAverage,Fintype.card_subtype,div_eq_mul_inv,mul_comm]

theorem upper_indicator_eq (p : OddPrimeBase) (ε : ℝ) :
    uniformAverage (fun χ : PrimitiveOddFamily p.val =>
      shortMagnitude p.val χ^2*(if ε < shortMagnitude p.val χ then 1 else 0)) =
      upperSquareMass (shortMagnitude p.val) ε := by
  unfold upperSquareMass
  congr 1
  funext χ
  split_ifs <;> simp

theorem lower_indicator_eq (p : OddPrimeBase) (ε : ℝ) :
    uniformAverage (fun χ : PrimitiveOddFamily p.val =>
      shortMagnitude p.val χ^2*(if shortMagnitude p.val χ ≤ ε then 1 else 0)) =
      lowerSquareMass (shortMagnitude p.val) ε := by
  unfold lowerSquareMass
  congr 1
  funext χ
  split_ifs <;> simp

theorem tail_proportion_bound (p : OddPrimeBase) {ε : ℝ} (hε : 0 < ε) :
    (Fintype.card {χ : PrimitiveOddFamily p.val // ε < shortMagnitude p.val χ} : ℝ) /
      (Fintype.card (PrimitiveOddFamily p.val) : ℝ) ≤
      ε^(-(3/2 : ℝ))*magnitudeMoment (3/2) (shortMagnitude p.val) := by
  rw [tail_proportion_eq,Real.rpow_neg hε.le,mul_comm,← div_eq_mul_inv]
  exact tail_fraction_bound _ (short_magnitude_nonneg p.val) ε hε

theorem tail_proportion_tendsto_zero {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun p : OddPrimeBase =>
      (Fintype.card {χ : PrimitiveOddFamily p.val // ε < shortMagnitude p.val χ} : ℝ) /
        (Fintype.card (PrimitiveOddFamily p.val) : ℝ)) oddPrimeAtTop (𝓝 0) := by
  simp_rw [tail_proportion_eq]
  exact tail_fraction_tendsto_zero (fun p : OddPrimeBase => shortMagnitude p.val)
    (fun p => short_magnitude_nonneg p.val) ε hε short_moment_tendsto_zero

theorem lower_square_mass_bound (p : OddPrimeBase) {ε : ℝ} (hε : 0 < ε) :
    uniformAverage (fun χ : PrimitiveOddFamily p.val =>
      shortMagnitude p.val χ^2*(if shortMagnitude p.val χ ≤ ε then 1 else 0)) ≤
      ε^(1/2 : ℝ)*magnitudeMoment (3/2) (shortMagnitude p.val) := by
  rw [lower_indicator_eq]
  exact FiniteMagnitudeDecorrelation.lower_square_mass_bound _ (short_magnitude_nonneg p.val) ε hε

theorem lower_square_mass_tendsto_zero {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun p : OddPrimeBase => uniformAverage (fun χ : PrimitiveOddFamily p.val =>
      shortMagnitude p.val χ^2*(if shortMagnitude p.val χ ≤ ε then 1 else 0)))
      oddPrimeAtTop (𝓝 0) := by
  simp_rw [lower_indicator_eq]
  exact FiniteMagnitudeDecorrelation.lower_square_mass_tendsto_zero
    (fun p : OddPrimeBase => shortMagnitude p.val) (fun p => short_magnitude_nonneg p.val)
    ε hε short_moment_tendsto_zero

theorem upper_square_mass_tendsto_one {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun p : OddPrimeBase => uniformAverage (fun χ : PrimitiveOddFamily p.val =>
      shortMagnitude p.val χ^2*(if ε < shortMagnitude p.val χ then 1 else 0)))
      oddPrimeAtTop (𝓝 1) := by
  simp_rw [upper_indicator_eq]
  exact FiniteMagnitudeDecorrelation.upper_square_mass_tendsto_one
    (fun p : OddPrimeBase => shortMagnitude p.val) (fun p => short_magnitude_nonneg p.val)
    (fun p => short_magnitude_second_moment p.property.1 p.property.2)
    ε hε short_moment_tendsto_zero

/-- All four limit clauses of Corollary 12 on the same complete odd-prime
filter, including the continuing excess in the squared magnitudes. -/
theorem square_mass_concentration {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun p : OddPrimeBase =>
      (Fintype.card {χ : PrimitiveOddFamily p.val // ε < shortMagnitude p.val χ} : ℝ) /
        (Fintype.card (PrimitiveOddFamily p.val) : ℝ)) oddPrimeAtTop (𝓝 0) ∧
    Tendsto (fun p : OddPrimeBase => uniformAverage (fun χ : PrimitiveOddFamily p.val =>
      shortMagnitude p.val χ^2*(if ε < shortMagnitude p.val χ then 1 else 0)))
      oddPrimeAtTop (𝓝 1) ∧
    Tendsto (fun p : OddPrimeBase =>
      uniformAverage (fun χ : PrimitiveOddFamily p.val => shortMagnitude p.val χ^2*lMagnitude p.val χ^2) /
      (uniformAverage (fun χ : PrimitiveOddFamily p.val => shortMagnitude p.val χ^2)*
       uniformAverage (fun χ : PrimitiveOddFamily p.val => lMagnitude p.val χ^2)))
      oddPrimeAtTop (𝓝 3) ∧
    Tendsto (fun p : OddPrimeBase =>
      magnitudeCovariance (fun χ : PrimitiveOddFamily p.val => shortMagnitude p.val χ^2)
        (fun χ : PrimitiveOddFamily p.val => lMagnitude p.val χ^2))
      oddPrimeAtTop (𝓝 (Real.pi^2/3)) :=
  ⟨tail_proportion_tendsto_zero hε,upper_square_mass_tendsto_one hε,
    mixed_magnitude_square_ratio_limit,square_magnitude_covariance_limit⟩

/-- The upper bound printed at the end of display 080 itself tends to zero. -/
theorem lower_square_mass_upper_bound_tendsto_zero (ε : ℝ) :
    Tendsto (fun p : OddPrimeBase => ε^(1/2 : ℝ)*magnitudeMoment (3/2) (shortMagnitude p.val))
      oddPrimeAtTop (𝓝 0) := by
  simpa [magnitudeMoment] using short_moment_tendsto_zero.const_mul (ε^(1/2 : ℝ))

end NField.Alignment.MagnitudeActualConcentration

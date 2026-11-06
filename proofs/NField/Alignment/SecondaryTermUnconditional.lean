/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.SaffariVaughanDistribution
import NField.Alignment.MagnitudeSecondaryUnconditional

/-! # The continuous and finite secondary terms without analytic premises -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.SecondaryTermUnconditional
open SecondaryCapacityAnalyticInputs SecondaryCapacityLedger GcdLcmCapacity
  PrimeSecondaryCoefficient PrimeCarryEnergyBridge

/-- Title: `Weighted fractional parts`. -/
theorem weighted_fractional_parts : WeightedFractionalPartsEstimate :=
  SecondaryCapacityAnalyticInputs.weighted_fractional_parts
    SaffariVaughanDistribution.saffari_vaughan_distribution

/-- Title: `Fractional-floor asymptotic`. -/
theorem fractional_floor_asymptotic :
    EventualErrorBound fractionalFloorTerm fractionalFloorMain
      secondaryCapacityRemainderScale :=
  SecondaryCapacityAnalyticInputs.fractional_floor_asymptotic
    SaffariVaughanDistribution.saffari_vaughan_distribution

/-- Title: `Continuous secondary coefficient`. -/
theorem continuous_secondary_coefficient :
    EventualErrorBound continuousCapacity continuousCapacityMain
      secondaryCapacityRemainderScale :=
  SecondaryCapacityAnalyticInputs.continuous_secondary_coefficient
    SaffariVaughanDistribution.saffari_vaughan_distribution

/-- Title: `Secondary term for the square GCD and LCM sum`. -/
theorem secondary_term_for_gcd_lcm_square :
    EventualErrorBound gcdLcmSquareSum gcdLcmSquareMain
      (fun N => 3 * secondaryCapacityRemainderScale N) :=
  SecondaryCapacityAnalyticInputs.secondary_term_for_gcd_lcm_square
    SaffariVaughanDistribution.saffari_vaughan_distribution

/-- Title: `Secondary term for the triangular GCD and LCM sum`. -/
theorem secondary_term_for_gcd_lcm_triangular :
    EventualErrorBound gcdLcmTriangularSum gcdLcmTriangularMain
      (fun N => (3 / 2 : ℝ) * secondaryCapacityRemainderScale N) :=
  SecondaryCapacityAnalyticInputs.secondary_term_for_gcd_lcm_triangular
    SaffariVaughanDistribution.saffari_vaughan_distribution

/-- Title: `Finite secondary coefficient`. -/
theorem finite_secondary_coefficient :
    PrimeEventualErrorBound primeCollisionEnergy primeDisplayedSecondaryMain
      (fun p => (p : ℝ)^2 * primePrintedSamplingScale p) :=
  MagnitudeSecondaryUnconditional.energy_secondary_expansion

end NField.Alignment.SecondaryTermUnconditional

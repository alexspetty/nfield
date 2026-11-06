/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.SecondaryTermUnconditional
import NField.Alignment.SquareLockCountBound
import NField.Alignment.LiveCarrierDamping

/-! # The square-lock and live-sector estimates without analytic premises -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.SecondaryLocalizationUnconditional
open SquareLockCarrierMass LiveCarrierDamping PrimeCarrierDamping
  PrimeSecondaryCoefficient PrimeCarryEnergyBridge DedekindInverseResidueTransform
  InverseResidueHarmonicRangeSplit InverseResiduePrefixCompletion

/-- Title: `Square-lock localization`. -/
theorem square_lock_localization :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ p C, p.Prime → 1 ≤ C → 2*C ≤ p →
      squareLockCollarMass p C ≤ constant *
        (((C : ℝ)/(p : ℝ))*(Real.log (2*p))^3 +
          Real.rpow p (-1/3 : ℝ)*(Real.log (2*p))^3) :=
  SquareLockCarrierMass.square_lock_localization SquareLockCountBound.square_lock_count_estimate

/-- Title: `Live-sector damping`. -/
theorem live_sector_damping :
    CarrierFamilyPrimeEventualBound liveCarrierSet logarithmicCarrierReservoirScale :=
  live_sector_damping_from_analytic_inputs
    (korolevAmbientInverseResidueEstimate_of_partials
      (uniformInverseSawPartialHarmonicEstimate KorolevRangeEstimate.korolev_range_estimate
        (completed_inverse_prefixes KloostermanGlobalBound.weil_estermann_inverse_prefix_estimate)
        CompletedPrefixDivisorGrowth.standard_completed_prefix_divisor_growth))
    SquareLockCountBound.square_lock_count_estimate

/--
Title: `Secondary coefficient under signed damping`.

The manuscript's open signed-damping hypothesis remains explicit.
-/
theorem finite_secondary_coefficient_under_signed_damping
    (hsigned : SignedDedekindCarrierDamping) :
    PrimeEventualErrorBound primeCollisionEnergy primeDisplayedSecondaryMain
      (fun p => (p : ℝ)^2*primeContinuousScale p) :=
  finite_secondary_coefficient_under_log_sampling
    SecondaryTermUnconditional.continuous_secondary_coefficient
    (sampling_conditional_on_signed_damping hsigned)

end NField.Alignment.SecondaryLocalizationUnconditional

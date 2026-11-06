/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevRangeEstimate
import NField.Alignment.KloostermanGlobalBound
import NField.Alignment.CompletedPrefixDivisorGrowth
import NField.Alignment.SecondaryCapacityAnalyticInputs
import NField.Alignment.PrimeCarrierDamping

/-! # The strongest existing secondary-energy estimate

Korolev, complete-sum completion and divisor growth are proved inputs.
Only the Saffari--Vaughan distribution estimate remains a premise.
-/

namespace NField.Alignment.MagnitudeSecondaryTransfer

open PrimeSecondaryCoefficient WeightedFractionalPartTransfer
  DedekindInverseResidueTransform InverseResidueHarmonicRangeSplit
  InverseResiduePrefixCompletion

theorem energy_secondary_from_saffari_vaughan
    (hSV : SaffariVaughanDistributionEstimate) :
    PrimeEventualErrorBound primeCollisionEnergy primeDisplayedSecondaryMain
      (fun p => (p : ℝ)^2*primePrintedSamplingScale p) :=
  PrimeSecondaryCoefficient.finite_secondary_coefficient_printed
    (SecondaryCapacityAnalyticInputs.continuous_secondary_coefficient hSV)
    (PrimeCarrierDamping.primeSamplingDefect_strict_bound_from_analytic_inputs
      (korolevAmbientInverseResidueEstimate_of_partials
        (uniformInverseSawPartialHarmonicEstimate KorolevRangeEstimate.korolev_range_estimate
          (completed_inverse_prefixes KloostermanGlobalBound.weil_estermann_inverse_prefix_estimate)
          CompletedPrefixDivisorGrowth.standard_completed_prefix_divisor_growth)))

end NField.Alignment.MagnitudeSecondaryTransfer

/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.SaffariVaughanDistribution
import NField.Alignment.MagnitudeSecondaryAsymptotics

/-! # Unconditional secondary expansions of the actual magnitude family -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.MagnitudeSecondaryUnconditional
open scoped Topology
open Filter Asymptotics MagnitudeSecondaryTransfer MagnitudeCubicLimits
  PrimeSecondaryCoefficient PrimeCarryEnergyBridge PrimeSquareMagnitudeFamily
  SpectralRepulsion FiniteMagnitudeDecorrelation

/-- Both printed actual-family secondary expansions, without analytic premises. -/
theorem magnitude_secondary_expansions :
    IsBigO oddPrimeAtTop
      (fun p : OddPrimeBase =>
        uniformAverage (fun χ : PrimitiveOddFamily p.val =>
          shortMagnitude p.val χ^2*lMagnitude p.val χ^2) -
            (Real.pi^2/2-(Real.log (p.val : ℝ))^2/(2*(p.val : ℝ))))
      magnitudeSecondaryScale ∧
    IsBigO oddPrimeAtTop
      (fun p : OddPrimeBase =>
        uniformAverage (fun χ : PrimitiveOddFamily p.val =>
          shortMagnitude p.val χ^2*lMagnitude p.val χ^2) /
          (uniformAverage (fun χ : PrimitiveOddFamily p.val => shortMagnitude p.val χ^2)*
            uniformAverage (fun χ : PrimitiveOddFamily p.val => lMagnitude p.val χ^2)) -
            (3-3/Real.pi^2*(Real.log (p.val : ℝ))^2/(p.val : ℝ)))
      magnitudeSecondaryScale :=
  magnitude_secondary_expansions_from_saffari_vaughan
    SaffariVaughanDistribution.saffari_vaughan_distribution

/--
Title: `Collision-energy secondary expansion`.

The literal secondary coefficient and the printed logarithmic remainder.
-/
theorem energy_secondary_expansion :
    PrimeEventualErrorBound primeCollisionEnergy primeDisplayedSecondaryMain
      (fun p => (p:ℝ)^2*primePrintedSamplingScale p) :=
  energy_secondary_from_saffari_vaughan
    SaffariVaughanDistribution.saffari_vaughan_distribution

/--
Title: `Mixed square-moment secondary expansion`.
-/
theorem mixed_secondary_expansion :
    IsBigO oddPrimeAtTop
      (fun p : OddPrimeBase =>
        uniformAverage (fun χ : PrimitiveOddFamily p.val =>
          shortMagnitude p.val χ^2*lMagnitude p.val χ^2) -
            (Real.pi^2/2-(Real.log (p.val : ℝ))^2/(2*(p.val : ℝ))))
      magnitudeSecondaryScale :=
  magnitude_secondary_expansions.1

/--
Title: `Square-ratio secondary expansion`.
-/
theorem ratio_secondary_expansion :
    IsBigO oddPrimeAtTop
      (fun p : OddPrimeBase =>
        uniformAverage (fun χ : PrimitiveOddFamily p.val =>
          shortMagnitude p.val χ^2*lMagnitude p.val χ^2) /
          (uniformAverage (fun χ : PrimitiveOddFamily p.val => shortMagnitude p.val χ^2)*
            uniformAverage (fun χ : PrimitiveOddFamily p.val => lMagnitude p.val χ^2)) -
            (3-3/Real.pi^2*(Real.log (p.val : ℝ))^2/(p.val : ℝ)))
      magnitudeSecondaryScale :=
  magnitude_secondary_expansions.2

end NField.Alignment.MagnitudeSecondaryUnconditional

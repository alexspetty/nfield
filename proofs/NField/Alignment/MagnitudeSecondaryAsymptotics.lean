/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.MagnitudeSecondaryScale
import NField.Alignment.MagnitudeSecondaryEnergy
import NField.Alignment.MagnitudeCubicLimits

/-! # The two literal magnitude secondary expansions from the energy theorem

The source's exact mixed average and exact square ratio are retained. This
completes their rational-denominator transfer. The final source-level premise
is explicitly Saffari--Vaughan; it is not discharged by this module.
-/

noncomputable section
namespace NField.Alignment.MagnitudeSecondaryTransfer

open scoped Topology
open Filter Asymptotics
open MagnitudeCubicLimits PrimeSecondaryCoefficient PrimeCarryEnergyBridge
  PrimeSquareMagnitudeFamily SpectralRepulsion FiniteMagnitudeDecorrelation
  WeightedFractionalPartTransfer

def magnitudeSecondaryScale (p : OddPrimeBase) : ℝ :=
  (Real.log (2*(p.val : ℝ)))^2 /
    ((p.val : ℝ)*Real.log (Real.log (3*(p.val : ℝ))))

theorem magnitude_secondary_scale_eq (p : OddPrimeBase) :
    magnitudeSecondaryScale p = primePrintedSamplingScale p.val/(p.val : ℝ) := by
  unfold magnitudeSecondaryScale primePrintedSamplingScale
  ring

theorem mixed_secondary_of_energy
    (henergy : PrimeEventualErrorBound primeCollisionEnergy primeDisplayedSecondaryMain
      (fun p => (p : ℝ)^2*primePrintedSamplingScale p)) :
    IsBigO oddPrimeAtTop
      (fun p : OddPrimeBase =>
        uniformAverage (fun χ : PrimitiveOddFamily p.val =>
          shortMagnitude p.val χ^2*lMagnitude p.val χ^2) -
            (Real.pi^2/2-(Real.log (p.val : ℝ))^2/(2*(p.val : ℝ))))
      magnitudeSecondaryScale := by
  obtain ⟨C,hC,T,henergy⟩ := henergy
  apply isBigO_iff.mpr
  refine ⟨Real.pi^2*C+Real.pi^2+1, ?_⟩
  have hT : ∀ᶠ p : OddPrimeBase in oddPrimeAtTop, max T 3 ≤ p.val :=
    Filter.tendsto_comap.eventually (eventually_ge_atTop (max T 3))
  filter_upwards [hT] with p hpT
  have hp3 : 3 ≤ p.val := (le_max_right T 3).trans hpT
  have hp0 : (0 : ℝ) < p.val := by exact_mod_cast p.property.1.pos
  obtain ⟨hS,hL⟩ := printed_scale_bounds p.val hp3
  have hE := henergy p.val ((le_max_left T 3).trans hpT) p.property.1
  have hE' : |primeCarryEnergy p.property.1-
      ((p.val : ℝ)^3-(Real.pi^2)⁻¹*(p.val : ℝ)^2*(Real.log (p.val : ℝ))^2)| ≤
        C*(p.val : ℝ)^2*primePrintedSamplingScale p.val := by
    simpa [primeCollisionEnergy,primeDisplayedSecondaryMain,p.property.1,
      ExactSamplingReservoirBridge.collisionEnergy_eq_primeCarryEnergy,mul_assoc] using hE
  rw [magnitude_secondary_scale_eq]
  rw [Real.norm_of_nonneg (div_nonneg (by linarith : 0 ≤ primePrintedSamplingScale p.val) hp0.le)]
  rw [Real.norm_eq_abs,mixed_magnitude_second_moment p.property.1 p.property.2]
  simpa only [mul_div_assoc] using mixed_secondary_transfer
    (show (2 : ℝ) ≤ p.val by exact_mod_cast p.property.1.two_le)
    (show 0 < Real.pi^2 by positivity) hS (sq_nonneg _) hL hC hE'

theorem ratio_secondary_of_energy
    (henergy : PrimeEventualErrorBound primeCollisionEnergy primeDisplayedSecondaryMain
      (fun p => (p : ℝ)^2*primePrintedSamplingScale p)) :
    IsBigO oddPrimeAtTop
      (fun p : OddPrimeBase =>
        uniformAverage (fun χ : PrimitiveOddFamily p.val =>
          shortMagnitude p.val χ^2*lMagnitude p.val χ^2) /
          (uniformAverage (fun χ : PrimitiveOddFamily p.val => shortMagnitude p.val χ^2)*
            uniformAverage (fun χ : PrimitiveOddFamily p.val => lMagnitude p.val χ^2)) -
            (3-3/Real.pi^2*(Real.log (p.val : ℝ))^2/(p.val : ℝ)))
      magnitudeSecondaryScale := by
  obtain ⟨C,hC,T,henergy⟩ := henergy
  apply isBigO_iff.mpr
  refine ⟨12*C+24+24/Real.pi^2, ?_⟩
  have hT : ∀ᶠ p : OddPrimeBase in oddPrimeAtTop, max T 3 ≤ p.val :=
    Filter.tendsto_comap.eventually (eventually_ge_atTop (max T 3))
  filter_upwards [hT] with p hpT
  have hp3 : 3 ≤ p.val := (le_max_right T 3).trans hpT
  have hp0 : (0 : ℝ) < p.val := by exact_mod_cast p.property.1.pos
  obtain ⟨hS,hL⟩ := printed_scale_bounds p.val hp3
  have hE := henergy p.val ((le_max_left T 3).trans hpT) p.property.1
  have hE' : |primeCarryEnergy p.property.1-
      ((p.val : ℝ)^3-(Real.pi^2)⁻¹*(p.val : ℝ)^2*(Real.log (p.val : ℝ))^2)| ≤
        C*(p.val : ℝ)^2*primePrintedSamplingScale p.val := by
    simpa [primeCollisionEnergy,primeDisplayedSecondaryMain,p.property.1,
      ExactSamplingReservoirBridge.collisionEnergy_eq_primeCarryEnergy,mul_assoc] using hE
  rw [magnitude_secondary_scale_eq]
  rw [Real.norm_of_nonneg (div_nonneg (by linarith : 0 ≤ primePrintedSamplingScale p.val) hp0.le)]
  rw [Real.norm_eq_abs,mixed_magnitude_square_ratio p.property.1 p.property.2]
  simpa only [mul_div_assoc] using ratio_secondary_transfer
    (show (2 : ℝ) ≤ p.val by exact_mod_cast p.property.1.two_le)
    (show 0 < Real.pi^2 by positivity) hS (sq_nonneg _) hL hC hE'

/-- Both printed expansions have only the remaining source distribution
estimate as a premise; the complete primitive family is used literally. -/
theorem magnitude_secondary_expansions_from_saffari_vaughan
    (hSV : SaffariVaughanDistributionEstimate) :
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
  ⟨mixed_secondary_of_energy (energy_secondary_from_saffari_vaughan hSV),
    ratio_secondary_of_energy (energy_secondary_from_saffari_vaughan hSV)⟩

end NField.Alignment.MagnitudeSecondaryTransfer

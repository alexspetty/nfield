/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperLogarithmicSum

/-!
# Dirichlet-series Parseval for the actual smooth Steinhaus sums

The exponential substitution transports both integrability and the integral
identity from the logarithmic smooth sum to its full positive-axis energy.
At real part one half, Parseval gives the actual random Euler product on
the full vertical line, including its squared denominator and 1/(2*pi).
Nonnegativity then bounds the manuscript's finite inverse integral. Phase
integrability follows from the jointly integrable spectral density.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperDirichletParseval

open MeasureTheory Set SteinhausMoment HarperLogarithmicSum HarperEulerIntegral
  HarperSmoothIntervals HarperMainIntegral

def smoothEnergyDensity (P : ℝ) (ω : PhaseSpace) (t : ℝ) : ℝ :=
  ‖smoothSum t P (fun n => steinhaus n ω)‖^2/t^2

def smoothEnergy (P : ℝ) (ω : PhaseSpace) : ℝ :=
  ∫ t in Ioi (0 : ℝ), smoothEnergyDensity P ω t

theorem smoothEnergyDensity_nonneg (P : ℝ) (ω : PhaseSpace) (t : ℝ) :
    0 ≤ smoothEnergyDensity P ω t := div_nonneg (sq_nonneg _) (sq_nonneg _)

private theorem exp_neg_deriv :
    ∀ u ∈ (univ : Set ℝ), HasDerivWithinAt (fun u : ℝ => Real.exp (-u))
      (-Real.exp (-u)) univ u := by
  intro u _
  simpa only [mul_neg_one] using!
    ((Real.hasDerivAt_exp (-u)).comp u (hasDerivAt_neg u)).hasDerivWithinAt (s := univ)

private theorem exp_neg_image :
    (fun u : ℝ => Real.exp (-u)) '' univ = Ioi (0 : ℝ) := by
  change (Real.exp ∘ Neg.neg) '' univ = _
  rw [image_comp, image_univ_of_surjective neg_surjective, image_univ, Real.range_exp]

private theorem exp_neg_injOn :
    InjOn (fun u : ℝ => Real.exp (-u)) univ :=
  Real.exp_injective.injOn.comp neg_injective.injOn (univ.mapsTo_univ _)

theorem smoothEnergyDensity_change (P : ℝ) (ω : PhaseSpace) (u : ℝ) :
    |-Real.exp (-u)| • smoothEnergyDensity P ω (Real.exp (-u)) =
      ‖logarithmicSum P (1/2) ω u‖^2 := by
  rw [abs_neg, abs_of_pos (Real.exp_pos _), smul_eq_mul, smoothEnergyDensity,
    logarithmicSum, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow]
  rw [← Real.exp_nat_mul ((1/2)*u) 2]
  norm_num only [Nat.cast_ofNat]
  have hmul : (2 : ℝ)*((1/2)*u) = u := by ring
  rw [hmul, Real.exp_neg]
  field_simp

theorem smoothEnergyDensity_integrable (P : ℝ) (ω : PhaseSpace) :
    IntegrableOn (smoothEnergyDensity P ω) (Ioi (0 : ℝ)) := by
  rw [← exp_neg_image, integrableOn_image_iff_integrableOn_abs_deriv_smul
    MeasurableSet.univ exp_neg_deriv exp_neg_injOn]
  simp_rw [smoothEnergyDensity_change]
  rw [integrableOn_univ]
  exact (memLp_two_iff_integrable_sq_norm
    (logarithmicSum_measurable P (1/2) ω).aestronglyMeasurable).mp
    (logarithmicSum_memLp P (by norm_num : (0 : ℝ) < 1/2) ω)

theorem smoothEnergy_eq_logarithmic (P : ℝ) (ω : PhaseSpace) :
    smoothEnergy P ω = ∫ u : ℝ, ‖logarithmicSum P (1/2) ω u‖^2 := by
  rw [smoothEnergy, ← exp_neg_image, integral_image_eq_integral_abs_deriv_smul
    MeasurableSet.univ exp_neg_deriv exp_neg_injOn]
  simp_rw [smoothEnergyDensity_change]
  rw [setIntegral_univ]

theorem smoothEnergy_parseval (P : ℝ) (ω : PhaseSpace) :
    smoothEnergy P ω = (1/(2*Real.pi))*spectralIntegral P (1/2) ω := by
  rw [smoothEnergy_eq_logarithmic]
  exact logarithmicSum_parseval P (by norm_num : (0 : ℝ) < 1/2) ω

theorem smoothSum_parseval (P : ℝ) (ω : PhaseSpace) :
    (∫ z in Ioi (0 : ℝ), ‖smoothSum z P (fun n => steinhaus n ω)‖^2/z^2) =
      (1/(2*Real.pi)) * ∫ t : ℝ,
        ‖HarperRandomEulerProduct.eulerProduct P (linePoint (1/2) t) ω‖^2 /
          ‖linePoint (1/2) t‖^2 := by
  simpa only [smoothEnergy, smoothEnergyDensity, spectralIntegral, spectralDensity_eq] using
    smoothEnergy_parseval P ω

theorem smoothEnergy_integrable (P : ℝ) : Integrable (smoothEnergy P) phaseMeasure := by
  have he : smoothEnergy P = fun ω => (1/(2*Real.pi))*spectralIntegral P (1/2) ω :=
    funext (smoothEnergy_parseval P)
  rw [he]
  exact (spectralIntegral_integrable P (by norm_num : (0 : ℝ) < 1/2)).const_mul _

theorem smoothInverseIntegral_le_energy {x y : ℝ} (hy : 0 < y) (hyx : y ≤ x)
    (P : ℝ) (ω : PhaseSpace) : smoothInverseIntegral x P y ω ≤ smoothEnergy P ω := by
  rw [smoothInverseIntegral, intervalIntegral.integral_of_le ((le_div_iff₀ hy).mpr (by simpa))]
  apply setIntegral_mono_set (smoothEnergyDensity_integrable P ω)
    (Filter.Eventually.of_forall (smoothEnergyDensity_nonneg P ω))
  exact Filter.Eventually.of_forall (fun _ ht => lt_trans zero_lt_one ht.1)

theorem smoothInverseIntegral_le_spectral {x y : ℝ} (hy : 0 < y) (hyx : y ≤ x)
    (P : ℝ) (ω : PhaseSpace) :
    smoothInverseIntegral x P y ω ≤ (1/(2*Real.pi))*spectralIntegral P (1/2) ω := by
  rw [← smoothEnergy_parseval]
  exact smoothInverseIntegral_le_energy hy hyx P ω

end NField.Alignment.HarperDirichletParseval

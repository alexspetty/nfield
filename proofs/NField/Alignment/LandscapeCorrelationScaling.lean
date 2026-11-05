/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.FiniteMagnitudeDecorrelation
import NField.Alignment.LandscapeActualSpectrum
import NField.Alignment.SpectralCharacterPairs

/-! # The exact invariance of the source's finite Pearson correlation -/

noncomputable section
namespace NField.Alignment.LandscapeCorrelationScaling
open SpectralRepulsion FiniteMagnitudeDecorrelation LandscapeActualSpectrum
  SpectralCharacterPairs CollisionSpectrumLandscape

theorem variance_mul_left {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ℝ) (Y : ι → ℝ) :
    uniformVariance (fun i => c * Y i) = c ^ 2 * uniformVariance Y := by
  rw [variance_eq_second_sub_square, variance_eq_second_sub_square,
    uniformAverage_mul_left]
  simp_rw [mul_pow]
  rw [uniformAverage_mul_left]
  ring

theorem correlation_mul_pos {ι : Type*} [Fintype ι] [Nonempty ι]
    (X Y : ι → ℝ) (c : ℝ) (hc : 0 < c) :
    magnitudeCorrelation X (fun i => c * Y i) = magnitudeCorrelation X Y := by
  have hcov : magnitudeCovariance X (fun i => c * Y i) = c * magnitudeCovariance X Y := by
    unfold magnitudeCovariance
    rw [uniformAverage_mul_left]
    have he : (fun i => X i * (c * Y i)) = fun i => c * (X i * Y i) := by
      funext i
      ring
    rw [he, uniformAverage_mul_left]
    ring
  unfold magnitudeCorrelation
  rw [hcov, variance_mul_left]
  have he : uniformVariance X * (c ^ 2 * uniformVariance Y) =
      c ^ 2 * (uniformVariance X * uniformVariance Y) := by ring
  rw [he, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]
  exact mul_div_mul_left _ _ hc.ne'

theorem actual_bernoulli_l_correlation {b : ℕ} [NeZero b] [NeZero (b ^ 2)]
    (hb : b.Prime) (hbodd : b ≠ 2) :
    magnitudeCorrelation (fun χ : PrimitiveOddFamily b => ‖initialCharacterSum b χ.val‖)
      (fun χ => ‖generalizedBernoulliOne χ.val⁻¹‖) =
    magnitudeCorrelation (fun χ : PrimitiveOddFamily b => ‖initialCharacterSum b χ.val‖)
      (fun χ => ‖DirichletCharacter.LFunction χ.val 1‖) := by
  letI : Nonempty (PrimitiveOddFamily b) := family_nonempty hb hbodd
  have he : (fun χ : PrimitiveOddFamily b => ‖generalizedBernoulliOne χ.val⁻¹‖) =
      fun χ => (b : ℝ) / Real.pi * ‖DirichletCharacter.LFunction χ.val 1‖ := by
    funext χ
    exact bernoulli_l_value_norm hb χ.val χ.property.1 χ.property.2
  rw [he]
  apply correlation_mul_pos
  exact div_pos (Nat.cast_pos.mpr hb.pos) Real.pi_pos

end NField.Alignment.LandscapeCorrelationScaling

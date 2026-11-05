/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimeSquareMagnitudeBernoulliMoment

/-!
# Literal finite displays in the magnitude paper

Retain both equalities in the unnormalized short-square total, and
specialize the finite Holder, covariance and Pearson inequalities to the
actual primitive odd family. The decay criterion keeps its stated third
moment and variance hypotheses; no vanishing fractional moment is claimed.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.MagnitudeFiniteDisplayCorrespondence

open scoped BigOperators
open PrimeSquareMagnitudeFamily FiniteMagnitudeDecorrelation SpectralRepulsion
  MagnitudeMomentArithmetic

theorem short_square_total_chain {p : ℕ} [NeZero p] [NeZero (p^2)]
    (hp : p.Prime) (hpodd : p ≠ 2) :
    (∑ χ : PrimitiveOddFamily p, ‖shortSum p χ‖^2) =
        (p : ℝ)*((p : ℝ)-1)^2/2 ∧
      (p : ℝ)*((p : ℝ)-1)^2/2 = (p : ℝ)*(Fintype.card (PrimitiveOddFamily p) : ℝ) := by
  constructor
  · simpa only [Nat.cast_sub hp.one_lt.le, Nat.cast_one] using shortSum_second_moment_total hp
  · rw [family_population hp hpodd, Nat.cast_pow, Nat.cast_sub hp.one_lt.le, Nat.cast_one]
    ring

private theorem third_moment_le {p : ℕ} [NeZero (p^2)] {M : ℝ}
    (h : uniformAverage (fun χ : PrimitiveOddFamily p => lMagnitude p χ ^ 3) ≤ M) :
    magnitudeMoment 3 (lMagnitude p) ≤ M := by
  have he (x : ℝ) : x^(3 : ℝ) = x^(3 : ℕ) := Real.rpow_natCast x 3
  simpa only [magnitudeMoment, he] using h

theorem mixed_magnitude_bound {p : ℕ} [NeZero p] [NeZero (p^2)]
    (hp : p.Prime) (hpodd : p ≠ 2) {M : ℝ}
    (hthird : uniformAverage (fun χ : PrimitiveOddFamily p => lMagnitude p χ ^ 3) ≤ M) :
    uniformAverage (fun χ : PrimitiveOddFamily p => shortMagnitude p χ * lMagnitude p χ) ≤
      magnitudeMoment (3/2) (shortMagnitude p)^(2/3 : ℝ) * M^(1/3 : ℝ) := by
  letI := family_nonempty hp hpodd
  have h := average_holder_three_halves (shortMagnitude p) (lMagnitude p)
    (short_magnitude_nonneg p) (l_magnitude_nonneg p)
  exact h.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (moment_nonneg 3 _ (l_magnitude_nonneg p))
      (third_moment_le hthird) (by norm_num))
    (Real.rpow_nonneg (moment_nonneg (3/2) _ (short_magnitude_nonneg p)) _))

theorem centered_magnitude_bound {p : ℕ} [NeZero p] [NeZero (p^2)]
    (hp : p.Prime) (hpodd : p ≠ 2) {M : ℝ}
    (hthird : uniformAverage (fun χ : PrimitiveOddFamily p => lMagnitude p χ ^ 3) ≤ M) :
    |uniformAverage (fun χ : PrimitiveOddFamily p => shortMagnitude p χ * lMagnitude p χ) -
      uniformAverage (shortMagnitude p) * uniformAverage (lMagnitude p)| ≤
      (M^(1/3 : ℝ) + Real.sqrt (marginalL p)) *
        magnitudeMoment (3/2) (shortMagnitude p)^(2/3 : ℝ) := by
  letI := family_nonempty hp hpodd
  exact covariance_bound _ _ (short_magnitude_nonneg p) (l_magnitude_nonneg p)
    (marginalL p) M (l_magnitude_second_moment hp hpodd) (third_moment_le hthird)

theorem family_fractional_correlation_bound {p : ℕ} [NeZero p] [NeZero (p^2)]
    (hp : p.Prime) (hpodd : p ≠ 2) {M v : ℝ} (hv : 0 < v)
    (hthird : uniformAverage (fun χ : PrimitiveOddFamily p => lMagnitude p χ ^ 3) ≤ M)
    (hvariance : v ≤ uniformVariance (lMagnitude p))
    (hsmall : magnitudeMoment (3/2) (shortMagnitude p) < 1) :
    |familyCorrelation p| ≤
      ((M^(1/3 : ℝ) + Real.sqrt (marginalL p)) *
        magnitudeMoment (3/2) (shortMagnitude p)^(2/3 : ℝ)) /
        Real.sqrt (v * (1 - magnitudeMoment (3/2) (shortMagnitude p)^(4/3 : ℝ))) := by
  letI := family_nonempty hp hpodd
  exact fractional_correlation_bound _ _ (short_magnitude_nonneg p) (l_magnitude_nonneg p)
    (marginalL p) M v hv (short_magnitude_second_moment hp hpodd)
    (l_magnitude_second_moment hp hpodd) (third_moment_le hthird) hvariance hsmall

end NField.Alignment.MagnitudeFiniteDisplayCorrespondence

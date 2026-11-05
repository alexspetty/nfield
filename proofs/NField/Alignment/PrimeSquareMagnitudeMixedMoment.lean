/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimeSquareMagnitudeBernoulliMoment
import NField.Alignment.CubicEnergyCharacterMoment

/-!
# The mixed magnitude moment of collision energy

These exact finite identities use the complete primitive odd character
family, the manuscript's conjugated short sum and its concrete class-centered
floor-jump energy. The proof reindexes the existing native character moment
and applies the two already proved marginal normalizations. No asymptotic
energy or moment estimate is an input, and no limiting rate is asserted.
-/

namespace NField.Alignment.PrimeSquareMagnitudeFamily

open scoped BigOperators
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CubicEnergyCharacterMoment
open NField.Alignment.PrimeCarryEnergyBridge
open NField.Alignment.PrimeSquareCollisionWindow
open NField.Alignment.PrimeSquareBoundaryFlux
open NField.Alignment.SpectralRepulsion
open NField.Alignment.MagnitudeMomentArithmetic

/-- The complete primitive odd short-sum/L-value square total, with the
manuscript's conjugated short sum and its class-centered carry energy. -/
theorem short_l_second_moment_total {p : ℕ} [NeZero p] [NeZero (p ^ 2)]
    (hp : p.Prime) (hpodd : p ≠ 2) :
    (∑ χ : PrimitiveOddFamily p, ‖shortSum p χ‖ ^ 2 * lMagnitude p χ ^ 2) =
      Real.pi ^ 2 * ((p - 1 : ℕ) : ℝ) / (4 * (p : ℝ)) *
        primeCarryEnergy hp := by
  classical
  have h := lValueWindowMoment_eq_primeCarryEnergy hp hpodd
  unfold lValueWindowMoment at h
  rw [← Finset.sum_filter] at h
  rw [Finset.sum_subtype (p := fun χ : Character (p ^ 2) => χ.IsPrimitive ∧ χ.Odd)
    (F := familyFintype p) _ (by simp) (fun χ =>
      Complex.normSq (DirichletCharacter.LFunction χ 1) *
        Complex.normSq (shortWindowSum hp χ))] at h
  calc
    (∑ χ : PrimitiveOddFamily p, ‖shortSum p χ‖ ^ 2 * lMagnitude p χ ^ 2) =
        ∑ χ : PrimitiveOddFamily p,
          Complex.normSq (DirichletCharacter.LFunction χ.val 1) *
            Complex.normSq (shortWindowSum hp χ.val) := by
      apply Finset.sum_congr rfl
      intro χ _
      unfold lMagnitude
      rw [shortSum_eq_conj_window hp, norm_star, Complex.sq_norm, Complex.sq_norm]
      ring
    _ = _ := h

/-- The actual mixed second moment in equation `eq:mixed-square`.
No sample-moment estimate is supplied as an input. -/
theorem mixed_magnitude_second_moment {p : ℕ} [NeZero p] [NeZero (p ^ 2)]
    (hp : p.Prime) (hpodd : p ≠ 2) :
    uniformAverage (fun χ : PrimitiveOddFamily p =>
        shortMagnitude p χ ^ 2 * lMagnitude p χ ^ 2) =
      Real.pi ^ 2 * primeCarryEnergy hp /
        (2 * (p : ℝ) ^ 2 * ((p : ℝ) - 1)) := by
  classical
  unfold uniformAverage shortMagnitude
  simp_rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg p), div_mul_eq_mul_div]
  rw [← Finset.sum_div, short_l_second_moment_total hp hpodd,
    family_population hp hpodd]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have := (show (1 : ℝ) < p by exact_mod_cast hp.one_lt)
    linarith
  push_cast [Nat.cast_sub hp.one_le]
  field_simp
  ring

/-- The actual quotient of mixed and marginal square averages in
equation `eq:ratio`, expressed solely through centered collision energy. -/
theorem mixed_magnitude_square_ratio {p : ℕ} [NeZero p] [NeZero (p ^ 2)]
    (hp : p.Prime) (hpodd : p ≠ 2) :
    uniformAverage (fun χ : PrimitiveOddFamily p =>
        shortMagnitude p χ ^ 2 * lMagnitude p χ ^ 2) /
      (uniformAverage (fun χ : PrimitiveOddFamily p => shortMagnitude p χ ^ 2) *
       uniformAverage (fun χ : PrimitiveOddFamily p => lMagnitude p χ ^ 2)) =
      3 * primeCarryEnergy hp / (((p : ℝ) - 1) * ((p : ℝ) ^ 2 - 1)) := by
  rw [mixed_magnitude_second_moment hp hpodd,
    short_magnitude_second_moment hp hpodd, l_magnitude_second_moment hp hpodd,
    one_mul]
  exact mixed_square_ratio (p : ℝ) (primeCarryEnergy hp)
    (by exact_mod_cast hp.one_lt)

end NField.Alignment.PrimeSquareMagnitudeFamily

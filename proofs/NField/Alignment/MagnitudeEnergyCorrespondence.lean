/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.MagnitudeDefinitionCorrespondence
import NField.Alignment.PrimeSquareMagnitudeMixedMoment

/-!
# Literal energy and coefficient correspondence

The floor-jump statistic and its residue-class centering are the native
prime carry table. This module identifies the precise class mean and the
normalized primitive coefficient, and restricts Parseval to the complete
primitive odd family as displayed in Proposition 5.
-/

set_option autoImplicit false

namespace NField.Alignment.PrimeSquareMagnitudeFamily

open scoped BigOperators ComplexConjugate ZMod
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionFluctuationSum
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.CollisionTransformStrip
open NField.Alignment.CollisionTransform
open NField.Alignment.NeutralityTheorem
open NField.Alignment.CollisionSpectrumLandscape
open NField.Alignment.PrimeCarryEnergyBridge
open NField.Alignment.PrimeCarryFiberCentering
open NField.Alignment.PrimeCarrySpectralBridge
open NField.Alignment.PrimeSquareBoundaryFlux
open NField.Alignment.CarryBoundarySpectra
open NField.Alignment.TheCollisionSpectrum
open NField.Alignment.OddBernoulliMoments
open NField.Alignment.SpectralRepulsion
open NField.Alignment.MagnitudeMomentArithmetic
open NField.Alignment.FiniteMagnitudeDecorrelation

theorem collision_class_mean {p : ℕ} [NeZero p] [NeZero (allLagModulus p 1)]
    (hp : p.Prime) (u : UnitClass p) :
    fiberMean (coarseUnitReduction p 1) (allLagUnitTable p 1) u =
      (p : ℂ)⁻¹ * ∑ a : Fiber (coarseUnitReduction p 1) u,
        (fluctuationTable p a.val.val.val : ℂ) := by
  classical
  have hcard : Fintype.card (Fiber (coarseUnitReduction p 1) u) = p := by
    simpa using Fintype.card_congr (primeFiberEquiv hp u).symm
  unfold fiberMean
  rw [hcard]
  simp_rw [allLagUnitTable_one_eq_fluctuationTable hp]

theorem collision_fiber_iff_mod {p : ℕ} [NeZero p] [NeZero (allLagModulus p 1)]
    (a : UnitClass (allLagModulus p 1)) (u : UnitClass p) :
    coarseUnitReduction p 1 a = u ↔ a.val.val % p = u.val.val := by
  have hv : (coarseUnitReduction p 1 a).val.val = a.val.val % p := by
    unfold coarseUnitReduction
    rw [ZMod.unitsMap_val, ZMod.cast_eq_val, ZMod.val_natCast]
  constructor
  · intro h
    simpa only [h] using hv.symm
  · intro h
    apply Units.ext
    apply ZMod.val_injective
    exact hv.trans h

/-- The displayed normalized coefficient, including its sign, conjugation
and exact denominator. -/
theorem collision_coefficient_factorization {p : ℕ} [NeZero (p^2)]
    (hp : p.Prime) (χ : PrimitiveOddFamily p) :
    collisionCoefficient (primeCarryCentered hp) χ.val =
      -(bernoulliSum p χ * star (diagonalSum p χ)) /
        ((p : ℂ) * ((p : ℂ)-1)) := by
  have hcoef := collisionCoefficient_inv_eq_characterTransform
    (primeCarryCentered hp) χ.val⁻¹
  simp only [inv_inv] at hcoef
  rw [hcoef, primitive_characterTransform_factorization hp χ.val⁻¹
    (inverse_isPrimitive χ.property.1), inv_inv]
  have hbern : bernoulliOne χ.val⁻¹ = bernoulliSum p χ := by
    unfold bernoulliOne bernoulliSum generalizedBernoulliOne
    rw [sum_character_pairing_eq_units (fun x : ZMod (p^2) => (x.val : ℂ)) χ.val⁻¹]
  have hflux : lagOneBoundaryFlux hp χ.val = star (diagonalSum p χ) := by
    rw [diagonalSum_eq_conj_flux hp, star_star]
  rw [hbern, hflux, Nat.totient_prime_pow hp (by decide : 0 < 2)]
  push_cast [Nat.cast_sub hp.one_le]
  simp only [pow_one]
  ring

/-- Every coefficient omitted from the primitive odd family is zero. -/
theorem collision_coefficient_inactive_zero {p : ℕ} [NeZero p] [NeZero (p^2)]
    (hp : p.Prime) (hpodd : p ≠ 2) (χ : Character (p^2))
    (hχ : ¬ (χ.IsPrimitive ∧ χ.Odd)) :
    collisionCoefficient (primeCarryCentered hp) χ = 0 := by
  letI : NeZero (allLagModulus p 1) := by
    simpa [allLagModulus] using (inferInstance : NeZero (p^2))
  by_contra hne
  apply hχ
  apply activeLagOneChannel_primitive_and_odd hp
  rw [show centeredLagOneSpectrum p = primeCarryCentered hp by
    funext a
    exact centeredLagOneSpectrum_eq_primeCarryCentered hp hpodd a]
  exact hne

theorem collision_coefficient_primitive_parseval {p : ℕ}
    [NeZero p] [NeZero (p^2)] (hp : p.Prime) (hpodd : p ≠ 2) :
    (∑ χ : PrimitiveOddFamily p,
      ‖collisionCoefficient (primeCarryCentered hp) χ.val‖^2) =
      primeCarryEnergy hp / ((p : ℝ)*((p : ℝ)-1)) := by
  classical
  have hsum : (∑ χ : Character (p^2),
      ‖collisionCoefficient (primeCarryCentered hp) χ‖^2) =
      ∑ χ : PrimitiveOddFamily p,
        ‖collisionCoefficient (primeCarryCentered hp) χ.val‖^2 := by
    rw [← Finset.sum_subtype (p := fun χ : Character (p^2) => χ.IsPrimitive ∧ χ.Odd)
      (F := familyFintype p)
      (Finset.univ.filter (fun χ : Character (p^2) => χ.IsPrimitive ∧ χ.Odd)) (by simp)
      (fun χ : Character (p^2) => ‖collisionCoefficient (primeCarryCentered hp) χ‖^2)]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro χ _ hnot
    have hχ : ¬ (χ.IsPrimitive ∧ χ.Odd) := by simpa using hnot
    rw [collision_coefficient_inactive_zero hp hpodd χ hχ]
    norm_num
  rw [← hsum, collisionCoefficient_parseval]
  change ((p^2).totient : ℝ)⁻¹ * primeCarryEnergy hp = _
  rw [Nat.totient_prime_pow hp (by decide : 0 < 2)]
  push_cast [Nat.cast_sub hp.one_le]
  simp only [pow_one]
  ring

/-- The displayed first-moment Pearson reduction for the actual family;
both marginal second moments have been discharged. -/
theorem family_correlation_reduction {p : ℕ} [NeZero p] [NeZero (p^2)]
    (hp : p.Prime) (hpodd : p ≠ 2) :
    familyCorrelation p =
      (uniformAverage (fun χ : PrimitiveOddFamily p => shortMagnitude p χ * lMagnitude p χ) -
        uniformAverage (shortMagnitude p) * uniformAverage (lMagnitude p)) /
      Real.sqrt ((1 - uniformAverage (shortMagnitude p)^2) *
        (marginalL p - uniformAverage (lMagnitude p)^2)) := by
  letI : Nonempty (PrimitiveOddFamily p) := family_nonempty hp hpodd
  exact correlation_from_first_moments (shortMagnitude p) (lMagnitude p)
    (short_magnitude_second_moment hp hpodd) (marginalL p)
    (l_magnitude_second_moment hp hpodd)

end NField.Alignment.PrimeSquareMagnitudeFamily

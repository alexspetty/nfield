/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ConductorBoundaryLedger
import NField.Alignment.EndpointNormalization

/-! # Printed carry-boundary corollaries with their actual hypotheses -/

noncomputable section
namespace NField.Alignment.CarrySourceCorollaries
open scoped BigOperators
open CollisionCharacterStructure CarryBoundarySpectra EndpointNormalization
  ConductorBoundaryLedger PrimitiveOddBoundaryMean

/-- The centered floor table appearing in the finite-prefix reduction. -/
def centeredFloorCarry {m : ℕ} [NeZero m] (w : ZMod m → ℂ) (a : ZMod m) : ℂ :=
  naturalWeightedCarry w a.val - (a.val : ℂ) / m * naturalWeightTotal w

/-- Title: `Primitive spectral factorization of the centered floor table`. -/
theorem centered_floor_spectral_factorization {m : ℕ} [NeZero m]
    (hm : 2 ≤ m) (w : ZMod m → ℂ) {χ : Character m} (hχ : χ.IsPrimitive) :
    (∑ a : ZMod m, centeredFloorCarry w a * χ⁻¹ a) =
      -(bernoulliOne χ⁻¹ * cellBoundaryFlux w χ) := by
  have h := unit_constant_is_spectrally_invisible (carryObservable w)
    (centeredFloorCarry w) ((1 / 2 : ℂ) * (w 0 - w (m - 1 : ℕ)))
    (primitive_ne_one hm (inverse_isPrimitive hχ)) (endpoint_normalization hm w)
  rw [← h]
  exact carryBoundary_factorization hm w hχ

/-- The top-level pushdown is the original unit boundary. -/
theorem unitPushdown_self {m : ℕ} [NeZero m]
    (μ : UnitClass m → ℂ) (r : UnitClass m) :
    unitPushdown (dvd_refl m) μ r = μ r := by
  classical
  simp [unitPushdown, pushdownUnit, ZMod.unitsMap_self, Finset.sum_filter]

/-- Title: `Proper pushdown vanishing gives the top conductor moment`. -/
theorem proper_pushdowns_moment_complex {m : ℕ} [NeZero m]
    (μ : UnitClass m → ℂ)
    (hproper : ∀ d (hd : d ∣ m), d < m → ∀ r : UnitClass d, unitPushdown hd μ r = 0)
    (hodd : ∀ x : UnitClass m, μ (-x) = -μ x) :
    primitiveOddBoundaryMoment μ = (m.totient : ℂ) * ∑ x : UnitClass m, μ x * star (μ x) := by
  classical
  rw [primitiveOddBoundaryMoment_conductorLedger]
  rw [Finset.sum_eq_single m]
  · rw [Nat.div_self (NeZero.pos m)]
    simp only [ArithmeticFunction.moebius_apply_one, Int.cast_one, one_mul]
    simp only [conductorLedgerTerm, dif_pos (dvd_refl m)]
    simp_rw [unitPushdown_self, hodd, star_neg, mul_neg]
    rw [Finset.sum_neg_distrib]
    ring
  · intro d hd hdm
    have hdvd := Nat.dvd_of_mem_divisors hd
    have hlt : d < m := lt_of_le_of_ne (Nat.le_of_dvd (NeZero.pos m) hdvd) hdm
    simp [conductorLedgerTerm, hdvd, hproper d hdvd hlt]
  · intro hm
    exact (hm (Nat.mem_divisors_self m (NeZero.ne m))).elim

/-- Title: `Exact real moment under proper conductor cancellation`. -/
theorem proper_pushdowns_moment {m : ℕ} [NeZero m]
    (μ : UnitClass m → ℂ)
    (hproper : ∀ d (hd : d ∣ m), d < m → ∀ r : UnitClass d, unitPushdown hd μ r = 0)
    (hodd : ∀ x : UnitClass m, μ (-x) = -μ x) :
    primitiveOddBoundaryMomentReal μ = (m.totient : ℝ) * ∑ x : UnitClass m, ‖μ x‖ ^ 2 := by
  unfold primitiveOddBoundaryMomentReal
  simp_rw [Complex.sq_norm]
  apply Complex.ofReal_injective
  push_cast
  simp_rw [Complex.normSq_eq_conj_mul_self]
  simpa [primitiveOddBoundaryMoment, mul_comm] using
    proper_pushdowns_moment_complex μ hproper hodd

/-- Title: `The conductor bracket is the energy of the odd part`. -/
theorem conductor_bracket_odd_energy {d : ℕ} [NeZero d] (f : UnitClass d → ℂ) :
    (∑ r : UnitClass d, f r * star (f r)) -
        (∑ r : UnitClass d, f r * star (f (-r))) =
      ((1 / 2 * ∑ r : UnitClass d, ‖f r - f (-r)‖ ^ 2 : ℝ) : ℂ) := by
  have hn : (∑ r : UnitClass d, f (-r) * star (f (-r))) =
      ∑ r : UnitClass d, f r * star (f r) :=
    Equiv.sum_comp (Equiv.neg (UnitClass d)) (fun r => f r * star (f r))
  have hc : (∑ r : UnitClass d, f (-r) * star (f r)) =
      ∑ r : UnitClass d, f r * star (f (-r)) := by
    simpa using Equiv.sum_comp (Equiv.neg (UnitClass d))
      (fun r => f r * star (f (-r)))
  simp_rw [Complex.sq_norm]
  push_cast
  simp_rw [Complex.normSq_eq_conj_mul_self, starRingEnd_apply, star_sub,
    sub_mul, mul_sub]
  simp only [Finset.sum_sub_distrib]
  simp_rw [mul_comm (star _) _]
  rw [hn, hc]
  ring

end NField.Alignment.CarrySourceCorollaries

/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionVarianceEnclosure
import NField.Alignment.CollisionRamanujanCovariance

/-!
# Explicit cutoff enclosures for increment covariance

The increment is a difference of two translates of the potential. Its
squared cutoff error is therefore at most four times the squared potential
error. Cauchy-Schwarz propagates that error uniformly to every covariance.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionCovarianceEnclosure

open scoped BigOperators
open CollisionRemainderDynamics CollisionPotentialHilbert CollisionMassReadout
open CollisionPotentialConvergence CollisionPotentialCoboundary CollisionDivisibilityCovariance
open CollisionRamanujanCovariance CollisionOdometerRecurrence CollisionVarianceEnclosure
open CollisionJordanVariance CollisionRamanujan

def finiteIncrement (M : ℕ) : HaarL2 :=
  finitePotential collisionWeight M-shift (-1) (finitePotential collisionWeight M)

def finiteIncrementCovariance (M : ℕ) (h : ℤ) : ℝ :=
  inner ℝ (finiteIncrement M) (shift h (finiteIncrement M))

theorem finiteIncrement_centeredReset (M : ℕ) :
    finiteIncrement M=(2/3 : ℝ) • finiteCenteredReset M := by
  rw [finiteIncrement, finitePotential_backward_step]
  simp only [finiteCenteredReset, centeredResetVector, Finset.sum_sub_distrib, Finset.sum_smul]

theorem self_covariance_even (v : HaarL2) (h : ℤ) :
    inner ℝ v (shift h v)=inner ℝ v (shift (-h) v) := by
  have he := (shift h).inner_map_map v (shift (-h) v)
  rw [← shift_add, add_neg_cancel, shift_zero] at he
  rw [← he, real_inner_comm]

theorem finiteIncrementCovariance_even (M : ℕ) (h : ℤ) :
    finiteIncrementCovariance M h=finiteIncrementCovariance M (-h) :=
  self_covariance_even _ _

theorem finiteIncrementCovariance_ramanujan_nat (M h : ℕ) :
    finiteIncrementCovariance M (h : ℤ)=(4/9 : ℝ)*
      ∑ q ∈ Finset.Icc 2 M, (finiteAmplitude collisionWeight q M)^2*ramanujan q h := by
  rw [finiteIncrementCovariance_even, finiteIncrementCovariance, finiteIncrement_centeredReset,
    map_smul, inner_smul_left, inner_smul_right, conj_trivial,
    finiteCenteredReset_covariance, finiteCovarianceCoefficient_tsum]
  ring

theorem finiteIncrementCovariance_ramanujan (M : ℕ) (h : ℤ) :
    finiteIncrementCovariance M h=(4/9 : ℝ)*
      ∑ q ∈ Finset.Icc 2 M, (finiteAmplitude collisionWeight q M)^2*ramanujan q h := by
  by_cases hh : 0 ≤ h
  · simpa only [Int.toNat_of_nonneg hh] using finiteIncrementCovariance_ramanujan_nat M h.toNat
  · have he : h=-(((-h).toNat : ℕ) : ℤ) := by omega
    rw [he, finiteIncrementCovariance_even, neg_neg, finiteIncrementCovariance_ramanujan_nat]
    simp only [ramanujan, dvd_neg]

theorem finiteIncrementCovariance_arithmetic (M : ℕ) (h : ℤ) :
    finiteIncrementCovariance M h=(4/9 : ℝ)*
      ∑ k ∈ Finset.Icc 2 M, ∑ l ∈ Finset.Icc 2 M, arithmeticCovarianceTerm h (k,l) := by
  rw [finiteIncrementCovariance_ramanujan, finite_arithmetic_regrouping]

theorem finiteIncrementCovariance_zero (M : ℕ) :
    finiteIncrementCovariance M 0=‖finiteIncrement M‖^2 := by
  rw [finiteIncrementCovariance, shift_zero, real_inner_self_eq_norm_sq]

theorem finiteIncrement_periodic (M : ℕ) :
    shift (cutoffPeriod M : ℤ) (finiteIncrement M)=finiteIncrement M := by
  have hc : shift (cutoffPeriod M : ℤ) (shift (-1) (finitePotential collisionWeight M))=
      shift (-1) (shift (cutoffPeriod M : ℤ) (finitePotential collisionWeight M)) := by
    rw [← shift_add, add_comm (cutoffPeriod M : ℤ) (-1), shift_add]
  simp only [finiteIncrement, map_sub, hc, finitePotential_periodic]

theorem finiteIncrementCovariance_recurrence (M : ℕ) :
    finiteIncrementCovariance M (cutoffPeriod M : ℤ)=finiteIncrementCovariance M 0 := by
  simp only [finiteIncrementCovariance, finiteIncrement_periodic, shift_zero]

theorem increment_cutoff_norm (M : ℕ) :
    ‖incrementVector-finiteIncrement M‖ ≤
      2*‖collisionPotential-finitePotential collisionWeight M‖ := by
  have he : incrementVector-finiteIncrement M =
      (collisionPotential-finitePotential collisionWeight M)-
        shift (-1) (collisionPotential-finitePotential collisionWeight M) := by
    simp only [incrementVector, finiteIncrement, map_sub]
    abel
  rw [he]
  have h := norm_sub_le (collisionPotential-finitePotential collisionWeight M)
    (shift (-1) (collisionPotential-finitePotential collisionWeight M))
  simpa only [(shift (-1)).norm_map, two_mul] using h

theorem increment_cutoff_sq_rational {M b : ℕ} (hM : 1 ≤ M) (hb : 2*M ≤ 2^b) :
    ‖incrementVector-finiteIncrement M‖^2 ≤ 4*rationalSquaredError M b := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (increment_cutoff_norm M) 2
  have he := collisionPotential_cutoff_sq_rational hM hb
  nlinarith

theorem self_covariance_difference_bound (x y : HaarL2) (h : ℤ) :
    |inner ℝ x (shift h x)-inner ℝ y (shift h y)| ≤
      2*‖y‖*‖x-y‖+‖x-y‖^2 := by
  have he : inner ℝ x (shift h x)-inner ℝ y (shift h y) =
      inner ℝ y (shift h (x-y))+inner ℝ (x-y) (shift h y)+
        inner ℝ (x-y) (shift h (x-y)) := by
    simp only [map_sub, inner_sub_left, inner_sub_right]
    ring
  rw [he]
  have ha := norm_inner_le_norm (𝕜 := ℝ) y (shift h (x-y))
  have hb := norm_inner_le_norm (𝕜 := ℝ) (x-y) (shift h y)
  have hc := norm_inner_le_norm (𝕜 := ℝ) (x-y) (shift h (x-y))
  simp only [Real.norm_eq_abs, (shift h).norm_map] at ha hb hc
  have h1 := abs_add_le (inner ℝ y (shift h (x-y))) (inner ℝ (x-y) (shift h y))
  have h2 := abs_add_le (inner ℝ y (shift h (x-y))+inner ℝ (x-y) (shift h y))
    (inner ℝ (x-y) (shift h (x-y)))
  nlinarith

theorem increment_covariance_rational_error {M b : ℕ} {u : ℝ} (h : ℤ)
    (hM : 1 ≤ M) (hb : 2*M ≤ 2^b) (hu : 0 ≤ u)
    (hcross : finiteIncrementCovariance M 0*(4*rationalSquaredError M b) ≤ u^2) :
    |incrementCovariance h-finiteIncrementCovariance M h| ≤
      2*u+4*rationalSquaredError M b := by
  have he := increment_cutoff_sq_rational hM hb
  rw [finiteIncrementCovariance_zero] at hcross
  have hp := mul_le_mul_of_nonneg_left he (sq_nonneg ‖finiteIncrement M‖)
  have hprod : ‖finiteIncrement M‖*‖incrementVector-finiteIncrement M‖ ≤ u := by
    nlinarith [mul_nonneg (norm_nonneg (finiteIncrement M))
      (norm_nonneg (incrementVector-finiteIncrement M))]
  have hc := self_covariance_difference_bound incrementVector (finiteIncrement M) h
  change |incrementCovariance h-finiteIncrementCovariance M h| ≤ _ at hc
  nlinarith

theorem increment_covariance_rational_enclosure {M b : ℕ} {u : ℝ} (h : ℤ)
    (hM : 1 ≤ M) (hb : 2*M ≤ 2^b) (hu : 0 ≤ u)
    (hcross : finiteIncrementCovariance M 0*(4*rationalSquaredError M b) ≤ u^2) :
    incrementCovariance h ∈ Set.Icc
      (finiteIncrementCovariance M h-(2*u+4*rationalSquaredError M b))
      (finiteIncrementCovariance M h+(2*u+4*rationalSquaredError M b)) := by
  have he := abs_le.mp (increment_covariance_rational_error h hM hb hu hcross)
  constructor <;> linarith

theorem potential_recurrence_sq_rational {M b : ℕ} (hM : 1 ≤ M) (hb : 2*M ≤ 2^b) :
    ‖shift (cutoffPeriod M : ℤ) collisionPotential-collisionPotential‖^2 ≤
      4*rationalSquaredError M b := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (potential_recurrence_norm M) 2
  have he := collisionPotential_cutoff_sq_rational hM hb
  nlinarith

theorem increment_covariance_recurrence_rational {M b : ℕ}
    (hM : 1 ≤ M) (hb : 2*M ≤ 2^b) :
    incrementCovariance 0-incrementCovariance (cutoffPeriod M : ℤ) ∈
      Set.Icc 0 (8*rationalSquaredError M b) := by
  have hn := pow_le_pow_left₀ (norm_nonneg _) (increment_recurrence_norm M) 2
  have he := potential_recurrence_sq_rational hM hb
  have hi : ‖shift (cutoffPeriod M : ℤ) incrementVector-incrementVector‖^2 =
      2*(incrementCovariance 0-incrementCovariance (cutoffPeriod M : ℤ)) := by
    rw [norm_sub_sq_real, (shift (cutoffPeriod M : ℤ)).norm_map]
    simp only [incrementCovariance, shift_zero, real_inner_self_eq_norm_sq]
    rw [real_inner_comm]
    ring
  constructor <;> nlinarith [sq_nonneg ‖shift (cutoffPeriod M : ℤ) incrementVector-incrementVector‖]

end NField.Alignment.CollisionCovarianceEnclosure

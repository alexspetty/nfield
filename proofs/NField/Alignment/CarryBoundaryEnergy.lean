/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CarryQuadraticLayer

/-! # The literal quadratic carry energy in boundary coordinates -/

noncomputable section
namespace NField.Alignment.CarryBoundaryEnergy
open scoped BigOperators
open CollisionCharacterStructure CarryBoundarySpectra

/-- Discrete summation by parts for any complex test function. -/
theorem cellDifference_boundary_pairing {m : ℕ} [NeZero m]
    (w f : ZMod m → ℂ) :
    (∑ n : ZMod m, w n * (f (n + 1) - f n)) =
      ∑ x : ZMod m, signedBoundary w x * f x := by
  have hshift : (∑ n : ZMod m, w n * f (n + 1)) =
      ∑ x : ZMod m, w (x - 1) * f x := by
    simpa using Equiv.sum_comp (Equiv.addRight (1 : ZMod m))
      (fun x : ZMod m => w (x - 1) * f x)
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, hshift, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  dsimp [signedBoundary]
  ring

/-- Title: `The carry observable is the signed boundary potential`. -/
theorem actual_carry_boundary_potential {m : ℕ} [NeZero m]
    (w : ZMod m → ℂ) (a : ZMod m) :
    carryObservable w a = -∑ x : ZMod m, signedBoundary w x * centeredSawtooth (x * a) := by
  unfold carryObservable
  rw [cellDifference_boundary_pairing w (fun x => centeredSawtooth (x * a))]

theorem centeredSawtooth_star {m : ℕ} [NeZero m] (x : ZMod m) :
    star (centeredSawtooth x) = centeredSawtooth x := by
  classical
  unfold centeredSawtooth
  split_ifs <;> simp only [star_zero, star_sub, star_div₀, star_natCast, star_one,
    star_ofNat]

/-- Title: `Exact quadratic carry energy from the signed boundary`. -/
theorem actual_quadratic_boundary_energy {m : ℕ} [NeZero m] (w : ZMod m → ℂ) :
    ((∑ a : UnitClass m, ‖carryObservable w a.val‖ ^ 2 : ℝ) : ℂ) =
      ∑ x : ZMod m, ∑ y : ZMod m,
        signedBoundary w x * star (signedBoundary w y) *
          ∑ a : UnitClass m, centeredSawtooth (x * a.val) * centeredSawtooth (y * a.val) := by
  classical
  have hpoint (a : UnitClass m) :
      ((‖carryObservable w a.val‖ ^ 2 : ℝ) : ℂ) =
        ∑ x : ZMod m, ∑ y : ZMod m,
          signedBoundary w x * star (signedBoundary w y) *
            (centeredSawtooth (x * a.val) * centeredSawtooth (y * a.val)) := by
    rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self, actual_carry_boundary_potential]
    simp only [starRingEnd_apply, star_neg, neg_mul_neg, star_sum, star_mul,
      centeredSawtooth_star]
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [Complex.ofReal_sum]
  simp_rw [hpoint]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.mul_sum]

end NField.Alignment.CarryBoundaryEnergy

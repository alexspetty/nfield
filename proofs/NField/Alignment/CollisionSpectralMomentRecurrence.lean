/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionRamanujanCovariance

/-!
# Recovering potential spectral moments from the coboundary

Translation is an isometry on the actual Haar space. Its covariance
satisfies the second-difference identity for a coboundary. An even moment
sequence is uniquely determined by that identity and its zeroth moment.
This provides a route from the proved increment spectrum to the potential
spectrum once the proposed atomic measure's moments have been computed.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionSpectralMomentRecurrence

open scoped BigOperators
open CollisionPotentialHilbert CollisionPotentialConvergence CollisionPotentialCoboundary
open CollisionOdometerRecurrence CollisionDivisibilityCovariance

def haarCovariance (V : HaarL2) (h : ℤ) : ℝ := inner ℝ V (shift h V)

theorem inner_shift_shift (V W : HaarL2) (a b : ℤ) :
    inner ℝ (shift a V) (shift b W) = inner ℝ V (shift (b-a) W) := by
  have hi := (shift a).inner_map_map V (shift (b-a) W)
  rw [← shift_add, show a+(b-a)=b by omega] at hi
  exact hi

theorem haarCovariance_even (V : HaarL2) (h : ℤ) :
    haarCovariance V (-h) = haarCovariance V h := by
  have hi := (shift h).inner_map_map V (shift (-h) V)
  rw [← shift_add, add_neg_cancel, shift_zero] at hi
  change inner ℝ V (shift (-h) V) = inner ℝ V (shift h V)
  rw [← hi, real_inner_comm]

theorem haarCovariance_zero (V : HaarL2) : haarCovariance V 0 = ‖V‖^2 := by
  rw [haarCovariance, shift_zero, real_inner_self_eq_norm_sq]

theorem haarCovariance_coboundary (V : HaarL2) (h : ℤ) :
    haarCovariance (V-shift (-1) V) h =
      2*haarCovariance V h-haarCovariance V (h-1)-haarCovariance V (h+1) := by
  simp only [haarCovariance, map_sub, inner_sub_left, inner_sub_right, ← shift_add]
  rw [inner_shift_shift, inner_shift_shift]
  rw [show h + -1 = h-1 by omega, show h - -1 = h+1 by omega,
    show (h-1) - -1 = h by omega]
  ring

theorem even_second_difference_unique (R S : ℤ → ℂ)
    (hR : ∀ h, R (-h)=R h) (hS : ∀ h, S (-h)=S h)
    (hzero : R 0=S 0)
    (hrec : ∀ h, 2*R h-R (h-1)-R (h+1)=2*S h-S (h-1)-S (h+1)) : R=S := by
  have hone : R 1=S 1 := by
    have h := hrec 0
    norm_num only at h
    rw [hR 1, hS 1, hzero] at h
    linear_combination -(1/2 : ℂ) * h
  have hnat (n : ℕ) : R (n : ℤ)=S (n : ℤ) ∧ R ((n : ℤ)+1)=S ((n : ℤ)+1) := by
    induction n with
    | zero => simpa using And.intro hzero hone
    | succ n ih =>
      constructor
      · simpa only [Nat.cast_add, Nat.cast_one] using ih.2
      · have h := hrec ((n : ℤ)+1)
        rw [show (n : ℤ)+1-1=n by omega, ih.1, ih.2] at h
        have he : R (((n : ℤ)+1)+1)=S (((n : ℤ)+1)+1) := by
          linear_combination -h
        simpa only [Nat.cast_add, Nat.cast_one] using he
  funext h
  by_cases hh : 0 ≤ h
  · simpa only [Int.toNat_of_nonneg hh] using (hnat h.toNat).1
  · have hn : 0 ≤ -h := by omega
    rw [← hR h, ← hS h]
    simpa only [Int.toNat_of_nonneg hn] using (hnat (-h).toNat).1

theorem potential_covariance_second_difference (h : ℤ) :
    2*haarCovariance collisionPotential h-haarCovariance collisionPotential (h-1)-
      haarCovariance collisionPotential (h+1) = incrementCovariance h := by
  rw [← haarCovariance_coboundary]
  rfl

theorem potential_spectral_moments_unique (m : ℤ → ℂ)
    (heven : ∀ h, m (-h)=m h)
    (hzero : m 0=(‖collisionPotential‖^2 : ℝ))
    (hrec : ∀ h, 2*m h-m (h-1)-m (h+1)=(incrementCovariance h : ℂ)) :
    m=fun h => (haarCovariance collisionPotential h : ℂ) := by
  apply even_second_difference_unique m _ heven
  · intro h
    rw [haarCovariance_even]
  · rw [hzero, haarCovariance_zero]
  · intro h
    rw [hrec]
    have h := congrArg Complex.ofReal (potential_covariance_second_difference h)
    push_cast at h
    exact h.symm

end NField.Alignment.CollisionSpectralMomentRecurrence

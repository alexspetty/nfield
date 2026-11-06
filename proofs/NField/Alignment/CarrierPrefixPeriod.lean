/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.CarrierStateSwitching
import NField.Alignment.CarrierJumpData

/-! # Removing complete zero-mean periods from an actual carrier prefix -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.CarrierPrefixPeriod
open scoped BigOperators
open CarrierStateSwitching RademacherThreeTerm DedekindReciprocity

theorem coefficient_period (x y k : ℕ) :
    arithmeticCoefficientDedekindTerm x (y+k) k = arithmeticCoefficientDedekindTerm x y k := by
  unfold arithmeticCoefficientDedekindTerm
  apply Finset.sum_congr rfl
  intro t ht
  simp [rationalSawtooth, Nat.add_mul, Nat.add_mod]

theorem carrierPrefix_range (p k X : ℕ) :
    carrierPrefix p k X = ∑ a ∈ Finset.range X,
      if (a+1).Coprime k then arithmeticCoefficientDedekindTerm (p^2) (a+1) k else 0 := by
  induction X with
  | zero => simp [carrierPrefix]
  | succ X ih => rw [carrierPrefix_succ, Finset.sum_range_succ, ih]

theorem carrierPrefix_eq_mod {p k : ℕ} (hk : 2 ≤ k) (hpk : (p^2).Coprime k) (X : ℕ) :
    carrierPrefix p k X = carrierPrefix p k (X%k) := by
  let f := fun a => if (a+1).Coprime k then arithmeticCoefficientDedekindTerm (p^2) (a+1) k else 0
  have hperiod : ∀ a, f (a+k)=f a := by
    intro a
    dsimp only [f]
    rw [show a+k+1=(a+1)+k by omega, coefficient_period]
    simp
  have hzero : (∑ a ∈ Finset.range k, f a)=0 := by
    rw [← carrierPrefix_range]
    exact carrierPrefix_self_eq_zero hk hpk
  have h := CarrierJumpData.sum_periodic_blocks f hperiod (X/k) (X%k)
  rw [show X/k*k+X%k=X by rw [Nat.mul_comm]; exact Nat.div_add_mod X k,
    hzero, mul_zero, zero_add] at h
  simpa only [carrierPrefix_range] using h

end NField.Alignment.CarrierPrefixPeriod

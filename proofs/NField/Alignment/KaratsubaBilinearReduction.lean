/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KaratsubaPhaseAlignment

/-! # The two finite Holder steps for the actual prime bilinear sum -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KaratsubaBilinearReduction
open scoped BigOperators
open KaratsubaPrimeMoment KaratsubaWeightedMoment KaratsubaFourierMoment KaratsubaPhaseAlignment

def ordinarySum {Q : Finset ℕ} {s : ℕ} (u : PrimeTuple Q s) : ℕ := ∑ i, (u i).val

def primeRow (Q : Finset ℕ) {m : ℕ} [NeZero m] (a b : ZMod m) (p : ℕ) : ℂ :=
  mixedPrimeSum Q (a * (p : ZMod m)⁻¹) (b * (p : ZMod m))

def bilinearPrimeSum (P Q : Finset ℕ) {m : ℕ} [NeZero m] (a b : ZMod m) : ℂ :=
  ∑ p : {p // p ∈ P}, primeRow Q a b p.val

theorem primeRow_power (Q : Finset ℕ) {m : ℕ} [NeZero m]
    (a b : ZMod m) (p s : ℕ) :
    primeRow Q a b p ^ s = ∑ u : PrimeTuple Q s,
      ZMod.stdAddChar ((a * (p : ZMod m)⁻¹) * reciprocalSum m (fun i => (u i).val) +
        (b * (p : ZMod m)) * (ordinarySum u : ZMod m)) := by
  rw [primeRow, mixedPrimeSum, Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro u _
  rw [← character_sum]
  congr 1
  simp only [reciprocalSum, ordinarySum, Nat.cast_sum, Finset.sum_add_distrib, Finset.mul_sum]

def tupleResponse (P Q : Finset ℕ) {m s : ℕ} [NeZero m]
    (a b : ZMod m) (u : PrimeTuple Q s) : ℂ :=
  ∑ p : {p // p ∈ P}, phaseAlign (primeRow Q a b p.val) ^ s *
    ZMod.stdAddChar ((a * reciprocalSum m (fun i => (u i).val)) * (p.val : ZMod m)⁻¹ +
      (b * (ordinarySum u : ZMod m)) * (p.val : ZMod m))

theorem aligned_rows_eq_tuple_sum (P Q : Finset ℕ) {m s : ℕ} [NeZero m] (a b : ZMod m) :
    (∑ p : {p // p ∈ P}, phaseAlign (primeRow Q a b p.val) ^ s * primeRow Q a b p.val ^ s) =
      ∑ u : PrimeTuple Q s, tupleResponse P Q a b u := by
  simp_rw [primeRow_power, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro p _
  congr 2
  ring

theorem first_holder_step (P Q : Finset ℕ) {m s : ℕ} [NeZero m]
    (a b : ZMod m) (hs : 1 ≤ s) :
    ‖bilinearPrimeSum P Q a b‖ ^ s ≤ (P.card : ℝ) ^ (s-1) *
      ‖∑ u : PrimeTuple Q s, tupleResponse P Q a b u‖ := by
  have h := linearized_holder Finset.univ (fun p : {p // p ∈ P} => primeRow Q a b p.val) hs
  rw [aligned_rows_eq_tuple_sum] at h
  simpa only [bilinearPrimeSum, Finset.card_univ, Fintype.card_coe] using h

theorem two_holder_steps (P Q : Finset ℕ) {m s k : ℕ} [NeZero m]
    (a b : ZMod m) (hs : 1 ≤ s) (hk : 1 ≤ k) :
    ‖bilinearPrimeSum P Q a b‖ ^ (s*k) ≤
      ((P.card : ℝ) ^ (s-1)) ^ k * ((Q.card : ℝ) ^ s) ^ (k-1) *
        ∑ u : PrimeTuple Q s, ‖tupleResponse P Q a b u‖ ^ k := by
  have h := pow_le_pow_left₀ (by positivity) (first_holder_step P Q a b hs) k
  rw [← pow_mul, mul_pow] at h
  have hh := KaratsubaHolder.norm_sum_pow_le Finset.univ (tupleResponse P Q (s := s) a b) hk
  have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ ((P.card : ℝ) ^ (s-1)) ^ k by positivity)
  apply h.trans
  simpa only [PrimeTuple, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_coe, Nat.cast_pow, mul_assoc] using hm

end NField.Alignment.KaratsubaBilinearReduction

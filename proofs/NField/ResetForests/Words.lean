/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetSampling
import Mathlib
/-! # Reflected source words, including nonunit addresses -/

noncomputable section

namespace NField.ResetForests.Core

open scoped BigOperators
open NField.Alignment
open CarrierJumpData DedekindReciprocity CommonResetSampling CollisionRampEnergy

theorem rational_saw_complex {k : ℕ} (hk : 0 < k) (b : ℕ) :
    (rationalSawtooth b k : ℂ) = CarryBoundarySpectra.centeredSawtooth (b : ZMod k) := by
  letI : NeZero k := ⟨hk.ne'⟩
  have h := rationalSawtooth_val_eq_centeredSawtooth (b : ZMod k)
  simpa only [ZMod.val_natCast, rationalSawtooth, Nat.mod_mod] using h

theorem rational_word_reflection {k r : ℕ} (hk : 2 ≤ k) (hr : r ≤ k) (a : ℕ) :
    rationalSawtooth ((k-r)*a) k = -rationalSawtooth (r*a) k := by
  letI : NeZero k := ⟨by omega⟩
  apply Rat.cast_injective (α := ℂ)
  push_cast
  rw [rational_saw_complex (by omega : 0 < k), rational_saw_complex (by omega : 0 < k)]
  have he : (((k-r)*a : ℕ) : ZMod k) = -((r*a : ℕ) : ZMod k) := by
    push_cast [Nat.cast_sub hr]
    simp
  rw [he, CarryBoundarySpectra.centeredSawtooth_neg hk]

/-- A complete harmonic period cancels even at nonunit addresses. -/
theorem full_word_period_zero {k : ℕ} (hk : 2 ≤ k) (a : ℕ) :
    (∑ r ∈ Finset.range k, rationalSawtooth ((r+1)*a) k) = 0 := by
  have href := Finset.sum_range_reflect (fun r => rationalSawtooth (r*a) k) (k+1)
  have hterms :
      (∑ r ∈ Finset.range (k+1), rationalSawtooth ((k+1-1-r)*a) k) =
        -(∑ r ∈ Finset.range (k+1), rationalSawtooth (r*a) k) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    simpa using rational_word_reflection hk (by
      have := Finset.mem_range.mp hr
      omega : r ≤ k) a
  rw [hterms] at href
  have hzero : (∑ r ∈ Finset.range (k+1), rationalSawtooth (r*a) k) = 0 := by
    linarith
  have hshift := sum_range_shift_one (fun r => rationalSawtooth (r*a) k) k
  rw [hzero] at hshift
  simpa only [Nat.zero_mul, rationalSawtooth_zero, add_zero] using hshift

theorem cutoff_word_remainder {k : ℕ} (hk : 2 ≤ k) (N a : ℕ) :
    boundaryMidpoint N a k = boundaryMidpoint (N%k) a k := by
  let f := fun r : ℕ => rationalSawtooth ((r+1)*a) k
  have hperiod : ∀ r, f (r+k) = f r := by
    intro r
    unfold f
    rw [show r+k+1 = (r+1)+k by omega]
    exact rationalSawtooth_add_period a k (r+1)
  have hblock : (∑ r ∈ Finset.range k, f r) = 0 := full_word_period_zero hk a
  have hdecomp : N/k*k+N%k = N := by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod N k
  unfold boundaryMidpoint
  change 2*(∑ r ∈ Finset.range N, f r) = 2*∑ r ∈ Finset.range (N%k), f r
  have hsum := sum_periodic_blocks f hperiod (N/k) (N%k)
  rw [hdecomp, hblock] at hsum
  rw [hsum]
  ring

theorem prefix_word_reflection {k r : ℕ} (hk : 2 ≤ k) (hr : r < k) (a : ℕ) :
    boundaryMidpoint r a k = boundaryMidpoint (k-1-r) a k := by
  let f := fun i : ℕ => rationalSawtooth ((i+1)*a) k
  let s := k-1-r
  have hlen : r+s = k-1 := by dsimp [s]; omega
  have hlast : f (k-1) = 0 := by
    dsimp [f]
    rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]
    simp [rationalSawtooth]
  have hfull : (∑ i ∈ Finset.range (k-1), f i) = 0 := by
    have h := full_word_period_zero hk a
    change (∑ i ∈ Finset.range k, f i) = 0 at h
    rw [← Nat.sub_add_cancel (by omega : 1 ≤ k), Finset.sum_range_succ,
      hlast, add_zero] at h
    exact h
  have htail : (∑ i ∈ Finset.range s, f (r+i)) = -(∑ i ∈ Finset.range s, f i) := by
    have hterm (i : ℕ) (hi : i ∈ Finset.range s) : f (r+i) = -f (s-1-i) := by
      have hi' := Finset.mem_range.mp hi
      have hri : r+i+1 ≤ k := by dsimp [s] at hi'; omega
      have he : k-(r+i+1) = s-1-i+1 := by dsimp [s] at *; omega
      have hf := rational_word_reflection hk hri a
      rw [he] at hf
      dsimp [f]
      linarith
    rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib, Finset.sum_range_reflect]
  have hsplit := Finset.sum_range_add f r s
  rw [hlen, hfull, htail] at hsplit
  unfold boundaryMidpoint
  change 2*(∑ i ∈ Finset.range r, f i) = 2*∑ i ∈ Finset.range s, f i
  linarith

def foldedWord (N k : ℕ) : ℕ := min (N%k) (k-1-N%k)

/-- The actual cutoff word equals its reflected short word at every address. -/
theorem reflected_source_word {k : ℕ} (hk : 2 ≤ k) (N a : ℕ) :
    boundaryResponse N ((a : ℝ)/(k : ℝ)) =
      boundaryResponse (foldedWord N k) ((a : ℝ)/(k : ℝ)) := by
  rw [boundaryResponse_rational (by omega : 0 < k),
    boundaryResponse_rational (by omega : 0 < k)]
  congr 1
  rw [cutoff_word_remainder hk]
  unfold foldedWord
  by_cases h : N%k ≤ k-1-N%k
  · rw [min_eq_left h]
  · rw [min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge h))]
    exact prefix_word_reflection hk (Nat.mod_lt N (by omega)) a

/-- The short word is bounded uniformly over all clocks in the cutoff. -/
theorem folded_word_third {N k : ℕ} (hk : 2 ≤ k) (hkN : k ≤ N) :
    foldedWord N k ≤ (N-1)/3 := by
  have hr : N%k < k := Nat.mod_lt N (by omega)
  have hfirst : foldedWord N k ≤ N%k := min_le_left _ _
  have hsecond : foldedWord N k ≤ k-1-N%k := min_le_right _ _
  have hload : 1 ≤ N/k := (Nat.le_div_iff_mul_le (by omega : 0 < k)).mpr (by simpa)
  have hprod : k ≤ N/k*k := by nlinarith
  have hdecomp : N/k*k+N%k = N := by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod N k
  omega

theorem common_word_phase (N s : ℕ) (hs : s ≤ N) :
    N+1+s*(s+1) = (N-s)+(s+1)^2 ∧
      N+1+s*(s+1) = (N+1+s)+s^2 := by
  constructor
  · have h := Nat.sub_add_cancel hs
    nlinarith
  · ring

/-- The lower branch includes the tie and keeps the actual quotient load. -/
theorem lower_word_branch {N k : ℕ} (hk : 2 ≤ k)
    (hbranch : N%k ≤ k-1-N%k) :
    N-foldedWord N k = (N/k)*k ∧
      2*foldedWord N k+1 ≤ k ∧
      (N+1)^2%k = (foldedWord N k+1)^2%k := by
  have hword : foldedWord N k = N%k := min_eq_left hbranch
  have hr : N%k < k := Nat.mod_lt N (by omega)
  have hdecomp : N/k*k+N%k = N := by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod N k
  rw [hword]
  refine ⟨by omega, by omega, ?_⟩
  simp [Nat.pow_mod, Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < k)]

/-- The upper branch has its own carrier but the same centered phase. -/
theorem upper_word_branch {N k : ℕ} (hk : 2 ≤ k)
    (hbranch : k-1-N%k < N%k) :
    N+1+foldedWord N k = (N/k+1)*k ∧
      2*foldedWord N k+2 ≤ k ∧
      (N+1)^2%k = (foldedWord N k)^2%k := by
  letI : NeZero k := ⟨by omega⟩
  have hword : foldedWord N k = k-1-N%k := min_eq_right hbranch.le
  have hr : N%k < k := Nat.mod_lt N (by omega)
  have hdecomp : N/k*k+N%k = N := by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod N k
  have hcarrier : N+1+foldedWord N k = (N/k+1)*k := by
    rw [hword]
    have hs : (k-1-N%k)+N%k = k-1 := Nat.sub_add_cancel (by omega)
    rw [Nat.add_mul, one_mul]
    omega
  refine ⟨hcarrier, by omega, ?_⟩
  have hz : ((N+1 : ℕ) : ZMod k)+(foldedWord N k : ZMod k) = 0 := by
    have h := congrArg (fun n : ℕ => (n : ZMod k)) hcarrier
    simpa only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero] using h
  have hp : ((N+1 : ℕ) : ZMod k) = -(foldedWord N k : ZMod k) :=
    eq_neg_iff_add_eq_zero.mpr hz
  have hsq : (((N+1)^2 : ℕ) : ZMod k) = (((foldedWord N k)^2 : ℕ) : ZMod k) := by
    push_cast
    push_cast at hp
    rw [hp, neg_sq]
  have hv := congrArg ZMod.val hsq
  simpa only [ZMod.val_natCast] using hv

theorem integer_address_reduction {k : ℕ} (hk : 0 < k) (N : ℕ) (a : ℤ) :
    boundaryResponse N ((a : ℝ)/(k : ℝ)) =
      boundaryResponse N ((((a%(k : ℤ)).toNat : ℕ) : ℝ)/(k : ℝ)) := by
  have hrem : 0 ≤ a%(k : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hk.ne')
  have hcast : (((a%(k : ℤ)).toNat : ℕ) : ℝ) = ((a%(k : ℤ) : ℤ) : ℝ) := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) (Int.toNat_of_nonneg hrem)
    simpa only [Int.cast_natCast] using h
  have haddr : (a : ℝ)/(k : ℝ)-((a/(k : ℤ) : ℤ) : ℝ) =
      (((a%(k : ℤ)).toNat : ℕ) : ℝ)/(k : ℝ) := by
    rw [hcast]
    have h := congrArg (fun z : ℤ => (z : ℝ)) (Int.emod_add_mul_ediv a (k : ℤ))
    push_cast at h
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    field_simp
    nlinarith
  have hp := (boundaryResponse_periodic N).sub_int_mul_eq
    (x := (a : ℝ)/(k : ℝ)) (a/(k : ℤ))
  simp only [mul_one] at hp
  rw [haddr] at hp
  exact hp.symm

/-- The reflected source-word identity for the manuscript's integer addresses. -/
theorem reflected_source_word_integer {k : ℕ} (hk : 2 ≤ k) (N : ℕ) (a : ℤ) :
    boundaryResponse N ((a : ℝ)/(k : ℝ)) =
      boundaryResponse (foldedWord N k) ((a : ℝ)/(k : ℝ)) := by
  rw [integer_address_reduction (by omega : 0 < k) N a,
    integer_address_reduction (by omega : 0 < k) (foldedWord N k) a]
  exact reflected_source_word hk N _

theorem tied_word_branch {N k : ℕ} (hk : 2 ≤ k)
    (htie : k = 2*foldedWord N k+1) :
    (N+1+foldedWord N k)/k-1 = (N-foldedWord N k)/k ∧
      (foldedWord N k+1)^2%k = (foldedWord N k)^2%k := by
  let s := foldedWord N k
  have hsN : s ≤ N := (min_le_left _ _).trans (Nat.mod_le _ _)
  have hcarrier : N+1+s = (N-s)+k := by
    have h := Nat.sub_add_cancel hsN
    change k = 2*s+1 at htie
    omega
  constructor
  · change (N+1+s)/k-1 = (N-s)/k
    rw [hcarrier, Nat.add_div_right _ (by omega : 0 < k)]
    simp
  · letI : NeZero k := ⟨by omega⟩
    have hz : (2 : ZMod k)*(s : ZMod k)+1 = 0 := by
      have h := congrArg (fun n : ℕ => (n : ZMod k)) htie
      push_cast at h
      simpa only [ZMod.natCast_self] using h.symm
    have hsq : (((s+1)^2 : ℕ) : ZMod k) = ((s^2 : ℕ) : ZMod k) := by
      push_cast
      calc
        ((s : ZMod k)+1)^2 = (s : ZMod k)^2+(2*(s : ZMod k)+1) := by ring
        _ = _ := by rw [hz, add_zero]
    have hv := congrArg ZMod.val hsq
    simpa only [ZMod.val_natCast] using hv

/-- The single common-phase polynomial represents the actual square sampler. -/
theorem common_sampling_phase {N k : ℕ} (hk : 2 ≤ k) :
    (N+1+foldedWord N k*(foldedWord N k+1))%k = (N+1)^2%k := by
  letI : NeZero k := ⟨by omega⟩
  let s := foldedWord N k
  have hsq : (((N+1+s*(s+1) : ℕ)) : ZMod k) = (((N+1)^2 : ℕ) : ZMod k) := by
    by_cases hbranch : N%k ≤ k-1-N%k
    · have hcarrier := (lower_word_branch hk hbranch).1
      have hsN : s ≤ N := (min_le_left _ _).trans (Nat.mod_le _ _)
      have heq : N = (N/k)*k+s := by dsimp [s]; omega
      have hn : (N : ZMod k) = (s : ZMod k) := by
        nth_rw 1 [heq]
        push_cast
        simp
      push_cast
      rw [hn]
      ring
    · have hcarrier := (upper_word_branch hk (Nat.lt_of_not_ge hbranch)).1
      have hz : ((N+1 : ℕ) : ZMod k)+(s : ZMod k) = 0 := by
        have h := congrArg (fun n : ℕ => (n : ZMod k)) hcarrier
        simpa only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero] using h
      have hp : ((N+1 : ℕ) : ZMod k) = -(s : ZMod k) := eq_neg_iff_add_eq_zero.mpr hz
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one] at hp ⊢
      rw [hp]
      ring
  have hv := congrArg ZMod.val hsq
  simpa only [ZMod.val_natCast] using hv

end NField.ResetForests.Core

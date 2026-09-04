/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CosetAlignment
import NField.Alignment.MultiplicativeRemainderOrbits

/-!
# Synchronized denominator clocks and multiplicative cosets

This module identifies the literal common-depth, numerator-by-numerator match
count with the orbit-bin sum attached to the selected multiplicative coset.
It is the bridge between long division and the finite coset formula.
-/

namespace NField.Alignment

open scoped BigOperators
open NField.CollisionDefinition

/-- The two standard finite sets of nonzero residue representatives agree. -/
theorem positiveResidues_eq_nonzeroResidues {p : ℕ} (hp : 0 < p) :
    ThreeTier.positiveResidues p = nonzeroResidues p := by
  ext r
  simp only [ThreeTier.positiveResidues, nonzeroResidues, Finset.mem_Icc,
    Finset.mem_erase, Finset.mem_range]
  omega

/-- Multiplication by a unit modulo `p` is a permutation of `Fin p`. -/
theorem transportedRemainder_fin_bijective {p a : ℕ} (hp : 0 < p)
    (hcop : Nat.Coprime p a) :
    Function.Bijective (fun r : Fin p =>
      (⟨transportedRemainder p a r, transportedRemainder_lt_of_pos p a r hp⟩ : Fin p)) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, rfl⟩
  intro x y hxy
  apply Fin.ext
  have hmod : a * x.val ≡ a * y.val [MOD p] := by
    change (a * x.val) % p = (a * y.val) % p
    exact congrArg Fin.val hxy
  have hcancel : x.val ≡ y.val [MOD p] :=
    Nat.ModEq.cancel_left_of_coprime hcop hmod
  exact hcancel.eq_of_lt_of_lt x.isLt y.isLt

/-- At one synchronized position, the number of matching rough residues is
the population of the digit bin containing the reference state. -/
noncomputable def periodicMatchingResidues (b p u j : ℕ) : Finset ℕ := by
  classical
  exact (ThreeTier.positiveResidues p).filter
    (fun r => ThreeTier.periodicMatchAt b p u r j)

theorem periodicMatchAt_card_eq_digitBinPopulation {b p u j : ℕ}
    (hp : Nat.Prime p) (hpb : ¬p ∣ b) (hu : Nat.Coprime p u) :
    (periodicMatchingResidues b p u j).card =
      digitBinPopulation b p
        (digitBin b p ((b ^ j * u) % p)) := by
  classical
  let a := b ^ j * u
  have hpa : Nat.Coprime p a := (prime_coprime_base_pow hp hpb).mul_right hu
  have hbij := transportedRemainder_fin_bijective hp.pos hpa
  unfold periodicMatchingResidues
  rw [positiveResidues_eq_nonzeroResidues hp.pos]
  unfold digitBinPopulation
  refine Finset.card_bij
    (fun r _hr => transportedRemainder p a r) ?_ ?_ ?_
  · intro r hr
    have hr' := Finset.mem_filter.mp hr
    have hrrange := Finset.mem_erase.mp hr'.1
    have hrlt : r < p := Finset.mem_range.mp hrrange.2
    have hrylt : transportedRemainder p a r < p :=
      transportedRemainder_lt_of_pos p a r hp.pos
    have hry0 : transportedRemainder p a r ≠ 0 := by
      intro hy0
      have hmodzero : a * r ≡ a * 0 [MOD p] := by
        change (a * r) % p = (a * 0) % p
        simpa [transportedRemainder] using hy0
      have hcancel := Nat.ModEq.cancel_left_of_coprime hpa hmodzero
      have hrzero : r = 0 := hcancel.eq_of_lt_of_lt hrlt hp.pos
      exact hrrange.1 hrzero
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_erase.mpr ⟨hry0, Finset.mem_range.mpr hrylt⟩, ?_⟩
    have hmatch := hr'.2
    unfold ThreeTier.periodicMatchAt ThreeTier.periodicDigit
      ThreeTier.periodicResidue at hmatch
    change digitBin b p (transportedRemainder p a r) =
      digitBin b p ((b ^ j * u) % p)
    simpa only [a, transportedRemainder, Nat.mul_one] using hmatch
  · intro r₁ hr₁ r₂ hr₂ heq
    have hr₁' := Finset.mem_filter.mp hr₁
    have hr₂' := Finset.mem_filter.mp hr₂
    have hr₁lt : r₁ < p := Finset.mem_range.mp (Finset.mem_erase.mp hr₁'.1).2
    have hr₂lt : r₂ < p := Finset.mem_range.mp (Finset.mem_erase.mp hr₂'.1).2
    have hmod : a * r₁ ≡ a * r₂ [MOD p] := by
      change (a * r₁) % p = (a * r₂) % p
      simpa [transportedRemainder] using heq
    exact (Nat.ModEq.cancel_left_of_coprime hpa hmod).eq_of_lt_of_lt hr₁lt hr₂lt
  · intro y hy
    have hy' := Finset.mem_filter.mp hy
    have hyrange := Finset.mem_erase.mp hy'.1
    have hylt : y < p := Finset.mem_range.mp hyrange.2
    rcases hbij.2 (⟨y, hylt⟩ : Fin p) with ⟨x, hx⟩
    have hxval : transportedRemainder p a x.val = y := congrArg Fin.val hx
    have hx0 : x.val ≠ 0 := by
      intro hxzero
      have : y = 0 := by simpa [hxzero, transportedRemainder] using hxval.symm
      exact hyrange.1 this
    refine ⟨x.val, ?_, hxval⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_erase.mpr ⟨hx0, Finset.mem_range.mpr x.isLt⟩, ?_⟩
    unfold ThreeTier.periodicMatchAt ThreeTier.periodicDigit
      ThreeTier.periodicResidue
    have hydigit : digitBin b p y = digitBin b p ((b ^ j * u) % p) := hy'.2
    have htransport : (b ^ j * u * x.val) % p = y := by
      simpa only [a, transportedRemainder] using hxval
    rw [htransport]
    simpa only [Nat.mul_one] using hydigit

/-- Double counting the position-residue incidence relation converts the
literal periodic match total into the power-orbit bin sum. -/
theorem periodicNonterminatingMatchTotal_eq_powerOrbitBinSum
    {b p u L : ℕ} (hp : Nat.Prime p) (hpb : ¬p ∣ b)
    (hu : Nat.Coprime p u) :
    ThreeTier.periodicNonterminatingMatchTotal b p u L =
      powerOrbitBinSum (L := L) hp hpb hu := by
  classical
  unfold ThreeTier.periodicNonterminatingMatchTotal
    ThreeTier.periodicMatchCount ThreeTier.periodicMatchPositions
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  unfold powerOrbitBinSum orbitBinSum powerReferenceOrbit
  change (∑ y ∈ Finset.range L, ∑ x ∈ ThreeTier.positiveResidues p,
      if ThreeTier.periodicMatchAt b p u x y then 1 else 0) =
    ∑ i : Fin L, digitBinPopulation b p
      (digitBin b p ((b ^ (i : ℕ) * u) % p))
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← periodicMatchAt_card_eq_digitBinPopulation hp hpb hu]
  unfold periodicMatchingResidues
  simp only [Finset.card_filter]

/-- The literal common-depth field count is exactly the coset total score. -/
theorem clearedFieldMatchTotal_eq_cosetTotalMatchCount
    {b p m D L : ℕ} (hp : Nat.Prime p) (hpb : ¬p ∣ b)
    (hm : 1 ≤ m) (hD : m ∣ b ^ D) :
    ThreeTier.clearedFieldMatchTotal b p m D L =
      cosetTotalMatchCount m L
        (powerOrbitBinSum (L := L) hp hpb
          (prime_coprime_clearingCofactor hp hpb hD)) := by
  rw [ThreeTier.clearedFieldMatchTotal_eq_periodicFieldMatchTotal hp.pos hm hD]
  unfold ThreeTier.periodicFieldMatchTotal cosetTotalMatchCount
  rw [periodicNonterminatingMatchTotal_eq_powerOrbitBinSum hp hpb]

/-- The literal synchronized alignment is the real coset formula. -/
theorem clearedAlignmentReal_eq_cosetAlignmentReal
    {b p m D L : ℕ} (hp : Nat.Prime p) (hpb : ¬p ∣ b)
    (hm : 1 ≤ m) (hD : m ∣ b ^ D) (hL : 0 < L) :
    ThreeTier.clearedAlignmentReal b p m D L =
      cosetAlignmentReal p m L
        (powerOrbitBinSum (L := L) hp hpb
          (prime_coprime_clearingCofactor hp hpb hD)) := by
  have hp1 : p ≠ 1 := hp.ne_one
  have hmpos : 0 < m := by omega
  have hpm : 1 ≤ p * m := Nat.mul_pos hp.pos hmpos
  rw [ThreeTier.clearedAlignmentReal, if_neg hp1,
    clearedFieldMatchTotal_eq_cosetTotalMatchCount hp hpb hm hD]
  unfold cosetAlignmentReal cosetTotalMatchCount
  push_cast [Nat.cast_sub hm, Nat.cast_sub hpm]
  have hLR : (L : ℝ) ≠ 0 := by positivity
  field_simp

/-- Any two valid clearing cofactors differ, in one direction or the other,
by multiplication by a power of the base.  Hence they select the same
multiplicative coset. -/
theorem clearingCofactors_differ_by_base_power {b m D E : ℕ}
    (hD : m ∣ b ^ D) (hE : m ∣ b ^ E) :
    (∃ q, clearingCofactor b m E = b ^ q * clearingCofactor b m D) ∨
      ∃ q, clearingCofactor b m D = b ^ q * clearingCofactor b m E := by
  rcases le_total D E with hDE | hED
  · obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hDE
    exact Or.inl ⟨q, ThreeTier.clearingCofactor_add hD⟩
  · obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hED
    exact Or.inr ⟨q, ThreeTier.clearingCofactor_add hE⟩

/-- Multiplying the starting multiplier by any base power rotates a complete
orbit and leaves its bin sum unchanged. -/
theorem powerOrbitBinSum_mul_base_pow {b p u L q : ℕ}
    (hp : Nat.Prime p) (hpb : ¬p ∣ b) (hu : Nat.Coprime p u)
    (hperiod : b ^ L % p = 1 % p) :
    powerOrbitBinSum (u := b ^ q * u) (L := L) hp hpb
        ((prime_coprime_base_pow (D := q) hp hpb).mul_right hu) =
      powerOrbitBinSum (L := L) hp hpb hu := by
  rw [← periodicNonterminatingMatchTotal_eq_powerOrbitBinSum hp hpb
      ((prime_coprime_base_pow hp hpb).mul_right hu),
    ← periodicNonterminatingMatchTotal_eq_powerOrbitBinSum hp hpb hu]
  unfold ThreeTier.periodicNonterminatingMatchTotal
  apply Finset.sum_congr rfl
  intro r _
  exact ThreeTier.periodicMatchCount_mul_base_pow hperiod

/-- The orbit-bin sum depends only on the starting multiplier modulo the
prime. -/
theorem powerOrbitBinSum_congr_multiplier {b p u v L : ℕ}
    (hp : Nat.Prime p) (hpb : ¬p ∣ b)
    (hu : Nat.Coprime p u) (hv : Nat.Coprime p v)
    (hmod : u % p = v % p) :
    powerOrbitBinSum (L := L) hp hpb hu =
      powerOrbitBinSum (L := L) hp hpb hv := by
  unfold powerOrbitBinSum orbitBinSum powerReferenceOrbit
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  calc
    (b ^ (i : ℕ) * u) % p = ((b ^ (i : ℕ)) % p * (u % p)) % p :=
      Nat.mul_mod _ _ _
    _ = ((b ^ (i : ℕ)) % p * (v % p)) % p := by rw [hmod]
    _ = (b ^ (i : ℕ) * v) % p := (Nat.mul_mod _ _ _).symm

end NField.Alignment

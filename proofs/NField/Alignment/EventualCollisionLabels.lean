/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.TheStructureThatSurvives
import Mathlib.NumberTheory.PrimeCounting

/-! Every actual prime collision label occurs in the first-prime exhaustion. -/

namespace NField.Alignment.EventualCollisionLabels

open scoped BigOperators
open Filter TheStructureThatSurvives CollisionFluctuationSum CenteredCollisionSum

def allPrimeLabelSet (b ell : ℕ) : Finset ℤ :=
  insert 0 ((reducedResidues (allLagModulus b ell)).image (allLagTable b ell))

noncomputable def firstPrimeLabelSet (b ell N : ℕ) : Finset ℤ :=
  (Finset.range N).image (fun k => directAllLagDeviation b ell (Nat.nth Nat.Prime k))

theorem prime_label_mem {b ell p : ℕ} (hb : 2 ≤ b) (hell : 1 ≤ ell) (hp : p.Prime) :
    directAllLagDeviation b ell p ∈ allPrimeLabelSet b ell := by
  by_cases hdiv : p ∣ b
  · rw [primeDividingBase_directDeviation_zero hb hell hp hdiv]
    exact Finset.mem_insert_self _ _
  · have hcop : Nat.Coprime p b := hp.coprime_iff_not_dvd.mpr hdiv
    rw [directAllLagDeviation_eq_table_mod hb hell hcop]
    apply Finset.mem_insert_of_mem
    apply Finset.mem_image.mpr
    refine ⟨p % allLagModulus b ell, ?_, rfl⟩
    have hm : 0 < allLagModulus b ell := pow_pos (by omega) _
    have hpow := hcop.pow_right (ell + 1)
    have hmod : Nat.Coprime (p % allLagModulus b ell) (allLagModulus b ell) :=
      (ZMod.coprime_mod_iff_coprime _ _).mpr hpow
    have hpos : 0 < p % allLagModulus b ell := by
      by_contra hh
      have hz : p % allLagModulus b ell = 0 := by omega
      rw [hz] at hmod
      have hone : allLagModulus b ell = 1 := by simpa using hmod
      have hlarge : b ≤ allLagModulus b ell := Nat.le_pow (by omega)
      omega
    simp only [reducedResidues, Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨hpos, Nat.mod_lt _ hm⟩, hmod⟩

theorem every_table_label_is_prime_label {b ell : ℕ} (hb : 2 ≤ b) (hell : 1 ≤ ell)
    {z : ℤ} (hz : z ∈ allPrimeLabelSet b ell) :
    ∃ p, p.Prime ∧ directAllLagDeviation b ell p = z := by
  classical
  rcases Finset.mem_insert.mp hz with rfl | hz
  · obtain ⟨p, hp, hpb⟩ := Nat.exists_prime_and_dvd (show b ≠ 1 by omega)
    exact ⟨p, hp, primeDividingBase_directDeviation_zero hb hell hp hpb⟩
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨haint, hcop⟩ := Finset.mem_filter.mp ha
    obtain ⟨ha0, ham⟩ := Finset.mem_Ico.mp haint
    have hm : 0 < allLagModulus b ell := pow_pos (by omega) _
    letI : NeZero (allLagModulus b ell) := ⟨ne_of_gt hm⟩
    let u := ZMod.unitOfCoprime a hcop
    obtain ⟨p, hpb, hp, hres⟩ := unitClass_contains_arbitrarily_large_primes u b
    have hnd : ¬p ∣ b := fun hd => (Nat.le_of_dvd (by omega) hd).not_gt hpb
    have hpcop := hp.coprime_iff_not_dvd.mpr hnd
    refine ⟨p, hp, ?_⟩
    rw [directAllLagDeviation_eq_table_mod hb hell hpcop]
    have hval := congrArg ZMod.val hres
    have hmod : p % allLagModulus b ell = a := by
      simpa [u, ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt ham] using hval
    rw [hmod]

/-- Title: `Every prime label belongs to the fixed finite table`. -/
theorem firstPrimeLabelSet_subset {b ell : ℕ} (hb : 2 ≤ b) (hell : 1 ≤ ell) (N : ℕ) :
    firstPrimeLabelSet b ell N ⊆ allPrimeLabelSet b ell := by
  intro z hz
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
  exact prime_label_mem hb hell (Nat.prime_nth_prime i)

/-- Title: `Every fixed table label eventually occurs among primes`.

Every label in the actual all-prime table eventually occurs among the first primes. -/
theorem eventually_firstPrimeLabelSet_eq {b ell : ℕ} (hb : 2 ≤ b) (hell : 1 ≤ ell) :
    ∀ᶠ N in atTop, firstPrimeLabelSet b ell N = allPrimeLabelSet b ell := by
  have hevent : ∀ z ∈ allPrimeLabelSet b ell,
      ∀ᶠ N in atTop, z ∈ firstPrimeLabelSet b ell N := by
    intro z hz
    obtain ⟨p, hp, hlabel⟩ := every_table_label_is_prime_label hb hell hz
    obtain ⟨k, hk⟩ := Nat.subset_range_nth (p := Nat.Prime) hp
    apply Filter.eventually_atTop.mpr
    refine ⟨k + 1, fun N hN => ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨k, Finset.mem_range.mpr (by omega), by rw [hk, hlabel]⟩
  have hall := (Filter.eventually_all_finset (allPrimeLabelSet b ell)).mpr hevent
  filter_upwards [hall] with N hN
  exact Finset.Subset.antisymm (firstPrimeLabelSet_subset hb hell N) (fun z hz => hN z hz)

theorem firstPrimeLabelSet_card_le {b ell : ℕ} (hb : 2 ≤ b) (hell : 1 ≤ ell) (N : ℕ) :
    (firstPrimeLabelSet b ell N).card ≤ (allPrimeLabelSet b ell).card :=
  Finset.card_le_card (firstPrimeLabelSet_subset hb hell N)

theorem nontrivial_mode_proportion_tendsto_zero {b ell : ℕ} (hb : 2 ≤ b) (hell : 1 ≤ ell) :
    Tendsto (fun N : ℕ => ((firstPrimeLabelSet b ell N).card : ℝ) / N) atTop (nhds 0) := by
  apply Filter.Tendsto.congr' _ (fixedModeProportion_tendsto_zero (allPrimeLabelSet b ell).card)
  filter_upwards [eventually_firstPrimeLabelSet_eq hb hell] with N hN
  rw [hN]

end NField.Alignment.EventualCollisionLabels

/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.PacketLoads
/-! # Reversible lower and upper word parametrizations

Both maps land in the original cutoff interior. Their inverses recover the
actual centered phase, load and branch, including every occupied load.
-/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.LoadedWords

open CenteredPhase PhasePopulations

theorem word_phase_bounds {p m h : ℕ}
    (ha : packetLowerCutoff p ≤ h) (hc : h ≤ packetWordCutoff p m) :
    0 < h ∧ h ≤ packetUpperCutoff p ∧ (2 * m + 1) * h < p := by
  have hh : 2 ≤ h := by unfold packetLowerCutoff at ha; omega
  have hb := hc.trans (min_le_left _ _)
  have hd := hc.trans (min_le_right _ _)
  have hmul := (Nat.le_div_iff_mul_le (by omega : 0 < 2 * m + 1)).mp hd
  have hp : 1 ≤ p := by
    unfold packetUpperCutoff at hb
    have := Nat.div_le_self p 3
    omega
  refine ⟨by omega, hb, ?_⟩
  nlinarith [Nat.sub_add_cancel hp]

theorem lower_word_spec {p m v : ℕ} (hm : 0 < m) (hv : v ∈ lowerWords p m) :
    lowerClock p m v ∈ retainedClocks p ∧ packetLoad p (lowerClock p m v) = m ∧
      centeredPhase p (lowerClock p m v) = v + 1 ∧ lowerBranch p (lowerClock p m v) := by
  obtain ⟨hI, hmod⟩ := Finset.mem_filter.mp hv
  obtain ⟨ha, hc⟩ := Finset.mem_Icc.mp hI
  have ha2 : 2 ≤ packetLowerCutoff p := by unfold packetLowerCutoff; omega
  have hvl : packetLowerCutoff p ≤ v + 1 := by omega
  have hvc : v + 1 ≤ packetWordCutoff p m := by omega
  obtain ⟨hh, hb, hs⟩ := word_phase_bounds hvl hvc
  have hp1 : 1 ≤ p := by nlinarith
  have hvN : v ≤ p - 1 := by nlinarith [Nat.sub_add_cancel hp1]
  have hd : m ∣ p - 1 - v := (Nat.modEq_iff_dvd' hvN).mp hmod
  have he : p - (v + 1) = p - 1 - v := by omega
  rw [← he] at hd
  obtain ⟨hwide, hkp, _, hload, hcenter, hbranch⟩ := lower_quotient_spec hm hh hs hd
  have hclock : lowerClock p m v = (p - (v + 1)) / m := by unfold lowerClock; rw [he]
  rw [hclock]
  refine ⟨?_, hload, hcenter, hbranch⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
  rw [hcenter]
  exact ⟨hvl, hb⟩

theorem upper_word_spec {p m s : ℕ} (hm : 0 < m) (hs : s ∈ upperWords p m) :
    upperClock p m s ∈ retainedClocks p ∧ packetLoad p (upperClock p m s) = m ∧
      centeredPhase p (upperClock p m s) = s ∧ ¬lowerBranch p (upperClock p m s) := by
  obtain ⟨hI, hmod⟩ := Finset.mem_filter.mp hs
  obtain ⟨ha, hc⟩ := Finset.mem_Icc.mp hI
  obtain ⟨hh, hb, hphase⟩ := word_phase_bounds ha hc
  obtain ⟨hwide, hkp, _, hload, hcenter, hbranch⟩ :=
    upper_quotient_spec hm hh hphase (Nat.dvd_of_mod_eq_zero hmod)
  change (p + s) / (m + 1) ∈ retainedClocks p ∧ _
  refine ⟨?_, hload, hcenter, hbranch⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
  rw [hcenter]
  exact ⟨ha, hb⟩

theorem retained_lower_word {p k : ℕ} (hp : p.Prime)
    (hk : k ∈ retainedClocks p) (hbranch : lowerBranch p k) :
    centeredPhase p k - 1 ∈ lowerWords p (packetLoad p k) ∧
      lowerClock p (packetLoad p k) (centeredPhase p k - 1) = k := by
  obtain ⟨hk2, hkp, ha, _⟩ := retained_clock_bounds hk
  have hh : 0 < centeredPhase p k := by unfold packetLowerCutoff at ha; omega
  have hc := retained_phase_word_cutoff hp hk
  have hm : 0 < packetLoad p k := (retained_clock_load_bounds hk).1
  have hcenter : centeredPhase p k = p % k := min_eq_left hbranch
  have hd := (predecessor_remainder (by omega : 0 < k)
    (prime_remainder_pos hp hk2 hkp)).2
  have he : p - 1 = (centeredPhase p k - 1) + k * packetLoad p k := by
    have hdecomp := Nat.div_add_mod p k
    unfold packetLoad
    rw [hd, hcenter]
    omega
  constructor
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    rw [he]
    simp [Nat.add_mod]
  · unfold lowerClock
    rw [he, Nat.add_sub_cancel_left, Nat.mul_div_cancel _ hm]

theorem retained_upper_word {p k : ℕ} (hp : p.Prime)
    (hk : k ∈ retainedClocks p) (hbranch : ¬lowerBranch p k) :
    centeredPhase p k ∈ upperWords p (packetLoad p k) ∧
      upperClock p (packetLoad p k) (centeredPhase p k) = k := by
  obtain ⟨hk2, hkp, ha, _⟩ := retained_clock_bounds hk
  have hc := retained_phase_word_cutoff hp hk
  have hl : k - p % k < p % k := Nat.lt_of_not_ge hbranch
  have hcenter : centeredPhase p k = k - p % k := min_eq_right hl.le
  have hd := (predecessor_remainder (by omega : 0 < k)
    (prime_remainder_pos hp hk2 hkp)).2
  have he : p + centeredPhase p k = k * (packetLoad p k + 1) := by
    have hdecomp := Nat.div_add_mod p k
    have hrem := Nat.mod_lt p (by omega : 0 < k)
    unfold packetLoad
    rw [hd, hcenter]
    nlinarith [Nat.sub_add_cancel hrem.le]
  constructor
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨ha, hc⟩, ?_⟩
    rw [he]
    simp
  · unfold upperClock
    rw [he, Nat.mul_div_cancel _ (by omega : 0 < packetLoad p k + 1)]

theorem lower_word_injective {p m : ℕ} (hm : 0 < m) :
    Set.InjOn (lowerClock p m) (lowerWords p m : Set ℕ) := by
  intro v hv w hw he
  have hvh := (lower_word_spec hm hv).2.2.1
  have hwh := (lower_word_spec hm hw).2.2.1
  rw [he] at hvh
  omega

theorem upper_word_injective {p m : ℕ} (hm : 0 < m) :
    Set.InjOn (upperClock p m) (upperWords p m : Set ℕ) := by
  intro s hs t ht he
  have hsh := (upper_word_spec hm hs).2.2.1
  have hth := (upper_word_spec hm ht).2.2.1
  rw [he] at hsh
  omega

theorem lower_upper_clock_ne {p m n v s : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hv : v ∈ lowerWords p m) (hs : s ∈ upperWords p n) :
    lowerClock p m v ≠ upperClock p n s := by
  intro he
  have hl := (lower_word_spec hm hv).2.2.2
  have hu := (upper_word_spec hn hs).2.2.2
  exact hu (he ▸ hl)

theorem retained_clock_word_partition {p k : ℕ} (hp : p.Prime) :
    k ∈ retainedClocks p ↔
      ∃ m, 1 ≤ m ∧ m ≤ packetMaxLoad p ∧
        ((∃ v ∈ lowerWords p m, lowerClock p m v = k) ∨
         (∃ s ∈ upperWords p m, upperClock p m s = k)) := by
  constructor
  · intro hk
    obtain ⟨hm, hM, _⟩ := retained_clock_load_bounds hk
    refine ⟨packetLoad p k, hm, hM, ?_⟩
    by_cases hb : lowerBranch p k
    · exact Or.inl ⟨centeredPhase p k - 1, retained_lower_word hp hk hb⟩
    · exact Or.inr ⟨centeredPhase p k, retained_upper_word hp hk hb⟩
  · rintro ⟨m, hm, _, (⟨v, hv, rfl⟩ | ⟨s, hs, rfl⟩)⟩
    · exact (lower_word_spec hm hv).1
    · exact (upper_word_spec hm hs).1

end NField.ResetForests.LoadedWords

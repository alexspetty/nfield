/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.PacketCells
/-! # Complete packets of actual cutoff clocks

The integer cell arithmetic is transported to the original lower and upper
word populations, without changing their clock maps or source weights.
-/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.CompletePackets

open CenteredPhase PhasePopulations LoadedWords

def completeStarts (p m : ℕ) : Finset ℕ :=
  (upperWords p m).filter (fun s => s + m ≤ packetWordCutoff p m - 1)
def packetLowerWords (p m s : ℕ) : Finset ℕ :=
  (lowerWords p m).filter (fun v => s ≤ v ∧ v ≤ s + m)
def packetClocks (p m s : ℕ) : Finset ℕ :=
  insert (upperClock p m s) ((packetLowerWords p m s).image (lowerClock p m))
def packetDelta (p m s : ℕ) : ℕ := (p - 1 - s) % m

theorem nat_lower_congruence {p m v : ℕ} (hp : 1 ≤ p) :
    Int.ModEq (m : ℤ) (v : ℤ) ((p : ℤ) - 1) ↔ v % m = (p - 1) % m := by
  have he : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by omega
  rw [← he, Int.natCast_modEq_iff]
  rfl

theorem nat_cell_delta {p m s : ℕ} (hp : 1 ≤ p) (hs : s ≤ p - 1) :
    cellDelta (p : ℤ) (m : ℤ) (s : ℤ) = (packetDelta p m s : ℤ) := by
  have he : ((p - 1 - s : ℕ) : ℤ) = (p : ℤ) - 1 - s := by omega
  unfold cellDelta packetDelta
  rw [← he]
  norm_cast

theorem complete_start_bounds {p m s : ℕ} (_hm : 0 < m)
    (hs : s ∈ completeStarts p m) :
    s ∈ upperWords p m ∧ packetLowerCutoff p ≤ s ∧
      s + m ≤ packetWordCutoff p m - 1 ∧ s ≤ p - 1 := by
  obtain ⟨hu, hhi⟩ := Finset.mem_filter.mp hs
  obtain ⟨hI, _⟩ := Finset.mem_filter.mp hu
  obtain ⟨ha, hc⟩ := Finset.mem_Icc.mp hI
  have hphase := (word_phase_bounds ha hc).2.2
  have hp1 : 1 ≤ p := by nlinarith
  refine ⟨hu, ha, hhi, ?_⟩
  nlinarith [Nat.sub_add_cancel hp1]

theorem complete_lower_word_members {p m s v : ℕ} (hm : 0 < m)
    (hs : s ∈ completeStarts p m) :
    v ∈ packetLowerWords p m s ↔
      s ≤ v ∧ v ≤ s + m ∧ v % m = (p - 1) % m := by
  obtain ⟨_, ha, hhi, _⟩ := complete_start_bounds hm hs
  simp only [packetLowerWords, Finset.mem_filter, lowerWords, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨_, hmod⟩, hlo, hhigh⟩
    exact ⟨hlo, hhigh, hmod⟩
  · rintro ⟨hlo, hhigh, hmod⟩
    exact ⟨⟨⟨by omega, by omega⟩, hmod⟩, hlo, hhigh⟩

theorem complete_lower_word_formula {p m s v : ℕ} (hp : 1 ≤ p) (hm : 0 < m)
    (hs : s ∈ completeStarts p m) :
    v ∈ packetLowerWords p m s ↔
      v = s + packetDelta p m s ∨ (packetDelta p m s = 0 ∧ v = s + m) := by
  have hsN := (complete_start_bounds hm hs).2.2.2
  have hδ := nat_cell_delta hp hsN (m := m)
  have hmZ : (0 : ℤ) < m := by exact_mod_cast hm
  have hc : v ∈ packetLowerWords p m s ↔
      (v : ℤ) ∈ lowerCellWords (p : ℤ) (m : ℤ) (s : ℤ) := by
    rw [complete_lower_word_members hm hs]
    simp only [lowerCellWords, Finset.mem_filter, Finset.mem_Icc,
      nat_lower_congruence hp]
    norm_cast
    tauto
  rw [hc, lower_cell_members hmZ, hδ]
  norm_cast

theorem complete_lower_word_set {p m s : ℕ} (hp : 1 ≤ p) (hm : 0 < m)
    (hs : s ∈ completeStarts p m) :
    packetLowerWords p m s =
      if packetDelta p m s = 0 then {s, s + m} else {s + packetDelta p m s} := by
  ext v
  rw [complete_lower_word_formula hp hm hs]
  by_cases hd : packetDelta p m s = 0 <;> simp [hd, or_comm]

theorem complete_lower_word_card {p m s : ℕ} (hp : 1 ≤ p) (hm : 0 < m)
    (hs : s ∈ completeStarts p m) :
    (packetLowerWords p m s).card = if packetDelta p m s = 0 then 2 else 1 := by
  rw [complete_lower_word_set hp hm hs]
  have hne : s ≠ s + m := by omega
  by_cases hd : packetDelta p m s = 0
  · simp only [hd, if_true, Finset.card_pair hne]
  · simp only [hd, if_false, Finset.card_singleton]

theorem packet_lower_injective {p m s : ℕ} (hm : 0 < m) :
    Set.InjOn (lowerClock p m) (packetLowerWords p m s : Set ℕ) := by
  intro v hv w hw he
  exact lower_word_injective hm (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hw).1 he

theorem packet_upper_not_lower {p m s : ℕ} (hm : 0 < m)
    (hs : s ∈ completeStarts p m) :
    upperClock p m s ∉ (packetLowerWords p m s).image (lowerClock p m) := by
  intro hk
  obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hk
  exact lower_upper_clock_ne hm hm (Finset.mem_filter.mp hv).1
    (Finset.mem_filter.mp hs).1 he

theorem packet_clock_card {p m s : ℕ} (hp : 1 ≤ p) (hm : 0 < m)
    (hs : s ∈ completeStarts p m) :
    (packetClocks p m s).card = if packetDelta p m s = 0 then 3 else 2 := by
  unfold packetClocks
  rw [Finset.card_insert_of_notMem (packet_upper_not_lower hm hs),
    Finset.card_image_of_injOn (packet_lower_injective hm), complete_lower_word_card hp hm hs]
  split_ifs <;> rfl

theorem packet_clock_population {p m s k : ℕ} (hm : 0 < m)
    (hs : s ∈ completeStarts p m) (hk : k ∈ packetClocks p m s) :
    k ∈ loadClocks p m := by
  rcases Finset.mem_insert.mp hk with rfl | hk
  · have hspec := upper_word_spec hm (Finset.mem_filter.mp hs).1
    exact Finset.mem_filter.mpr ⟨hspec.1, hspec.2.1⟩
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hk
    have hspec := lower_word_spec hm (Finset.mem_filter.mp hv).1
    exact Finset.mem_filter.mpr ⟨hspec.1, hspec.2.1⟩

theorem complete_start_upper_integer {p m s : ℕ} (hs : s ∈ completeStarts p m) :
    ((m : ℤ) + 1) ∣ (p : ℤ) + s := by
  have hmod := (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).2
  have hd : m + 1 ∣ p + s := Nat.dvd_of_mod_eq_zero hmod
  exact_mod_cast hd

theorem same_load_packets_disjoint {p m s t : ℕ} (hm : 0 < m)
    (hs : s ∈ completeStarts p m) (ht : t ∈ completeStarts p m) (hst : s ≠ t) :
    Disjoint (packetClocks p m s) (packetClocks p m t) := by
  apply Finset.disjoint_left.mpr
  intro k hks hkt
  rcases Finset.mem_insert.mp hks with hks | hks
  · rcases Finset.mem_insert.mp hkt with hkt | hkt
    · exact hst (upper_word_injective hm (Finset.mem_filter.mp hs).1
        (Finset.mem_filter.mp ht).1 (hks.symm.trans hkt))
    · obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hkt
      exact lower_upper_clock_ne hm hm (Finset.mem_filter.mp hv).1
        (Finset.mem_filter.mp hs).1 (he.trans hks)
  · obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hks
    rcases Finset.mem_insert.mp hkt with hkt | hkt
    · exact lower_upper_clock_ne hm hm (Finset.mem_filter.mp hv).1
        (Finset.mem_filter.mp ht).1 (he.trans hkt)
    · obtain ⟨w, hw, hf⟩ := Finset.mem_image.mp hkt
      have hvw := lower_word_injective hm (Finset.mem_filter.mp hv).1
        (Finset.mem_filter.mp hw).1 (he.trans hf.symm)
      have hvs := (Finset.mem_filter.mp hv).2
      have hwt := (Finset.mem_filter.mp hw).2
      have hmZ : (0 : ℤ) < m := by exact_mod_cast hm
      have ha := cell_anchor_unique (v := (v : ℤ)) hmZ (complete_start_upper_integer hs)
        (by exact_mod_cast hvs.1) (by exact_mod_cast hvs.2)
      have hb := cell_anchor_unique (v := (w : ℤ)) hmZ (complete_start_upper_integer ht)
        (by exact_mod_cast hwt.1) (by exact_mod_cast hwt.2)
      rw [← hvw] at hb
      exact hst (by exact_mod_cast ha.symm.trans hb)

theorem different_load_packets_disjoint {p m n s t : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hs : s ∈ completeStarts p m) (ht : t ∈ completeStarts p n) (hmn : m ≠ n) :
    Disjoint (packetClocks p m s) (packetClocks p n t) := by
  apply Finset.disjoint_left.mpr
  intro k hk hl
  have hkm := (Finset.mem_filter.mp (packet_clock_population hm hs hk)).2
  have hkn := (Finset.mem_filter.mp (packet_clock_population hn ht hl)).2
  exact hmn (hkm.symm.trans hkn)

end NField.ResetForests.CompletePackets

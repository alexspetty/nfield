/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.PacketConstruction
/-! # The complete packet fringe in the original cutoff population

Every omitted lower word lies in one of two endpoint intervals. Every
omitted upper word lies in the final partial cell. No nonempty common
interval is assumed.
-/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.CompletePackets

open scoped BigOperators
open CenteredPhase PhasePopulations LoadedWords

def loadPackets (p m : ℕ) : Finset ℕ :=
  (completeStarts p m).biUnion (packetClocks p m)
def loadFringe (p m : ℕ) : Finset ℕ := loadClocks p m \ loadPackets p m
def completePackets (p : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (packetMaxLoad p)).biUnion (loadPackets p)
def packetFringe (p : ℕ) : Finset ℕ := retainedClocks p \ completePackets p
def leftLowerFringeWords (p m : ℕ) : Finset ℕ :=
  (lowerWords p m).filter (fun v =>
    (packetLowerCutoff p : ℤ) - 1 ≤ v ∧
      (v : ℤ) ≤ (packetLowerCutoff p : ℤ) - 1 + m)
def rightLowerFringeWords (p m : ℕ) : Finset ℕ :=
  (lowerWords p m).filter (fun v =>
    (packetWordCutoff p m : ℤ) - 1 - m ≤ v ∧
      (v : ℤ) ≤ (packetWordCutoff p m : ℤ) - 1)
def upperFringeWords (p m : ℕ) : Finset ℕ :=
  (upperWords p m).filter (fun s => packetWordCutoff p m - 1 < s + m)

theorem lower_interval_card {p m : ℕ} (hp : 1 ≤ p) (hm : 0 < m) (l : ℤ) :
    ((lowerWords p m).filter (fun v : ℕ => l ≤ (v : ℤ) ∧ (v : ℤ) ≤ l + m)).card ≤ 2 := by
  let W := (lowerWords p m).filter (fun v : ℕ => l ≤ (v : ℤ) ∧ (v : ℤ) ≤ l + m)
  have hsub : W.image (fun v : ℕ => (v : ℤ)) ⊆ lowerCellWords p m l := by
    intro v hv
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hw, hI⟩ := Finset.mem_filter.mp hn
    have hmod := (Finset.mem_filter.mp hw).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr hI,
      (nat_lower_congruence hp).mpr hmod⟩
  have hinj : Set.InjOn (fun v : ℕ => (v : ℤ)) (W : Set ℕ) := by
    intro v _ w _ he
    change (v : ℤ) = (w : ℤ) at he
    exact_mod_cast he
  calc
    W.card = (W.image (fun v : ℕ => (v : ℤ))).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ (lowerCellWords p m l).card := Finset.card_le_card hsub
    _ ≤ 2 := (lower_cell_card_bounds (by exact_mod_cast hm)).2

theorem left_lower_fringe_card {p m : ℕ} (hp : 1 ≤ p) (hm : 0 < m) :
    (leftLowerFringeWords p m).card ≤ 2 := lower_interval_card hp hm _

theorem right_lower_fringe_card {p m : ℕ} (hp : 1 ≤ p) (hm : 0 < m) :
    (rightLowerFringeWords p m).card ≤ 2 := by
  simpa only [rightLowerFringeWords, sub_add_cancel] using
    lower_interval_card hp hm ((packetWordCutoff p m : ℤ) - 1 - m)

theorem upper_fringe_card {p m : ℕ} (hm : 0 < m) :
    (upperFringeWords p m).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro s hs t ht
  obtain ⟨hsu, hsbad⟩ := Finset.mem_filter.mp hs
  obtain ⟨htu, htbad⟩ := Finset.mem_filter.mp ht
  obtain ⟨hsI, hsmod⟩ := Finset.mem_filter.mp hsu
  obtain ⟨htI, htmod⟩ := Finset.mem_filter.mp htu
  have hsC := (Finset.mem_Icc.mp hsI).2
  have htC := (Finset.mem_Icc.mp htI).2
  have hsD : ((m : ℤ) + 1) ∣ (p : ℤ) + s := by
    exact_mod_cast Nat.dvd_of_mod_eq_zero hsmod
  have htD : ((m : ℤ) + 1) ∣ (p : ℤ) + t := by
    exact_mod_cast Nat.dvd_of_mod_eq_zero htmod
  have hmZ : (0 : ℤ) < m := by exact_mod_cast hm
  have hsCell := cell_anchor_unique (v := (packetWordCutoff p m : ℤ)) hmZ hsD
    (by exact_mod_cast hsC) (by exact_mod_cast (by omega : packetWordCutoff p m ≤ s + m))
  have htCell := cell_anchor_unique (v := (packetWordCutoff p m : ℤ)) hmZ htD
    (by exact_mod_cast htC) (by exact_mod_cast (by omega : packetWordCutoff p m ≤ t + m))
  exact_mod_cast hsCell.symm.trans htCell

theorem lower_away_from_endpoints_in_packet {p m v : ℕ} (hm : 0 < m)
    (hv : v ∈ lowerWords p m) (hl : v ∉ leftLowerFringeWords p m)
    (hr : v ∉ rightLowerFringeWords p m) :
    lowerClock p m v ∈ loadPackets p m := by
  obtain ⟨hvI, _⟩ := Finset.mem_filter.mp hv
  obtain ⟨hva, hvc⟩ := Finset.mem_Icc.mp hvI
  have ha2 : 2 ≤ packetLowerCutoff p := by unfold packetLowerCutoff; omega
  have hc1 : 1 ≤ packetWordCutoff p m := by omega
  have hvaZ : (packetLowerCutoff p : ℤ) - 1 ≤ v := by omega
  have hvcZ : (v : ℤ) ≤ (packetWordCutoff p m : ℤ) - 1 := by omega
  have hleft : (packetLowerCutoff p : ℤ) - 1 + m < v := by
    by_contra hn
    exact hl (Finset.mem_filter.mpr ⟨hv, hvaZ, by omega⟩)
  have hright : (v : ℤ) < (packetWordCutoff p m : ℤ) - 1 - m := by
    by_contra hn
    exact hr (Finset.mem_filter.mpr ⟨hv, by omega, hvcZ⟩)
  let z := cellAnchor (p : ℤ) (m : ℤ) (v : ℤ)
  have hmZ : (0 : ℤ) < m := by exact_mod_cast hm
  have hzb := cell_anchor_bounds (p : ℤ) (v : ℤ) hmZ
  have hza : (packetLowerCutoff p : ℤ) ≤ z := by dsimp [z]; omega
  have hzc : z + m ≤ (packetWordCutoff p m : ℤ) - 1 := by dsimp [z]; omega
  have hz0 : 0 ≤ z := by omega
  let s := z.toNat
  have hsZ : (s : ℤ) = z := Int.toNat_of_nonneg hz0
  have hsa : packetLowerCutoff p ≤ s := by omega
  have hsc : s + m ≤ packetWordCutoff p m - 1 := by omega
  have hsu : s ≤ packetWordCutoff p m := by omega
  have hsd : m + 1 ∣ p + s := by
    have hd := cell_anchor_upper (p : ℤ) (m : ℤ) (v : ℤ)
    change ((m : ℤ) + 1) ∣ (p : ℤ) + z at hd
    rw [← hsZ] at hd
    exact_mod_cast hd
  have hsupper : s ∈ upperWords p m := Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨hsa, hsu⟩, Nat.mod_eq_zero_of_dvd hsd⟩
  have hscomplete : s ∈ completeStarts p m := Finset.mem_filter.mpr ⟨hsupper, hsc⟩
  have hvs : s ≤ v ∧ v ≤ s + m := by omega
  have hvpacket : v ∈ packetLowerWords p m s := Finset.mem_filter.mpr ⟨hv, hvs⟩
  exact Finset.mem_biUnion.mpr ⟨s, hscomplete,
    Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨v, hvpacket, rfl⟩)⟩

theorem load_fringe_subset_endpoints {p m : ℕ} (hp : p.Prime) (hm : 0 < m) :
    loadFringe p m ⊆
      ((leftLowerFringeWords p m).image (lowerClock p m) ∪
       (rightLowerFringeWords p m).image (lowerClock p m)) ∪
       (upperFringeWords p m).image (upperClock p m) := by
  intro k hk
  obtain ⟨hload, hnot⟩ := Finset.mem_sdiff.mp hk
  rw [load_clocks_eq_word_images hp hm] at hload
  rcases Finset.mem_union.mp hload with hlow | hupp
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hlow
    by_cases hl : v ∈ leftLowerFringeWords p m
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v, hl, rfl⟩))
    · by_cases hr : v ∈ rightLowerFringeWords p m
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v, hr, rfl⟩))
      · exact False.elim (hnot (lower_away_from_endpoints_in_packet hm hv hl hr))
  · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hupp
    have hbad : packetWordCutoff p m - 1 < s + m := by
      by_contra hn
      have hc : s ∈ completeStarts p m := Finset.mem_filter.mpr ⟨hs, by omega⟩
      exact hnot (Finset.mem_biUnion.mpr ⟨s, hc, Finset.mem_insert_self _ _⟩)
    exact Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨s, Finset.mem_filter.mpr ⟨hs, hbad⟩, rfl⟩)

theorem load_fringe_card {p m : ℕ} (hp : p.Prime) (hm : 0 < m) :
    (loadFringe p m).card ≤ 8 := by
  have hL := (Finset.card_image_le (f := lowerClock p m) (s := leftLowerFringeWords p m)).trans
    (left_lower_fringe_card hp.one_le hm)
  have hR := (Finset.card_image_le (f := lowerClock p m) (s := rightLowerFringeWords p m)).trans
    (right_lower_fringe_card hp.one_le hm)
  have hU := (Finset.card_image_le (f := upperClock p m) (s := upperFringeWords p m)).trans
    (upper_fringe_card hm)
  calc
    _ ≤ (((leftLowerFringeWords p m).image (lowerClock p m) ∪
       (rightLowerFringeWords p m).image (lowerClock p m)) ∪
       (upperFringeWords p m).image (upperClock p m)).card :=
      Finset.card_le_card (load_fringe_subset_endpoints hp hm)
    _ ≤ ((leftLowerFringeWords p m).image (lowerClock p m)).card +
      ((rightLowerFringeWords p m).image (lowerClock p m)).card +
      ((upperFringeWords p m).image (upperClock p m)).card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    _ ≤ 2 + 2 + 1 := Nat.add_le_add (Nat.add_le_add hL hR) hU
    _ ≤ 8 := by decide

theorem packet_fringe_subset_load_fringes {p : ℕ} :
    packetFringe p ⊆ (Finset.Icc 1 (packetMaxLoad p)).biUnion (loadFringe p) := by
  intro k hk
  obtain ⟨hr, hnot⟩ := Finset.mem_sdiff.mp hk
  obtain ⟨hm, hM, _⟩ := retained_clock_load_bounds hr
  have hI := Finset.mem_Icc.mpr ⟨hm, hM⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨packetLoad p k, hI, Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hr, rfl⟩, ?_⟩⟩
  intro hload
  exact hnot (Finset.mem_biUnion.mpr ⟨packetLoad p k, hI, hload⟩)

theorem packet_fringe_card {p : ℕ} (hp : p.Prime) :
    (packetFringe p).card ≤ 8 * packetMaxLoad p := by
  calc
    _ ≤ ((Finset.Icc 1 (packetMaxLoad p)).biUnion (loadFringe p)).card :=
      Finset.card_le_card packet_fringe_subset_load_fringes
    _ ≤ ∑ m ∈ Finset.Icc 1 (packetMaxLoad p), (loadFringe p m).card := Finset.card_biUnion_le
    _ ≤ ∑ _m ∈ Finset.Icc 1 (packetMaxLoad p), 8 :=
      Finset.sum_le_sum (fun m hm => load_fringe_card hp (Finset.mem_Icc.mp hm).1)
    _ = _ := by simp [mul_comm]

end NField.ResetForests.CompletePackets

/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.LoadOnePackets
/-! # The sharper four-clock fringe at load one -/

noncomputable section
set_option autoImplicit false

namespace NField.ResetForests.LoadOnePackets

open PhasePopulations LoadedWords CompletePackets

def loadOneRightFringeWords (p : ℕ) : Finset ℕ :=
  (lowerWords p 1).filter (fun v => v=packetWordCutoff p 1-1)

theorem load_one_right_fringe_card (p : ℕ) : (loadOneRightFringeWords p).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro v hv w hw
  exact (Finset.mem_filter.mp hv).2.trans (Finset.mem_filter.mp hw).2.symm

theorem load_one_lower_away_from_edges {p v : ℕ} (hv : v ∈ lowerWords p 1)
    (hl : v ∉ leftLowerFringeWords p 1) (hr : v ≠ packetWordCutoff p 1-1) :
    lowerClock p 1 v ∈ loadPackets p 1 := by
  obtain ⟨hvI,_⟩ := Finset.mem_filter.mp hv
  obtain ⟨hva,hvc⟩ := Finset.mem_Icc.mp hvI
  have ha2 : 2 ≤ packetLowerCutoff p := by unfold packetLowerCutoff; omega
  have hleft : packetLowerCutoff p<v := by
    by_contra hn
    apply hl
    exact Finset.mem_filter.mpr ⟨hv,by omega,by omega⟩
  have hright : v<packetWordCutoff p 1-1 := lt_of_le_of_ne hvc hr
  let s := v-(p+v)%2
  have hmod : (p+s)%2=0 := by
    dsimp only [s]
    omega
  have hslo : packetLowerCutoff p ≤ s := by dsimp only [s]; omega
  have hshi : s+1 ≤ packetWordCutoff p 1-1 := by dsimp only [s]; omega
  have hvs : s ≤ v ∧ v ≤ s+1 := by dsimp only [s]; omega
  have hu : s ∈ upperWords p 1 := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨hslo,by omega⟩,hmod⟩
  have hs : s ∈ completeStarts p 1 := Finset.mem_filter.mpr ⟨hu,hshi⟩
  have hvp : v ∈ packetLowerWords p 1 s := Finset.mem_filter.mpr ⟨hv,hvs⟩
  exact Finset.mem_biUnion.mpr ⟨s,hs,
    Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨v,hvp,rfl⟩)⟩

theorem load_one_fringe_subset {p : ℕ} (hp : p.Prime) :
    loadFringe p 1 ⊆
      ((leftLowerFringeWords p 1).image (lowerClock p 1) ∪
       (loadOneRightFringeWords p).image (lowerClock p 1)) ∪
       (upperFringeWords p 1).image (upperClock p 1) := by
  intro k hk
  obtain ⟨hload,hnot⟩ := Finset.mem_sdiff.mp hk
  rw [load_clocks_eq_word_images hp (by decide)] at hload
  rcases Finset.mem_union.mp hload with hlow | hupp
  · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hlow
    by_cases hl : v ∈ leftLowerFringeWords p 1
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v,hl,rfl⟩))
    · by_cases hr : v=packetWordCutoff p 1-1
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨v,Finset.mem_filter.mpr ⟨hv,hr⟩,rfl⟩))
      · exact False.elim (hnot (load_one_lower_away_from_edges hv hl hr))
  · obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hupp
    have hbad : packetWordCutoff p 1-1<s+1 := by
      by_contra hn
      have hc : s ∈ completeStarts p 1 := Finset.mem_filter.mpr ⟨hs,by omega⟩
      exact hnot (Finset.mem_biUnion.mpr ⟨s,hc,Finset.mem_insert_self _ _⟩)
    exact Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨s,Finset.mem_filter.mpr ⟨hs,hbad⟩,rfl⟩)

/-- Title: `The complete load-one packets leave at most four actual clocks of that load`. -/
theorem load_one_fringe_card {p : ℕ} (hp : p.Prime) : (loadFringe p 1).card ≤ 4 := by
  have hL := (Finset.card_image_le (f := lowerClock p 1) (s := leftLowerFringeWords p 1)).trans
    (left_lower_fringe_card hp.one_le (by decide))
  have hR := (Finset.card_image_le (f := lowerClock p 1) (s := loadOneRightFringeWords p)).trans
    (load_one_right_fringe_card p)
  have hU := (Finset.card_image_le (f := upperClock p 1) (s := upperFringeWords p 1)).trans
    (upper_fringe_card (by decide))
  calc
    _  ≤  (((leftLowerFringeWords p 1).image (lowerClock p 1) ∪
       (loadOneRightFringeWords p).image (lowerClock p 1)) ∪
       (upperFringeWords p 1).image (upperClock p 1)).card :=
      Finset.card_le_card (load_one_fringe_subset hp)
    _  ≤  ((leftLowerFringeWords p 1).image (lowerClock p 1)).card+
      ((loadOneRightFringeWords p).image (lowerClock p 1)).card+
      ((upperFringeWords p 1).image (upperClock p 1)).card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    _  ≤  2+1+1 := Nat.add_le_add (Nat.add_le_add hL hR) hU

end NField.ResetForests.LoadOnePackets

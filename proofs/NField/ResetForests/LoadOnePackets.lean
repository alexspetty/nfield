/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.PhaseIntegration
/-! # The complete load-one packets and their literal three clocks -/

noncomputable section
set_option autoImplicit false

namespace NField.ResetForests.LoadOnePackets

open scoped BigOperators
open PhasePopulations LoadedWords CompletePackets

theorem load_one_word_cutoff (p : ℕ) : packetWordCutoff p 1=packetUpperCutoff p := by
  unfold packetWordCutoff
  norm_num only [Nat.mul_one,Nat.reduceAdd]
  apply min_eq_left
  unfold packetUpperCutoff
  omega

theorem load_one_lower_words (p : ℕ) :
    lowerWords p 1=Finset.Icc (packetLowerCutoff p-1) (packetUpperCutoff p-1) := by
  simp only [lowerWords,load_one_word_cutoff,Nat.mod_one,Finset.filter_true]

theorem load_one_upper_words {p : ℕ} (hp : Odd p) :
    upperWords p 1=(Finset.Icc (packetLowerCutoff p) (packetUpperCutoff p)).filter Odd := by
  have hpm := Nat.odd_iff.mp hp
  ext s
  simp only [upperWords,Finset.mem_filter,Finset.mem_Icc,load_one_word_cutoff,
    Nat.reduceAdd,Nat.odd_iff]
  omega

/-- Title: `The complete load-one starts are exactly the printed odd word range`. -/
theorem load_one_complete_start {p s : ℕ} (hp : Odd p) :
    s ∈ completeStarts p 1 ↔
      packetLowerCutoff p ≤ s ∧ s ≤ packetUpperCutoff p-2 ∧ Odd s := by
  have ha : 2≤packetLowerCutoff p := by unfold packetLowerCutoff; omega
  constructor
  · intro hs
    obtain ⟨hu,hcell⟩ := Finset.mem_filter.mp hs
    rw [load_one_word_cutoff] at hcell
    rw [load_one_upper_words hp] at hu
    obtain ⟨hI,hodd⟩ := Finset.mem_filter.mp hu
    obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hI
    exact ⟨hlo,by omega,hodd⟩
  · rintro ⟨hlo,hhi,hodd⟩
    have hu : s ∈ upperWords p 1 := by
      rw [load_one_upper_words hp]
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hlo,by omega⟩,hodd⟩
    apply Finset.mem_filter.mpr
    refine ⟨hu,?_⟩
    rw [load_one_word_cutoff]
    omega

theorem load_one_start_set {p : ℕ} (hp : Odd p) :
    completeStarts p 1=(Finset.Icc (packetLowerCutoff p) (packetUpperCutoff p-2)).filter Odd := by
  ext s
  simp only [load_one_complete_start hp,Finset.mem_filter,Finset.mem_Icc]
  tauto

theorem load_one_delta (p s : ℕ) : packetDelta p 1 s=0 := by simp only [packetDelta,Nat.mod_one]

theorem load_one_lower_packet {p s : ℕ} (hp : 1≤p) (hs : s ∈ completeStarts p 1) :
    packetLowerWords p 1 s={s,s+1} := by
  rw [complete_lower_word_set hp (by decide) hs,load_one_delta,if_pos rfl]

/-- Title: `Every actual complete load-one packet has the three printed denominators`. -/
theorem load_one_packet_clocks {p s : ℕ} (hp : 1≤p) (hs : s ∈ completeStarts p 1) :
    packetClocks p 1 s={p-s-1,p-s-2,(p+s)/2} := by
  rw [packetClocks,load_one_lower_packet hp hs]
  simp only [Finset.image_insert,Finset.image_singleton,lowerClock,upperClock,
    Nat.div_one,Nat.reduceAdd]
  have h1 : p-1-s=p-s-1 := by omega
  have h2 : p-1-(s+1)=p-s-2 := by omega
  rw [h1,h2]
  ext k
  simp only [Finset.mem_insert,Finset.mem_singleton]
  tauto

theorem load_one_packet_card {p s : ℕ} (hp : 1≤p) (hs : s ∈ completeStarts p 1) :
    (packetClocks p 1 s).card=3 := by
  rw [packet_clock_card hp (by decide) hs,load_one_delta,if_pos rfl]

theorem load_one_packets {p : ℕ} (hp : p.Prime) (hodd : p≠2) :
    loadPackets p 1=
      ((Finset.Icc (packetLowerCutoff p) (packetUpperCutoff p-2)).filter Odd).biUnion
        (fun s => {p-s-1,p-s-2,(p+s)/2}) := by
  rw [loadPackets]
  have he : (completeStarts p 1).biUnion (packetClocks p 1)=
      (completeStarts p 1).biUnion (fun s => {p-s-1,p-s-2,(p+s)/2}) := by
    apply Finset.biUnion_congr rfl
    intro s hs
    exact load_one_packet_clocks hp.one_le hs
  rw [he,load_one_start_set (hp.odd_of_ne_two hodd)]

end NField.ResetForests.LoadOnePackets

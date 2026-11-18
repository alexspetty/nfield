/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.LoadOneFringe
/-! # Every word, clock and offset in the actual p=127 packet figure -/

noncomputable section
set_option autoImplicit false

namespace NField.ResetForests.LoadOnePackets

open CenteredPhase PhasePopulations LoadedWords CompletePackets

theorem figure127_prime : Nat.Prime 127 := by norm_num

theorem figure127_cutoffs :
    packetLowerCutoff 127=13 ∧ packetUpperCutoff 127=41 ∧
      packetWordCutoff 127 2=25 ∧ packetMaxLoad 127=4 := by
  norm_num [packetLowerCutoff,phaseReturnCutoff,packetUpperCutoff,packetWordCutoff,packetMaxLoad]

theorem figure127_lower_words : lowerWords 127 2={12,14,16,18,20,22,24} := by
  unfold lowerWords
  rw [figure127_cutoffs.1,figure127_cutoffs.2.2.1]
  decide

theorem figure127_upper_words : upperWords 127 2={14,17,20,23} := by
  unfold upperWords
  rw [figure127_cutoffs.1,figure127_cutoffs.2.2.1]
  decide

theorem figure127_complete_starts : completeStarts 127 2={14,17,20} := by
  rw [completeStarts,figure127_upper_words,figure127_cutoffs.2.2.1]
  decide

theorem figure127_offsets :
    packetDelta 127 2 14=0 ∧ packetDelta 127 2 17=1 ∧ packetDelta 127 2 20=0 := by decide

theorem figure127_lower_cells :
    packetLowerWords 127 2 14={14,16} ∧
    packetLowerWords 127 2 17={18} ∧
    packetLowerWords 127 2 20={20,22} := by
  simp only [packetLowerWords,figure127_lower_words]
  decide

/-- Title: `The three displayed p=127 cells are exactly the complete load-two packets`. -/
theorem figure127_packets :
    packetClocks 127 2 14={47,56,55} ∧
    packetClocks 127 2 17={48,54} ∧
    packetClocks 127 2 20={49,53,52} := by
  simp only [packetClocks,figure127_lower_cells.1,figure127_lower_cells.2.1,
    figure127_lower_cells.2.2,Finset.image_insert,Finset.image_singleton]
  decide

theorem figure127_upper_labels :
    ([14,17,20].map (fun s => (s,upperClock 127 2 s)))=[(14,47),(17,48),(20,49)] := by decide

theorem figure127_lower_labels :
    ([14,16,18,20,22].map (fun s => (s,lowerClock 127 2 s)))=
      [(14,56),(16,55),(18,54),(20,53),(22,52)] := by decide

theorem figure127_complete_packet_population :
    loadPackets 127 2={47,48,49,52,53,54,55,56} := by
  rw [loadPackets,figure127_complete_starts]
  simp only [Finset.biUnion_insert,Finset.singleton_biUnion,figure127_packets.1,
    figure127_packets.2.1,figure127_packets.2.2]
  decide

theorem figure127_complete_load_population :
    loadClocks 127 2={47,48,49,50,51,52,53,54,55,56,57} := by
  rw [load_clocks_eq_word_images figure127_prime (by decide),
    figure127_lower_words,figure127_upper_words]
  decide

theorem figure127_complete_fringe : loadFringe 127 2={50,51,57} := by
  rw [loadFringe,figure127_complete_load_population,figure127_complete_packet_population]
  decide

theorem figure127_packet_geometry {s k : ℕ} (hs : s ∈ ({14,17,20} : Finset ℕ))
    (hk : k ∈ packetClocks 127 2 s) : k ∈ retainedClocks 127 ∧ packetLoad 127 k=2 := by
  have hs' : s ∈ completeStarts 127 2 := by rw [figure127_complete_starts]; exact hs
  exact Finset.mem_filter.mp (packet_clock_population (by decide) hs' hk)

theorem figure127_upper_geometry {s : ℕ} (hs : s ∈ ({14,17,20} : Finset ℕ)) :
    upperClock 127 2 s ∈ retainedClocks 127 ∧ packetLoad 127 (upperClock 127 2 s)=2 ∧
      centeredPhase 127 (upperClock 127 2 s)=s ∧ ¬lowerBranch 127 (upperClock 127 2 s) := by
  have hs' : s ∈ completeStarts 127 2 := by rw [figure127_complete_starts]; exact hs
  exact upper_word_spec (by decide) (Finset.mem_filter.mp hs').1

theorem figure127_lower_geometry {v : ℕ} (hv : v ∈ ({14,16,18,20,22} : Finset ℕ)) :
    lowerClock 127 2 v ∈ retainedClocks 127 ∧ packetLoad 127 (lowerClock 127 2 v)=2 ∧
      centeredPhase 127 (lowerClock 127 2 v)=v+1 ∧ lowerBranch 127 (lowerClock 127 2 v) := by
  have hs : ({14,16,18,20,22} : Finset ℕ) ⊆ lowerWords 127 2 := by
    rw [figure127_lower_words]
    decide
  exact lower_word_spec (by decide) (hs hv)

end NField.ResetForests.LoadOnePackets

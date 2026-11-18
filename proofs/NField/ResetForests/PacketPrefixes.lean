/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.PrefixReadout
import NField.ResetForests.PacketReading
/-! # Ordered complete packets and their literal physical prefix rows -/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.PrefixGeometry

open scoped BigOperators Matrix
open CompletePackets PacketQueries

def packetKeys (p : ℕ) (loads : Finset ℕ) : Finset (ℕ ×ₗ ℕ) :=
  loads.biUnion (fun m => (completeStarts p m).image (fun s => toLex (m, s)))

def orderedPackets (p : ℕ) (loads : Finset ℕ) : List (ℕ ×ₗ ℕ) :=
  (packetKeys p loads).sort (· ≤ ·)

def chosenClocks (p : ℕ) (loads : Finset ℕ) : Finset ℕ :=
  (packetKeys p loads).biUnion (fun a => packetClocks p (ofLex a).1 (ofLex a).2)

def prefixClocks (p : ℕ) (loads : Finset ℕ) (n : ℕ) : Finset ℕ :=
  ((orderedPackets p loads).take n).toFinset.biUnion
    (fun a => packetClocks p (ofLex a).1 (ofLex a).2)

def bandLoads (p M : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (LoadedWords.packetMaxLoad p)).filter (fun m => M ≤ m ∧ m < 2 * M)

theorem packet_order_load_then_word (p : ℕ) (loads : Finset ℕ) :
    (orderedPackets p loads).SortedLT := Finset.sortedLT_sort _

theorem packet_order_lex_meaning (a b : ℕ ×ₗ ℕ) :
    a < b ↔ (ofLex a).1 < (ofLex b).1 ∨
      (ofLex a).1 = (ofLex b).1 ∧ (ofLex a).2 < (ofLex b).2 :=
  Prod.Lex.toLex_lt_toLex

theorem chosen_clock_membership (p : ℕ) (loads : Finset ℕ) (k : ℕ) :
    k ∈ chosenClocks p loads ↔ ∃ m ∈ loads, ∃ s ∈ completeStarts p m, k ∈ packetClocks p m s := by
  simp [chosenClocks, packetKeys]
  constructor
  · rintro ⟨m, s, ⟨hm, hs⟩, hk⟩
    exact ⟨m, hm, s, hs, hk⟩
  · rintro ⟨m, hm, s, hs, hk⟩
    exact ⟨m, s, ⟨hm, hs⟩, hk⟩

theorem entire_packet_population (p : ℕ) :
    chosenClocks p (Finset.Icc 1 (LoadedWords.packetMaxLoad p)) = completePackets p := by
  ext k
  simp [chosen_clock_membership, completePackets, loadPackets]

theorem band_packet_population (p M k : ℕ) :
    k ∈ chosenClocks p (bandLoads p M) ↔
      ∃ m ∈ Finset.Icc 1 (LoadedWords.packetMaxLoad p), M ≤ m ∧ m < 2 * M ∧
        ∃ s ∈ completeStarts p m, k ∈ packetClocks p m s := by
  rw [chosen_clock_membership]
  constructor
  · rintro ⟨m, hm, s, hs, hk⟩
    obtain ⟨hm, hlo, hhi⟩ := Finset.mem_filter.mp hm
    exact ⟨m, hm, hlo, hhi, s, hs, hk⟩
  · rintro ⟨m, hm, hlo, hhi, s, hs, hk⟩
    exact ⟨m, Finset.mem_filter.mpr ⟨hm, hlo, hhi⟩, s, hs, hk⟩

theorem prefix_clocks_zero (p : ℕ) (loads : Finset ℕ) : prefixClocks p loads 0 = ∅ := by
  simp [prefixClocks]

theorem prefix_clocks_final (p : ℕ) (loads : Finset ℕ) :
    prefixClocks p loads (orderedPackets p loads).length = chosenClocks p loads := by
  unfold prefixClocks
  rw [List.take_length]
  change ((packetKeys p loads).sort (· ≤ ·)).toFinset.biUnion _ = _
  rw [Finset.sort_toFinset]
  rfl

theorem prefix_clocks_monotone (p : ℕ) (loads : Finset ℕ) : Monotone (prefixClocks p loads) := by
  intro a b hab k hk
  obtain ⟨key, hkey, hk⟩ := Finset.mem_biUnion.mp hk
  apply Finset.mem_biUnion.mpr
  refine ⟨key, ?_, hk⟩
  apply List.mem_toFinset.mpr
  exact (List.take_sublist_take_left hab).subset (List.mem_toFinset.mp hkey)

abbrev PhysicalIndex (p : ℕ) (loads : Finset ℕ) := ↥(chosenClocks p loads) × Bool

def physicalRecord (p : ℕ) (loads : Finset ℕ) : Matrix (PhysicalIndex p loads) (Fin (p - 1)) ℝ :=
  fun i j => if i.2 then detectorRow (p - 1) (p ^ 2) i.1.val j else resetRow (p - 1) i.1.val j

def physicalReadoutWeights (p : ℕ) (loads : Finset ℕ) : PhysicalIndex p loads → ℝ :=
  fun i => if i.2 then 4 * ((p - 1) / i.1.val : ℕ) else 0

def physicalPrefixes (p : ℕ) (loads : Finset ℕ) (cuts : ℕ → ℕ) (r : ℕ) :
    Finset (PhysicalIndex p loads) :=
  Finset.univ.filter (fun i => i.1.val ∈ prefixClocks p loads (cuts r))

theorem physical_prefix_zero (p : ℕ) (loads : Finset ℕ) (cuts : ℕ → ℕ) (h0 : cuts 0 = 0) :
    physicalPrefixes p loads cuts 0 = ∅ := by
  simp [physicalPrefixes, h0, prefix_clocks_zero]

theorem physical_prefix_final (p : ℕ) (loads : Finset ℕ) (cuts : ℕ → ℕ) (L : ℕ)
    (hL : cuts L = (orderedPackets p loads).length) :
    physicalPrefixes p loads cuts L = Finset.univ := by
  ext i
  simp only [physicalPrefixes, Finset.mem_filter, Finset.mem_univ, true_and, hL,
    prefix_clocks_final]
  exact iff_true_intro i.1.property

theorem physical_prefix_monotone (p : ℕ) (loads : Finset ℕ) (cuts : ℕ → ℕ)
    (hc : Monotone cuts) : Monotone (physicalPrefixes p loads cuts) := by
  intro a b hab i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    prefix_clocks_monotone p loads (hc hab) (Finset.mem_filter.mp hi).2⟩

theorem physical_linear_readout (p : ℕ) (loads : Finset ℕ) (c : Fin (p - 1) → ℝ) :
    finalReadout (physicalRecord p loads) (physicalReadoutWeights p loads) c =
      ∑ k ∈ chosenClocks p loads,
        4 * ((p - 1) / k : ℕ) * (detectorRow (p - 1) (p ^ 2) k ⬝ᵥ c) := by
  change (∑ i : PhysicalIndex p loads, physicalReadoutWeights p loads i *
    (physicalRecord p loads *ᵥ c) i) = _
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, physicalReadoutWeights,
    physicalRecord, Matrix.mulVec, Bool.false_eq_true, if_false, if_true, zero_mul, add_zero]
  simpa only using (Finset.sum_coe_sort (chosenClocks p loads)
    (fun k : ℕ => 4 * ((p - 1) / k : ℕ) * (detectorRow (p - 1) (p ^ 2) k ⬝ᵥ c)))

end NField.ResetForests.PrefixGeometry

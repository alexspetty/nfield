/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.SourceEnergy
import NField.ResetForests.DyadicPrefixes
/-! # Fixed physical partitions and the complete native packet readout -/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.CostCriteria

open scoped BigOperators Matrix
open SourceMetrics GramDecomposition CompletePackets PacketQueries RecordGeometry PrefixGeometry
open NField.Alignment CommonResetGram CollisionRampEnergy

structure PacketPartition (p : ℕ) (loads : Finset ℕ) where
  cuts : ℕ → ℕ
  monotone_cuts : Monotone cuts
  initial : cuts 0 = 0
  blocks : ℕ
  terminal : cuts blocks = (orderedPackets p loads).length

def dyadicPartition (p : ℕ) (loads : Finset ℕ) : PacketPartition p loads where
  cuts := dyadicCuts (orderedPackets p loads).length
  monotone_cuts := dyadic_cuts_monotone _
  initial := dyadic_cuts_zero _
  blocks := (orderedPackets p loads).length + 1
  terminal := dyadic_cuts_final _

def entireLoads (p : ℕ) : Finset ℕ := Finset.Icc 1 (LoadedWords.packetMaxLoad p)

def packetReadout (p : ℕ) (loads : Finset ℕ) : ℝ :=
  finalReadout (physicalRecord p loads) (physicalReadoutWeights p loads) (fun _ => 1)

def packetCost (p : OddPrime) (loads : Finset ℕ) (σ : PacketPartition p.val loads) : ℝ :=
  prefixCost (sampledGram (p.val - 1) (p.val ^ 2))
    (both_prime_square_grams_posDef p.property.1 p.property.2).2
    (physicalRecord p.val loads) (physicalReadoutWeights p.val loads)
    (physicalPrefixes p.val loads σ.cuts) (fun _ => 1) σ.blocks

theorem packet_cost_nonnegative (p : OddPrime) (loads : Finset ℕ) (σ : PacketPartition p.val loads) :
    0 ≤ packetCost p loads σ := by
  unfold packetCost prefixCost
  apply Core.readout_cost_nonneg
  intro r _
  exact source_work_nonnegative _ (both_prime_square_grams_posDef p.property.1 p.property.2).2 _

theorem packet_readout_energy_cost_bound (p : OddPrime) (loads : Finset ℕ)
    (σ : PacketPartition p.val loads) :
    |packetReadout p.val loads| ^ 2 ≤ sourceEnergy p.val * packetCost p loads σ := by
  have hb := prefix_signed_bound (sampledGram (p.val - 1) (p.val ^ 2))
    (both_prime_square_grams_posDef p.property.1 p.property.2).2
    (physicalRecord p.val loads) (physicalReadoutWeights p.val loads)
    (physicalPrefixes p.val loads σ.cuts) (physical_prefix_monotone _ _ _ σ.monotone_cuts)
    (physical_prefix_zero _ _ _ σ.initial) (fun _ => 1) σ.blocks
    (physical_prefix_final _ _ _ _ σ.terminal)
  exact hb.1.trans hb.2

theorem coherent_detector_reading (N Q k : ℕ) :
    detectorRow N Q k ⬝ᵥ (fun _ => 1) =
      ∑ a ∈ (Finset.Ico 1 k).filter (fun a => a.Coprime k),
        boundaryResponse N ((a : ℝ) / (k : ℝ)) * midpointRow Q ((a : ℝ) / (k : ℝ)) := by
  simpa only [cutoff_complete_profile, unit_weights, BranchTransport.unitAddresses] using
    detector_row_reading N Q k (fun _ => 1)

theorem packet_readout_native (p : ℕ) (loads : Finset ℕ) :
    packetReadout p loads = ∑ k ∈ chosenClocks p loads, 4 * Core.clockReading (p - 1) (p ^ 2) k := by
  rw [packetReadout, physical_linear_readout]
  apply Finset.sum_congr rfl
  intro k _
  rw [coherent_detector_reading]
  exact mul_assoc _ _ _

theorem entire_readout_packet_sum (p : ℕ) :
    packetReadout p (entireLoads p) = packetSignedSum p := by
  rw [packet_readout_native, entireLoads, entire_packet_population, complete_packets_sum]
  rfl

def loadWork (p m : ℕ) : ℝ := ∑ k ∈ loadPackets p m, 4 * Core.clockReading (p - 1) (p ^ 2) k

theorem chosen_clocks_load_union (p : ℕ) (loads : Finset ℕ) :
    chosenClocks p loads = loads.biUnion (loadPackets p) := by
  ext k
  simp only [chosen_clock_membership, Finset.mem_biUnion, loadPackets]

theorem packet_readout_load_sum (p : ℕ) (loads : Finset ℕ)
    (hpos : ∀ m ∈ loads, 0 < m) : packetReadout p loads = ∑ m ∈ loads, loadWork p m := by
  rw [packet_readout_native, chosen_clocks_load_union]
  exact Finset.sum_biUnion (fun m hm n hn hmn => load_packets_disjoint p (hpos m hm) (hpos n hn) hmn)

end NField.ResetForests.CostCriteria

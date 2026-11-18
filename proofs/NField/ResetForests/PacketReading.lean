/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.PacketFringeWork
/-! # Exact complete packet sums and their normalized fringe allowance -/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.CompletePackets

open scoped BigOperators
open CenteredPhase PhasePopulations LoadedWords NField.Alignment

def packetSignedSum (p : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 (packetMaxLoad p), ∑ s ∈ completeStarts p m,
    ∑ k ∈ packetClocks p m s, 4 * Core.clockReading (p - 1) (p ^ 2) k

theorem load_packets_subset {p m : ℕ} (hm : 0 < m) : loadPackets p m ⊆ loadClocks p m := by
  intro k hk
  obtain ⟨s, hs, hks⟩ := Finset.mem_biUnion.mp hk
  exact packet_clock_population hm hs hks

theorem complete_packets_subset (p : ℕ) : completePackets p ⊆ retainedClocks p := by
  intro k hk
  obtain ⟨m, hm, hkm⟩ := Finset.mem_biUnion.mp hk
  exact (Finset.mem_filter.mp (load_packets_subset (Finset.mem_Icc.mp hm).1 hkm)).1

theorem load_packets_disjoint (p : ℕ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hmn : m ≠ n) : Disjoint (loadPackets p m) (loadPackets p n) :=
  (distinct_loads_disjoint p hmn).mono (load_packets_subset hm) (load_packets_subset hn)

theorem load_packets_sum {p m : ℕ} (hm : 0 < m) (q : ℕ → ℝ) :
    (∑ k ∈ loadPackets p m, q k) =
      ∑ s ∈ completeStarts p m, ∑ k ∈ packetClocks p m s, q k := by
  apply Finset.sum_biUnion
  intro s hs t ht hst
  exact same_load_packets_disjoint hm hs ht hst

theorem complete_packets_sum (p : ℕ) (q : ℕ → ℝ) :
    (∑ k ∈ completePackets p, q k) =
      ∑ m ∈ Finset.Icc 1 (packetMaxLoad p), ∑ s ∈ completeStarts p m,
        ∑ k ∈ packetClocks p m s, q k := by
  unfold completePackets
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro m hm
    exact load_packets_sum (Finset.mem_Icc.mp hm).1 q
  · intro m hm n hn hmn
    exact load_packets_disjoint p (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hn).1 hmn

theorem packet_interior_partition (p : ℕ) :
    (∑ k ∈ retainedClocks p, 4 * Core.clockReading (p - 1) (p ^ 2) k) =
      packetSignedSum p + ∑ k ∈ packetFringe p, 4 * Core.clockReading (p - 1) (p ^ 2) k := by
  have hs := Finset.sum_sdiff (f := fun k => 4 * Core.clockReading (p - 1) (p ^ 2) k)
    (complete_packets_subset p)
  rw [complete_packets_sum] at hs
  change _ + packetSignedSum p = _ at hs
  unfold packetFringe
  linarith

theorem packet_fringe_signed_abs (p : ℕ) :
    |∑ k ∈ packetFringe p, 4 * Core.clockReading (p - 1) (p ^ 2) k| ≤ packetFringeWork p :=
  Finset.abs_sum_le_sum_abs _ _

theorem packet_fringe_normalized_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime →
      |(1 / (p : ℝ) ^ 2) *
        (∑ k ∈ packetFringe p, 4 * Core.clockReading (p - 1) (p ^ 2) k)| ≤
          C * (p : ℝ) ^ (-1 / 2 + ε) := by
  obtain ⟨C, hC, hc⟩ := packet_fringe_small_power ε hε
  refine ⟨C, hC, ?_⟩
  intro p hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [show (1 / (p : ℝ) ^ 2) *
      (∑ k ∈ packetFringe p, 4 * Core.clockReading (p - 1) (p ^ 2) k) =
        (∑ k ∈ packetFringe p, 4 * Core.clockReading (p - 1) (p ^ 2) k) / (p : ℝ) ^ 2 by ring,
    abs_div, abs_of_nonneg (sq_nonneg (p : ℝ))]
  calc
    _ ≤ packetFringeWork p / (p : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (packet_fringe_signed_abs p) (sq_nonneg _)
    _ ≤ (C * (p : ℝ) ^ (3 / 2 + ε)) / (p : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (hc p hp) (sq_nonneg _)
    _ = _ := by
      rw [mul_div_assoc, ← Real.rpow_two, ← Real.rpow_sub hpR]
      congr 2
      ring

theorem complete_packet_reading_half_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime → p ≠ 2 →
      |CommonResetSampling.defect (p - 1) (p ^ 2) - 1 -
        (1 / (p : ℝ) ^ 2) * packetSignedSum p| ≤ C * (p : ℝ) ^ (-1 / 2 + ε) := by
  obtain ⟨C, hC, hc⟩ := complete_clock_interior_half_power ε hε
  obtain ⟨D, hD, hd⟩ := packet_fringe_normalized_small_power ε hε
  refine ⟨C + D, by positivity, ?_⟩
  intro p hp hodd
  have hsplit := packet_interior_partition p
  have he : CommonResetSampling.defect (p - 1) (p ^ 2) - 1 -
      (1 / (p : ℝ) ^ 2) * packetSignedSum p =
      (CommonResetSampling.defect (p - 1) (p ^ 2) - 1 -
        (1 / (p : ℝ) ^ 2) *
          (∑ k ∈ retainedClocks p, 4 * Core.clockReading (p - 1) (p ^ 2) k)) +
        (1 / (p : ℝ) ^ 2) *
          (∑ k ∈ packetFringe p, 4 * Core.clockReading (p - 1) (p ^ 2) k) := by
    rw [hsplit]
    ring
  rw [he]
  calc
    _ ≤ |CommonResetSampling.defect (p - 1) (p ^ 2) - 1 -
        (1 / (p : ℝ) ^ 2) *
          (∑ k ∈ retainedClocks p, 4 * Core.clockReading (p - 1) (p ^ 2) k)| +
        |(1 / (p : ℝ) ^ 2) *
          (∑ k ∈ packetFringe p, 4 * Core.clockReading (p - 1) (p ^ 2) k)| := abs_add_le _ _
    _ ≤ C * (p : ℝ) ^ (-1 / 2 + ε) + D * (p : ℝ) ^ (-1 / 2 + ε) :=
      add_le_add (hc p hp hodd) (hd p hp)
    _ = _ := by ring

end NField.ResetForests.CompletePackets

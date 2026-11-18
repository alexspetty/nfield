/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.BandCriterion
/-! # A local sufficient estimate for fixed dyadic physical prefix cuts -/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.RefinedBounds

open scoped BigOperators Topology Matrix
open Filter
open NField.Alignment CommonResetGram
open CenteredPhase PhasePopulations SourceMetrics LoadedWords CompletePackets RecordGeometry PrefixGeometry CostCriteria

theorem packet_key_membership (p : ℕ) (loads : Finset ℕ) (a : ℕ ×ₗ ℕ) :
    a ∈ packetKeys p loads ↔ (ofLex a).1 ∈ loads ∧ (ofLex a).2 ∈ completeStarts p (ofLex a).1 := by
  simp only [packetKeys, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨m, hm, s, hs, rfl⟩
    exact ⟨hm, hs⟩
  · rintro ⟨hm, hs⟩
    exact ⟨(ofLex a).1, hm, (ofLex a).2, hs, rfl⟩

theorem ordered_packet_count_le {p : ℕ} (loads : Finset ℕ)
    (hpos : ∀ m ∈ loads, 0 < m) : (orderedPackets p loads).length ≤ p := by
  rw [orderedPackets, Finset.length_sort]
  let f : (ℕ ×ₗ ℕ) → ℕ := fun a => upperClock p (ofLex a).1 (ofLex a).2
  have hmap : Set.MapsTo f (packetKeys p loads) (Finset.range p) := by
    intro a ha
    obtain ⟨hm, hs⟩ := (packet_key_membership p loads a).mp ha
    have hk := (upper_word_spec (hpos _ hm) (Finset.mem_filter.mp hs).1).1
    exact Finset.mem_range.mpr (retained_clock_bounds hk).2.1
  have hinj : Set.InjOn f (packetKeys p loads) := by
    intro a ha b hb he
    obtain ⟨ham, has⟩ := (packet_key_membership p loads a).mp ha
    obtain ⟨hbm, hbs⟩ := (packet_key_membership p loads b).mp hb
    have hA := upper_word_spec (hpos _ ham) (Finset.mem_filter.mp has).1
    have hB := upper_word_spec (hpos _ hbm) (Finset.mem_filter.mp hbs).1
    have hm : (ofLex a).1 = (ofLex b).1 := by
      change upperClock p (ofLex a).1 (ofLex a).2 = upperClock p (ofLex b).1 (ofLex b).2 at he
      exact hA.2.1.symm.trans ((congrArg (packetLoad p) he).trans hB.2.1)
    have hs : (ofLex a).2 = (ofLex b).2 := by
      change upperClock p (ofLex a).1 (ofLex a).2 = upperClock p (ofLex b).1 (ofLex b).2 at he
      exact hA.2.2.1.symm.trans ((congrArg (centeredPhase p) he).trans hB.2.2.1)
    exact congrArg toLex (Prod.ext hm hs)
  simpa only [Finset.card_range] using Finset.card_le_card_of_injOn f hmap hinj

def dyadicBlocks (K : ℕ) : ℕ := Nat.log 2 K + 2

theorem compact_dyadic_final (K : ℕ) : dyadicCuts K (dyadicBlocks K) = K := by
  have hK : K ≤ 2 ^ (Nat.log 2 K + 1) :=
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) K).le
  simp only [dyadicCuts, dyadicBlocks, show Nat.log 2 K + 2 ≠ 0 by omega, if_false,
    show Nat.log 2 K + 2 - 1 = Nat.log 2 K + 1 by omega, min_eq_left hK]

def compactDyadicPartition (p : ℕ) (loads : Finset ℕ) : PacketPartition p loads where
  cuts := dyadicCuts (orderedPackets p loads).length
  monotone_cuts := dyadic_cuts_monotone _
  initial := dyadic_cuts_zero _
  blocks := dyadicBlocks (orderedPackets p loads).length
  terminal := compact_dyadic_final _

theorem compact_dyadic_block_bound {p : ℕ} (loads : Finset ℕ)
    (hpos : ∀ m ∈ loads, 0 < m) :
    (compactDyadicPartition p loads).blocks ≤ bandCount p + 1 := by
  have h := Nat.log_mono_right (ordered_packet_count_le (p := p) loads hpos) (b := 2)
  change Nat.log 2 (orderedPackets p loads).length + 2 ≤ Nat.log 2 p + 1 + 1
  omega

theorem compact_dyadic_blocks_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : OddPrime) (loads : Finset ℕ),
      (∀ m ∈ loads, 0 < m) →
      ((compactDyadicPartition p.val loads).blocks : ℝ) ≤ C * primePower ε p := by
  obtain ⟨C, hC, h⟩ := band_count_small_power ε hε
  refine ⟨C + 1, by positivity, ?_⟩
  intro p loads hpos
  have hb : ((compactDyadicPartition p.val loads).blocks : ℝ) ≤ (bandCount p.val : ℝ) + 1 := by
    exact_mod_cast compact_dyadic_block_bound loads hpos
  have hone : 1 ≤ primePower ε p := Real.one_le_rpow (by exact_mod_cast p.property.1.one_le) hε.le
  calc
    _ ≤ (bandCount p.val : ℝ) + 1 := hb
    _ ≤ C * primePower ε p + primePower ε p := add_le_add (h p.val p.property.1.one_le) hone
    _ = _ := by ring

def packetIncrement (p : OddPrime) (loads : Finset ℕ)
    (σ : PacketPartition p.val loads) (r : ℕ) : Fin (p.val - 1) → ℝ :=
  prefixIncrement (sampledGram (p.val - 1) (p.val ^ 2))
    (both_prime_square_grams_posDef p.property.1 p.property.2).2
    (physicalRecord p.val loads) (physicalPrefixes p.val loads σ.cuts) (fun _ => 1) r

def packetIncrementEnergy (p : OddPrime) (loads : Finset ℕ)
    (σ : PacketPartition p.val loads) (r : ℕ) : ℝ :=
  sourceWork (sampledGram (p.val - 1) (p.val ^ 2))
    (packetIncrement p loads σ r) (packetIncrement p loads σ r)

def packetIncrementReading (p : OddPrime) (loads : Finset ℕ)
    (σ : PacketPartition p.val loads) (r : ℕ) : ℝ :=
  finalReadout (physicalRecord p.val loads) (physicalReadoutWeights p.val loads)
    (packetIncrement p loads σ r)

theorem packet_cost_local_sum (p : OddPrime) (loads : Finset ℕ)
    (σ : PacketPartition p.val loads) :
    packetCost p loads σ = ∑ r ∈ Finset.range σ.blocks,
      packetIncrementReading p loads σ r ^ 2 / packetIncrementEnergy p loads σ r := rfl

theorem packet_increment_energy_nonnegative (p : OddPrime) (loads : Finset ℕ)
    (σ : PacketPartition p.val loads) (r : ℕ) : 0 ≤ packetIncrementEnergy p loads σ r :=
  source_work_nonnegative _ (both_prime_square_grams_posDef p.property.1 p.property.2).2 _

theorem packet_cost_le_local_bound (p : OddPrime) (loads : Finset ℕ)
    (σ : PacketPartition p.val loads) {B : ℝ} (hB : 0 ≤ B)
    (hlocal : ∀ r ∈ Finset.range σ.blocks,
      packetIncrementReading p loads σ r ^ 2 ≤ B * packetIncrementEnergy p loads σ r) :
    packetCost p loads σ ≤ (σ.blocks : ℝ) * B := by
  rw [packet_cost_local_sum]
  calc
    _ ≤ ∑ _r ∈ Finset.range σ.blocks, B := by
      apply Finset.sum_le_sum
      intro r hr
      by_cases he : packetIncrementEnergy p loads σ r = 0
      · simpa only [he, div_zero] using hB
      · have hepos := lt_of_le_of_ne (packet_increment_energy_nonnegative p loads σ r) (Ne.symm he)
        exact (div_le_iff₀ hepos).mpr (hlocal r hr)
    _ = _ := by simp

def DyadicLocalSubpower : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ p : OddPrime,
    ∀ r ∈ Finset.range (compactDyadicPartition p.val (entireLoads p.val)).blocks,
      packetIncrementReading p (entireLoads p.val) (compactDyadicPartition p.val (entireLoads p.val)) r ^ 2 ≤
        (C * primePower ε p) *
          packetIncrementEnergy p (entireLoads p.val) (compactDyadicPartition p.val (entireLoads p.val)) r

theorem dyadic_local_cost_subpower (hlocal : DyadicLocalSubpower) :
    EntireCostSubpower (fun p => compactDyadicPartition p.val (entireLoads p.val)) := by
  intro ε hε
  obtain ⟨C, hC, hc⟩ := hlocal (ε / 2) (by positivity)
  obtain ⟨B, hB, hb⟩ := compact_dyadic_blocks_subpower (ε / 2) (by positivity)
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨B * C, Eventually.of_forall ?_⟩
  intro p
  rw [Real.norm_of_nonneg (packet_cost_nonnegative p _ _),
    Real.norm_of_nonneg (show 0 ≤ primePower ε p from Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  have hpow : 0 ≤ C * primePower (ε / 2) p := mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hpos : ∀ m ∈ entireLoads p.val, 0 < m := fun m hm => (Finset.mem_Icc.mp hm).1
  calc
    _ ≤ ((compactDyadicPartition p.val (entireLoads p.val)).blocks : ℝ) * (C * primePower (ε / 2) p) :=
      packet_cost_le_local_bound p _ _ hpow (hc p)
    _ ≤ (B * primePower (ε / 2) p) * (C * primePower (ε / 2) p) :=
      mul_le_mul_of_nonneg_right (hb p _ hpos) hpow
    _ = (B * C) * (primePower (ε / 2) p * primePower (ε / 2) p) := by ring
    _ = _ := by
      unfold primePower
      rw [← Real.rpow_add (by exact_mod_cast p.property.1.pos), add_halves]

theorem dyadic_local_half_power_criterion (hlocal : DyadicLocalSubpower) : HalfPowerConclusion :=
  entire_packet_half_power_criterion _ (dyadic_local_cost_subpower hlocal)

theorem one_final_prefix_cost {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (b : ι → ℝ) (J : ℕ → Finset ι)
    (h0 : J 0 = ∅) (h1 : J 1 = Finset.univ) (c : Fin N → ℝ) :
    prefixCost G hG A b J c 1 =
      (finalReadout A b c) ^ 2 /
        sourceWork G (prefixSource G hG A J c 1) (prefixSource G hG A J c 1) := by
  have hd : finalReadout A b c = finalReadout A b (prefixSource G hG A J c 1) := by
    have h := prefix_readout_sum G hG A b J h0 c 1 h1
    simpa only [Finset.sum_range_one, prefixIncrement, zero_add,
      prefix_zero G hG A J h0 c, sub_zero] using h
  simp only [prefixCost, Core.readoutCost, Finset.sum_range_one, prefixIncrement, zero_add,
    prefix_zero G hG A J h0 c, sub_zero, ← hd]

end NField.ResetForests.RefinedBounds

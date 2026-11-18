/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.SeedWork
/-! # Exact seed rank, inertia, entering readings and retained source work -/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.SeedRecord

open scoped BigOperators Matrix
open PacketQueries RecordGeometry

def seedJointRecord := Matrix.fromRows seedPacketRecord seedFringeRecord
def seedMetric : Matrix (Fin 30) (Fin 30) ℝ := SourceMetrics.sampledGram 30 961

theorem seed_metric_posDef : seedMetric.PosDef :=
  (SourceMetrics.both_prime_square_grams_posDef (p := 31) (by decide) (by decide)).2

def seedEnteringRecord : Matrix (RecordIndex 2) (Fin 30) ℝ :=
  enteringRecord seedMetric seed_metric_posDef seedPacketRecord seedFringeRecord

theorem seed_packet_row (i : Fin 3) (b : Bool) :
    seedPacketRecord (i, b) = seedRecord (⟨i.val, by omega⟩, b) := by
  fin_cases i <;> cases b <;> rfl

theorem seed_fringe_row (i : Fin 2) (b : Bool) :
    seedFringeRecord (i, b) = seedRecord (⟨i.val + 3, by omega⟩, b) := by
  fin_cases i <;> cases b <;> rfl

theorem seed_packet_reading (c : Fin 30 → ℝ) (i : Fin 3) (b : Bool) :
    (seedPacketRecord *ᵥ c) (i, b) = (seedRecord *ᵥ c) (⟨i.val, by omega⟩, b) := by
  change seedPacketRecord (i, b) ⬝ᵥ c = seedRecord (⟨i.val, by omega⟩, b) ⬝ᵥ c
  rw [seed_packet_row]

theorem seed_fringe_reading (c : Fin 30 → ℝ) (i : Fin 2) (b : Bool) :
    (seedFringeRecord *ᵥ c) (i, b) = (seedRecord *ᵥ c) (⟨i.val + 3, by omega⟩, b) := by
  change seedFringeRecord (i, b) ⬝ᵥ c = seedRecord (⟨i.val + 3, by omega⟩, b) ⬝ᵥ c
  rw [seed_fringe_row]

theorem seed_joint_surjective : Function.Surjective seedJointRecord.mulVec := by
  intro w
  let y : RecordIndex 5 → ℝ := fun i =>
    if h : i.1.val < 3 then w (Sum.inl (⟨i.1.val, h⟩, i.2))
    else w (Sum.inr (⟨i.1.val - 3, by have := i.1.isLt; omega⟩, i.2))
  obtain ⟨c, hc⟩ := seed_record_surjective y
  refine ⟨c, ?_⟩
  ext i
  rcases i with ⟨i, b⟩ | ⟨i, b⟩
  · change (seedPacketRecord *ᵥ c) (i, b) = w (Sum.inl (i, b))
    rw [seed_packet_reading]
    have he := congrFun hc (⟨i.val, by omega⟩, b)
    simpa only [y, dif_pos i.isLt] using he
  · change (seedFringeRecord *ᵥ c) (i, b) = w (Sum.inr (i, b))
    rw [seed_fringe_reading]
    have he := congrFun hc (⟨i.val + 3, by omega⟩, b)
    simpa only [y, dif_neg (by omega : ¬i.val + 3 < 3), Nat.add_sub_cancel] using he

theorem seed_joint_rank : seedJointRecord.rank = 10 := by
  have hs : Function.Surjective seedJointRecord.mulVecLin := seed_joint_surjective
  unfold Matrix.rank
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, Module.finrank_pi,
    Fintype.card_sum, record_index_card, record_index_card]

theorem seed_entering_rank : seedEnteringRecord.rank = 4 := by
  rw [seedEnteringRecord, entering_record_rank_increase]
  change seedJointRecord.rank - seedPacketRecord.rank = 4
  rw [seed_joint_rank, seed_packet_record_rank]

theorem seed_entering_surjective : Function.Surjective seedEnteringRecord.mulVec :=
  full_row_rank_surjective seedEnteringRecord seed_entering_rank

theorem seed_complete_query_rank_signature :
    (pullbackQuery seedRecord).rank = 10 ∧
      sigPos (matrixForm (pullbackQuery seedRecord)) = 5 ∧
      sigNeg (matrixForm (pullbackQuery seedRecord)) = 5 :=
  complete_packet_record_rank_signature 30 961 seedClocks seed_record_rank

theorem seed_packet_query_rank_signature :
    (pullbackQuery seedPacketRecord).rank = 6 ∧
      sigPos (matrixForm (pullbackQuery seedPacketRecord)) = 3 ∧
      sigNeg (matrixForm (pullbackQuery seedPacketRecord)) = 3 :=
  complete_packet_record_rank_signature 30 961 packetClocks seed_packet_record_rank

theorem seed_minimum_record_dimension {d : ℕ} (T : Matrix (Fin d) (Fin 30) ℝ)
    (f : (Fin d → ℝ) → ℝ)
    (hf : ∀ c, packetQuery 30 961 seedClocks c = f (T *ᵥ c)) : 10 ≤ d :=
  complete_packet_record_minimal 30 961 seedClocks seed_record_rank T f hf

theorem seed_ten_actual_readings : Fintype.card (RecordIndex 5) = 10 := record_index_card 5

theorem seed_record_kernel_dimension : Module.finrank ℝ (LinearMap.ker seedRecord.mulVecLin) = 20 := by
  have hd := LinearMap.finrank_range_add_finrank_ker seedRecord.mulVecLin
  change seedRecord.rank + _ = _ at hd
  rw [seed_record_rank, Module.finrank_pi, Fintype.card_fin] at hd
  omega

theorem seed_joint_kernel_dimension : Module.finrank ℝ (LinearMap.ker seedJointRecord.mulVecLin) = 20 := by
  have hd := LinearMap.finrank_range_add_finrank_ker seedJointRecord.mulVecLin
  change seedJointRecord.rank + _ = _ at hd
  rw [seed_joint_rank, Module.finrank_pi, Fintype.card_fin] at hd
  omega

theorem seed_full_source_energy (c : Fin 30 → ℝ) :
    sourceWork seedMetric c c =
      (seedPacketRecord *ᵥ c) ⬝ᵥ (recordInverse seedMetric seed_metric_posDef seedPacketRecord *ᵥ (seedPacketRecord *ᵥ c)) +
      (seedEnteringRecord *ᵥ c) ⬝ᵥ (recordInverse seedMetric seed_metric_posDef seedEnteringRecord *ᵥ (seedEnteringRecord *ᵥ c)) +
      sourceWork seedMetric (residualSource seedMetric seed_metric_posDef seedPacketRecord seedFringeRecord c)
        (residualSource seedMetric seed_metric_posDef seedPacketRecord seedFringeRecord c) :=
  complete_record_energy seedMetric seed_metric_posDef seedPacketRecord seedFringeRecord c

theorem seed_complete_interior_population : PhasePopulations.retainedClocks 31 = {19, 20, 22, 23, 24} := by
  have hsub : ({19, 20, 22, 23, 24} : Finset ℕ) ⊆ Finset.Icc 2 30 := by decide
  ext k
  by_cases hk : k ∈ Finset.Icc 2 30
  · obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hk
    interval_cases k <;>
      norm_num [PhasePopulations.retainedClocks, PhasePopulations.retainedPhase, PhasePopulations.phaseReturnCutoff,
        CenteredPhase.centeredPhase]
  · have ho : k ∉ ({19, 20, 22, 23, 24} : Finset ℕ) := fun h => hk (hsub h)
    simp only [PhasePopulations.retainedClocks, Nat.reduceSub, Finset.mem_filter, hk, false_and, ho]

theorem seed_actual_complete_packet : CompletePackets.completePackets 31 = {19, 22, 23} := by
  norm_num [CompletePackets.completePackets, CompletePackets.loadPackets, CompletePackets.completeStarts,
    CompletePackets.packetClocks, CompletePackets.packetLowerWords, LoadedWords.packetMaxLoad,
    LoadedWords.packetLowerCutoff, PhasePopulations.phaseReturnCutoff, LoadedWords.packetWordCutoff,
    LoadedWords.packetUpperCutoff, LoadedWords.upperWords, LoadedWords.lowerWords,
    LoadedWords.lowerClock, LoadedWords.upperClock,
    show Finset.Icc 1 2 = {1, 2} from by decide,
    show Finset.Icc 7 9 = {7, 8, 9} from by decide,
    show Finset.Icc 6 8 = {6, 7, 8} from by decide,
    show Finset.Icc 7 6 = (∅ : Finset ℕ) from by decide]
  norm_num [Finset.filter_insert, Finset.filter_singleton, Finset.biUnion_insert,
    Finset.biUnion_singleton, CompletePackets.packetClocks,
    CompletePackets.packetLowerWords, LoadedWords.lowerWords, LoadedWords.packetLowerCutoff,
    PhasePopulations.phaseReturnCutoff, LoadedWords.packetWordCutoff, LoadedWords.packetUpperCutoff,
    LoadedWords.lowerClock, LoadedWords.upperClock,
    show Finset.Icc 6 8 = {6, 7, 8} from by decide]
  decide

theorem seed_actual_fringe : CompletePackets.packetFringe 31 = {20, 24} := by
  rw [CompletePackets.packetFringe, seed_complete_interior_population, seed_actual_complete_packet]
  decide

theorem seed_clocks_match_interior : Finset.univ.image seedClocks = PhasePopulations.retainedClocks 31 := by
  rw [seed_complete_interior_population]
  decide

theorem seed_packet_clocks_match : Finset.univ.image packetClocks = CompletePackets.completePackets 31 := by
  rw [seed_actual_complete_packet]
  decide

theorem seed_fringe_clocks_match : Finset.univ.image fringeClocks = CompletePackets.packetFringe 31 := by
  rw [seed_actual_fringe]
  decide

theorem coherent_clock_native (N Q k : ℕ) :
    QuadraticResponse.coherentClockContribution N Q k = 4 * Core.clockReading N Q k := by
  simp only [QuadraticResponse.coherentClockContribution, Core.clockReading, NField.Alignment.CommonResetGram.unit_weights]
  exact mul_assoc _ _ _

theorem native_clock_rational (N Q : ℕ) {k : ℕ} (hk : 0 < k) :
    4 * Core.clockReading N Q k = (rationalShortClock N Q k : ℝ) := by
  rw [← coherent_clock_native, coherent_clock_rational N Q hk]

theorem seed_native_packet_work :
    (∑ k ∈ CompletePackets.completePackets 31, 4 * Core.clockReading 30 961 k) = (-3248/209 : ℝ) := by
  rw [seed_actual_complete_packet]
  norm_num [native_clock_rational 30 961 (by norm_num : 0 < 19),
    native_clock_rational 30 961 (by norm_num : 0 < 22),
    native_clock_rational 30 961 (by norm_num : 0 < 23),
    seed_clock19_work, seed_clock22_work, seed_clock23_work]

theorem seed_native_fringe_work :
    (∑ k ∈ CompletePackets.packetFringe 31, 4 * Core.clockReading 30 961 k) = (601/15 : ℝ) := by
  rw [seed_actual_fringe]
  norm_num [native_clock_rational 30 961 (by norm_num : 0 < 20),
    native_clock_rational 30 961 (by norm_num : 0 < 24), seed_clock20_work, seed_clock24_work]

theorem seed_native_interior_work :
    (∑ k ∈ PhasePopulations.retainedClocks 31, 4 * Core.clockReading 30 961 k) = (76889/3135 : ℝ) := by
  rw [seed_complete_interior_population]
  norm_num [native_clock_rational 30 961 (by norm_num : 0 < 19),
    native_clock_rational 30 961 (by norm_num : 0 < 20),
    native_clock_rational 30 961 (by norm_num : 0 < 22),
    native_clock_rational 30 961 (by norm_num : 0 < 23),
    native_clock_rational 30 961 (by norm_num : 0 < 24),
    seed_clock19_work, seed_clock20_work, seed_clock22_work, seed_clock23_work, seed_clock24_work]

end NField.ResetForests.SeedRecord

/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.SeedRank
/-! # Coherent seed work on the original complete thirty-source field -/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.SeedRecord

open scoped BigOperators Matrix
open NField.Alignment CommonResetGrid CommonResetGram CommonResetSampling CommonResetWeightedSources CommonResetAllGrids
open CarrierJumpData DedekindReciprocity SourceMetrics GramDecomposition QuadraticResponse PacketQueries

def rationalShortClock (N Q k : ℕ) : ℚ :=
  4 * (N / k : ℕ) * ∑ a ∈ BranchTransport.unitAddresses k,
    cyclicPrefixResponse a k (N % k) * rationalSawtooth (Q * a) k

theorem coherent_clock_rational (N Q : ℕ) {k : ℕ} (hk : 0 < k) :
    coherentClockContribution N Q k = (rationalShortClock N Q k : ℝ) := by
  unfold coherentClockContribution rationalShortClock
  push_cast
  apply congrArg (fun z : ℝ => 4 * ((N / k : ℕ) : ℝ) * z)
  apply Finset.sum_congr rfl
  intro a ha
  rw [unit_weights, boundaryResponse_reduced_prefix hk (Finset.mem_filter.mp ha).2,
    midpointRow_rational hk]

theorem coherent_packet_clock_sum {t : ℕ} (N Q : ℕ) (κ : Fin t → ℕ) :
    packetQuery N Q κ (fun _ => 1) = ∑ i : Fin t, coherentClockContribution N Q (κ i) := by
  simp only [packetQuery, cutoff_reset_weight_coherent, cutoff_complete_profile,
    coherentClockContribution, BranchTransport.unitAddresses]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (mul_assoc _ _ _).symm

theorem seed_clock23_work : rationalShortClock 30 961 23 = (-12 : ℚ) := by
  norm_num [rationalShortClock, BranchTransport.unitAddresses, cyclicPrefixResponse,
    Finset.sum_filter, Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ, rationalSawtooth]

theorem seed_clock22_work : rationalShortClock 30 961 22 = (-32/11 : ℚ) := by
  norm_num [rationalShortClock, BranchTransport.unitAddresses, cyclicPrefixResponse,
    Finset.sum_filter, Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ, rationalSawtooth]

theorem seed_clock19_work : rationalShortClock 30 961 19 = (-12/19 : ℚ) := by
  norm_num [rationalShortClock, BranchTransport.unitAddresses, cyclicPrefixResponse,
    Finset.sum_filter, Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ, rationalSawtooth]

theorem seed_clock24_work : rationalShortClock 30 961 24 = (53/3 : ℚ) := by
  norm_num [rationalShortClock, BranchTransport.unitAddresses, cyclicPrefixResponse,
    Finset.sum_filter, Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ, rationalSawtooth]

theorem seed_clock20_work : rationalShortClock 30 961 20 = (112/5 : ℚ) := by
  norm_num [rationalShortClock, BranchTransport.unitAddresses, cyclicPrefixResponse,
    Finset.sum_filter, Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ, rationalSawtooth]

theorem seed_packet_coherent_work : packetQuery 30 961 packetClocks (fun _ => 1) = (-3248/209 : ℝ) := by
  rw [coherent_packet_clock_sum]
  simp only [Fin.sum_univ_succ, packetClocks, Matrix.cons_val_zero, Matrix.cons_val_succ]
  rw [coherent_clock_rational 30 961 (by norm_num : 0 < 23),
    coherent_clock_rational 30 961 (by norm_num : 0 < 22),
    coherent_clock_rational 30 961 (by norm_num : 0 < 19),
    seed_clock23_work, seed_clock22_work, seed_clock19_work]
  norm_num

theorem seed_fringe_coherent_work : packetQuery 30 961 fringeClocks (fun _ => 1) = (601/15 : ℝ) := by
  rw [coherent_packet_clock_sum]
  simp only [Fin.sum_univ_succ, fringeClocks, Matrix.cons_val_zero, Matrix.cons_val_succ]
  rw [coherent_clock_rational 30 961 (by norm_num : 0 < 24),
    coherent_clock_rational 30 961 (by norm_num : 0 < 20), seed_clock24_work, seed_clock20_work]
  norm_num

theorem seed_complete_coherent_work : packetQuery 30 961 seedClocks (fun _ => 1) = (76889/3135 : ℝ) := by
  rw [coherent_packet_clock_sum]
  simp only [Fin.sum_univ_succ, seedClocks, Matrix.cons_val_zero, Matrix.cons_val_succ]
  rw [coherent_clock_rational 30 961 (by norm_num : 0 < 23),
    coherent_clock_rational 30 961 (by norm_num : 0 < 22),
    coherent_clock_rational 30 961 (by norm_num : 0 < 19),
    coherent_clock_rational 30 961 (by norm_num : 0 < 24),
    coherent_clock_rational 30 961 (by norm_num : 0 < 20),
    seed_clock23_work, seed_clock22_work, seed_clock19_work, seed_clock24_work, seed_clock20_work]
  norm_num

end NField.ResetForests.SeedRecord

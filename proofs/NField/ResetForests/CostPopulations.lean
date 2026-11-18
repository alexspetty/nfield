/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.PacketFigure
/-! # Every complete load-one packet and the fixed prefixes in the finite cost examples -/

set_option autoImplicit false
noncomputable section

namespace NField.ResetForests.ExactCost

open scoped BigOperators Matrix
open PhasePopulations LoadedWords CompletePackets PrefixGeometry LoadOnePackets

theorem cost43_prime : Nat.Prime 43 := by norm_num

theorem cost43_complete_starts : completeStarts 43 1 = {9, 11} := by
  have ha : packetLowerCutoff 43 = 8 := by norm_num [packetLowerCutoff, phaseReturnCutoff]
  have hb : packetUpperCutoff 43 = 13 := by norm_num [packetUpperCutoff]
  rw [load_one_start_set (by decide : Odd 43), ha, hb]
  decide +kernel

theorem cost43_packet9 : packetClocks 43 1 9 = {33, 32, 26} := by
  rw [load_one_packet_clocks (by decide) (by rw [cost43_complete_starts]; decide)]

theorem cost43_packet11 : packetClocks 43 1 11 = {31, 30, 27} := by
  rw [load_one_packet_clocks (by decide) (by rw [cost43_complete_starts]; decide)]

theorem cost43_ordered : orderedPackets 43 {1} = [toLex (1, 9), toLex (1, 11)] := by
  rw [orderedPackets, packetKeys, Finset.singleton_biUnion, cost43_complete_starts]
  convert (List.toFinset_sort (r := (· ≤ ·)) (by decide : [toLex (1, 9), toLex (1, 11)].Nodup)).2 (by decide) using 1
  congr 1

theorem cost43_prefix1 : prefixClocks 43 {1} 1 = {33, 32, 26} := by
  norm_num [prefixClocks, cost43_ordered, List.take, cost43_packet9, cost43_packet11]

theorem cost43_prefix2 : prefixClocks 43 {1} 2 = {33, 32, 26, 31, 30, 27} := by
  norm_num [prefixClocks, cost43_ordered, List.take, cost43_packet9, cost43_packet11]
  decide

theorem cost43_chosen : chosenClocks 43 {1} = {33, 32, 26, 31, 30, 27} := by
  have h := prefix_clocks_final 43 {1}
  rw [cost43_ordered] at h
  change prefixClocks 43 {1} 2 = chosenClocks 43 {1} at h
  rw [cost43_prefix2] at h
  exact h.symm

theorem cost43_cut_values : ∀ r : Fin 3,
    dyadicCuts 2 r.val = ![0, 1, 2] r := by decide

theorem cost43_chosen_positive : ∀ k ∈ chosenClocks 43 {1}, 0 < k := by
  rw [cost43_chosen]
  decide +kernel

theorem cost43_chosen_load : ∀ k ∈ chosenClocks 43 {1}, packetLoad 43 k = 1 := by
  rw [cost43_chosen]
  decide +kernel

theorem cost61_prime : Nat.Prime 61 := by norm_num

theorem cost61_complete_starts : completeStarts 61 1 = {9, 11, 13, 15, 17} := by
  have ha : packetLowerCutoff 61 = 9 := by norm_num [packetLowerCutoff, phaseReturnCutoff]
  have hb : packetUpperCutoff 61 = 19 := by norm_num [packetUpperCutoff]
  rw [load_one_start_set (by decide : Odd 61), ha, hb]
  decide +kernel

theorem cost61_packet9 : packetClocks 61 1 9 = {51, 50, 35} := by
  rw [load_one_packet_clocks (by decide) (by rw [cost61_complete_starts]; decide)]

theorem cost61_packet11 : packetClocks 61 1 11 = {49, 48, 36} := by
  rw [load_one_packet_clocks (by decide) (by rw [cost61_complete_starts]; decide)]

theorem cost61_packet13 : packetClocks 61 1 13 = {47, 46, 37} := by
  rw [load_one_packet_clocks (by decide) (by rw [cost61_complete_starts]; decide)]

theorem cost61_packet15 : packetClocks 61 1 15 = {45, 44, 38} := by
  rw [load_one_packet_clocks (by decide) (by rw [cost61_complete_starts]; decide)]

theorem cost61_packet17 : packetClocks 61 1 17 = {43, 42, 39} := by
  rw [load_one_packet_clocks (by decide) (by rw [cost61_complete_starts]; decide)]

theorem cost61_ordered : orderedPackets 61 {1} = [toLex (1, 9), toLex (1, 11), toLex (1, 13), toLex (1, 15), toLex (1, 17)] := by
  rw [orderedPackets, packetKeys, Finset.singleton_biUnion, cost61_complete_starts]
  convert (List.toFinset_sort (r := (· ≤ ·)) (by decide : [toLex (1, 9), toLex (1, 11), toLex (1, 13), toLex (1, 15), toLex (1, 17)].Nodup)).2 (by decide) using 1
  congr 1

theorem cost61_prefix1 : prefixClocks 61 {1} 1 = {51, 50, 35} := by
  norm_num [prefixClocks, cost61_ordered, List.take, cost61_packet9, cost61_packet11, cost61_packet13, cost61_packet15, cost61_packet17]

theorem cost61_prefix2 : prefixClocks 61 {1} 2 = {51, 50, 35, 49, 48, 36} := by
  norm_num [prefixClocks, cost61_ordered, List.take, cost61_packet9, cost61_packet11, cost61_packet13, cost61_packet15, cost61_packet17]
  decide

theorem cost61_prefix4 : prefixClocks 61 {1} 4 = {51, 50, 35, 49, 48, 36, 47, 46, 37, 45, 44, 38} := by
  norm_num [prefixClocks, cost61_ordered, List.take, cost61_packet9, cost61_packet11, cost61_packet13, cost61_packet15, cost61_packet17]
  decide

theorem cost61_prefix5 : prefixClocks 61 {1} 5 = {51, 50, 35, 49, 48, 36, 47, 46, 37, 45, 44, 38, 43, 42, 39} := by
  norm_num [prefixClocks, cost61_ordered, List.take, cost61_packet9, cost61_packet11, cost61_packet13, cost61_packet15, cost61_packet17]
  decide

theorem cost61_chosen : chosenClocks 61 {1} = {51, 50, 35, 49, 48, 36, 47, 46, 37, 45, 44, 38, 43, 42, 39} := by
  have h := prefix_clocks_final 61 {1}
  rw [cost61_ordered] at h
  change prefixClocks 61 {1} 5 = chosenClocks 61 {1} at h
  rw [cost61_prefix5] at h
  exact h.symm

theorem cost61_cut_values : ∀ r : Fin 5,
    dyadicCuts 5 r.val = ![0, 1, 2, 4, 5] r := by decide

theorem cost61_chosen_positive : ∀ k ∈ chosenClocks 61 {1}, 0 < k := by
  rw [cost61_chosen]
  decide +kernel

theorem cost61_chosen_load : ∀ k ∈ chosenClocks 61 {1}, packetLoad 61 k = 1 := by
  rw [cost61_chosen]
  decide +kernel

theorem cost73_prime : Nat.Prime 73 := by norm_num

theorem cost73_complete_starts : completeStarts 73 1 = {11, 13, 15, 17, 19, 21} := by
  have ha : packetLowerCutoff 73 = 10 := by norm_num [packetLowerCutoff, phaseReturnCutoff]
  have hb : packetUpperCutoff 73 = 23 := by norm_num [packetUpperCutoff]
  rw [load_one_start_set (by decide : Odd 73), ha, hb]
  decide +kernel

theorem cost73_packet11 : packetClocks 73 1 11 = {61, 60, 42} := by
  rw [load_one_packet_clocks (by decide) (by rw [cost73_complete_starts]; decide)]

theorem cost73_packet13 : packetClocks 73 1 13 = {59, 58, 43} := by
  rw [load_one_packet_clocks (by decide) (by rw [cost73_complete_starts]; decide)]

theorem cost73_packet15 : packetClocks 73 1 15 = {57, 56, 44} := by
  rw [load_one_packet_clocks (by decide) (by rw [cost73_complete_starts]; decide)]

theorem cost73_packet17 : packetClocks 73 1 17 = {55, 54, 45} := by
  rw [load_one_packet_clocks (by decide) (by rw [cost73_complete_starts]; decide)]

theorem cost73_packet19 : packetClocks 73 1 19 = {53, 52, 46} := by
  rw [load_one_packet_clocks (by decide) (by rw [cost73_complete_starts]; decide)]

theorem cost73_packet21 : packetClocks 73 1 21 = {51, 50, 47} := by
  rw [load_one_packet_clocks (by decide) (by rw [cost73_complete_starts]; decide)]

theorem cost73_ordered : orderedPackets 73 {1} = [toLex (1, 11), toLex (1, 13), toLex (1, 15), toLex (1, 17), toLex (1, 19), toLex (1, 21)] := by
  rw [orderedPackets, packetKeys, Finset.singleton_biUnion, cost73_complete_starts]
  convert (List.toFinset_sort (r := (· ≤ ·)) (by decide : [toLex (1, 11), toLex (1, 13), toLex (1, 15), toLex (1, 17), toLex (1, 19), toLex (1, 21)].Nodup)).2 (by decide) using 1
  congr 1

theorem cost73_prefix1 : prefixClocks 73 {1} 1 = {61, 60, 42} := by
  norm_num [prefixClocks, cost73_ordered, List.take, cost73_packet11, cost73_packet13, cost73_packet15, cost73_packet17, cost73_packet19, cost73_packet21]

theorem cost73_prefix2 : prefixClocks 73 {1} 2 = {61, 60, 42, 59, 58, 43} := by
  norm_num [prefixClocks, cost73_ordered, List.take, cost73_packet11, cost73_packet13, cost73_packet15, cost73_packet17, cost73_packet19, cost73_packet21]
  decide

theorem cost73_prefix4 : prefixClocks 73 {1} 4 = {61, 60, 42, 59, 58, 43, 57, 56, 44, 55, 54, 45} := by
  norm_num [prefixClocks, cost73_ordered, List.take, cost73_packet11, cost73_packet13, cost73_packet15, cost73_packet17, cost73_packet19, cost73_packet21]
  decide

theorem cost73_prefix6 : prefixClocks 73 {1} 6 = {61, 60, 42, 59, 58, 43, 57, 56, 44, 55, 54, 45, 53, 52, 46, 51, 50, 47} := by
  norm_num [prefixClocks, cost73_ordered, List.take, cost73_packet11, cost73_packet13, cost73_packet15, cost73_packet17, cost73_packet19, cost73_packet21]
  decide

theorem cost73_chosen : chosenClocks 73 {1} = {61, 60, 42, 59, 58, 43, 57, 56, 44, 55, 54, 45, 53, 52, 46, 51, 50, 47} := by
  have h := prefix_clocks_final 73 {1}
  rw [cost73_ordered] at h
  change prefixClocks 73 {1} 6 = chosenClocks 73 {1} at h
  rw [cost73_prefix6] at h
  exact h.symm

theorem cost73_cut_values : ∀ r : Fin 5,
    dyadicCuts 6 r.val = ![0, 1, 2, 4, 6] r := by decide

theorem cost73_chosen_positive : ∀ k ∈ chosenClocks 73 {1}, 0 < k := by
  rw [cost73_chosen]
  decide +kernel

theorem cost73_chosen_load : ∀ k ∈ chosenClocks 73 {1}, packetLoad 73 k = 1 := by
  rw [cost73_chosen]
  decide +kernel

end NField.ResetForests.ExactCost

/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.PacketCost
/-! # Exact dyadic load coverage and a subpower bound on its logarithmic count -/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.CostCriteria

open scoped BigOperators
open LoadedWords CompletePackets PrefixGeometry

def bandCount (p : ℕ) : ℕ := Nat.log 2 p + 1

theorem maximum_load_le_base (p : ℕ) : packetMaxLoad p ≤ p :=
  (Nat.div_le_self _ _).trans (Nat.sub_le p 1)

theorem dyadic_band_membership (p j m : ℕ) :
    m ∈ bandLoads p (2 ^ j) ↔ m ∈ entireLoads p ∧ Nat.log 2 m = j := by
  simp only [bandLoads, entireLoads, Finset.mem_filter]
  constructor
  · rintro ⟨hm, hlo, hhi⟩
    refine ⟨hm, Nat.log_eq_of_pow_le_of_lt_pow hlo ?_⟩
    simpa only [pow_succ, Nat.mul_comm] using hhi
  · rintro ⟨hm, hj⟩
    have hm0 : m ≠ 0 := by have := (Finset.mem_Icc.mp hm).1; omega
    refine ⟨hm, ?_, ?_⟩
    · rw [← hj]
      exact Nat.pow_log_le_self 2 hm0
    · rw [← hj]
      simpa only [pow_succ, Nat.mul_comm] using Nat.lt_pow_succ_log_self (by decide : 1 < 2) m

theorem dyadic_bands_disjoint (p : ℕ) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (bandLoads p (2 ^ i)) (bandLoads p (2 ^ j)) := by
  apply Finset.disjoint_left.mpr
  intro m hmi hmj
  have hi := ((dyadic_band_membership p i m).mp hmi).2
  have hj := ((dyadic_band_membership p j m).mp hmj).2
  exact hij (hi.symm.trans hj)

theorem dyadic_loads_union (p : ℕ) :
    (Finset.range (bandCount p)).biUnion (fun j => bandLoads p (2 ^ j)) = entireLoads p := by
  ext m
  constructor
  · intro hm
    obtain ⟨j, _, hm⟩ := Finset.mem_biUnion.mp hm
    exact ((dyadic_band_membership p j m).mp hm).1
  · intro hm
    have hmp : m ≤ p := (Finset.mem_Icc.mp hm).2.trans (maximum_load_le_base p)
    refine Finset.mem_biUnion.mpr ⟨Nat.log 2 m, ?_, (dyadic_band_membership p _ m).mpr ⟨hm, rfl⟩⟩
    apply Finset.mem_range.mpr
    have hlog : Nat.log 2 m ≤ Nat.log 2 p := Nat.log_mono_right hmp
    exact Nat.lt_succ_of_le hlog

theorem entire_readout_dyadic_sum (p : ℕ) :
    packetReadout p (entireLoads p) =
      ∑ j ∈ Finset.range (bandCount p), packetReadout p (bandLoads p (2 ^ j)) := by
  rw [packet_readout_load_sum p (entireLoads p) (by
    intro m hm; exact (Finset.mem_Icc.mp hm).1)]
  rw [← dyadic_loads_union p, Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro j _
    exact (packet_readout_load_sum p (bandLoads p (2 ^ j)) (by
      intro m hm; exact (Finset.mem_Icc.mp ((dyadic_band_membership p j m).mp hm).1).1)).symm
  · intro i _ j _ hij
    exact dyadic_bands_disjoint p hij

theorem band_count_le_real_log {p : ℕ} (hp : 1 ≤ p) :
    (bandCount p : ℝ) ≤ 1 + Real.log (p : ℝ) / Real.log 2 := by
  have hpow : 2 ^ Nat.log 2 p ≤ p := Nat.pow_log_le_self 2 (by omega)
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ Nat.log 2 p)
    (by exact_mod_cast hpow : (2 : ℝ) ^ Nat.log 2 p ≤ (p : ℝ))
  rw [Real.log_pow] at hlog
  have htwo : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hdiv : (Nat.log 2 p : ℝ) ≤ Real.log (p : ℝ) / Real.log 2 :=
    (le_div_iff₀ htwo).mpr hlog
  simp only [bandCount, Nat.cast_add, Nat.cast_one]
  linarith

theorem band_count_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, 1 ≤ p → (bandCount p : ℝ) ≤ C * (p : ℝ) ^ ε := by
  have htwo : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1 + (1 / ε) / Real.log 2, by positivity, ?_⟩
  intro p hp
  have hpow : 1 ≤ (p : ℝ) ^ ε := Real.one_le_rpow (by exact_mod_cast hp) hε.le
  have hlog := Real.log_natCast_le_rpow_div p hε
  calc
    _ ≤ 1 + Real.log (p : ℝ) / Real.log 2 := band_count_le_real_log hp
    _ ≤ (p : ℝ) ^ ε + ((p : ℝ) ^ ε / ε) / Real.log 2 :=
      add_le_add hpow (div_le_div_of_nonneg_right hlog htwo.le)
    _ = _ := by ring

end NField.ResetForests.CostCriteria

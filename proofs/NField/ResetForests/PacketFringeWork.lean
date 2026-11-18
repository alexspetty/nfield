/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.PacketFringeCount
/-! # The original signed-clock weights on the entire packet fringe

The finite bound uses the printed maximum over positive clocks up to N.
Its uniform consequence uses the existing Mathlib-based subpower estimates.
-/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.CompletePackets

open scoped BigOperators
open CenteredPhase PhasePopulations LoadedWords

def cutoffDivisorMaximum (N : ℕ) : ℕ :=
  (Finset.Icc 1 N).sup (fun k => k.divisors.card)
def packetFringeWork (p : ℕ) : ℝ :=
  ∑ k ∈ packetFringe p, |4 * Core.clockReading (p - 1) (p ^ 2) k|

theorem cutoff_divisor_count {N k : ℕ} (hk : 1 ≤ k) (hkN : k ≤ N) :
    k.divisors.card ≤ cutoffDivisorMaximum N :=
  Finset.le_sup (f := fun n : ℕ => n.divisors.card) (Finset.mem_Icc.mpr ⟨hk, hkN⟩)

theorem cutoff_divisor_maximum_le_phase (p : ℕ) :
    cutoffDivisorMaximum (p - 1) ≤ phaseDivisorMaximum p := by
  apply Finset.sup_le
  intro k hk
  obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.mp hk
  exact divisor_count_le_phase_maximum hk1 (by omega)

theorem packet_fringe_finite_work {p : ℕ} (hp : p.Prime) :
    packetFringeWork p ≤
      16 * ((p - 1 : ℕ) : ℝ) * (harmonic (p - 1) : ℝ) ^ 2 *
        (cutoffDivisorMaximum (p - 1) : ℝ) * (packetMaxLoad p : ℝ) := by
  have hbound : ∀ k ∈ packetFringe p,
      |4 * Core.clockReading (p - 1) (p ^ 2) k| ≤
        2 * ((p - 1 : ℕ) : ℝ) * (harmonic (p - 1) : ℝ) ^ 2 *
          (cutoffDivisorMaximum (p - 1) : ℝ) := by
    intro k hk
    have hr := (Finset.mem_sdiff.mp hk).1
    obtain ⟨hk2, hkp, _, _⟩ := retained_clock_bounds hr
    have hT : (k.divisors.card : ℝ) ≤ (cutoffDivisorMaximum (p - 1) : ℝ) := by
      exact_mod_cast cutoff_divisor_count (by omega : 1 ≤ k) (by omega : k ≤ p - 1)
    exact (raw_clock_card_bound hp hk2 hkp).trans
      (mul_le_mul_of_nonneg_left hT (by positivity))
  have hcard : ((packetFringe p).card : ℝ) ≤ 8 * (packetMaxLoad p : ℝ) := by
    exact_mod_cast packet_fringe_card hp
  unfold packetFringeWork
  calc
    _ ≤ ∑ _k ∈ packetFringe p,
        2 * ((p - 1 : ℕ) : ℝ) * (harmonic (p - 1) : ℝ) ^ 2 *
          (cutoffDivisorMaximum (p - 1) : ℝ) := Finset.sum_le_sum hbound
    _ = ((packetFringe p).card : ℝ) *
        (2 * ((p - 1 : ℕ) : ℝ) * (harmonic (p - 1) : ℝ) ^ 2 *
          (cutoffDivisorMaximum (p - 1) : ℝ)) := by simp
    _ ≤ (8 * (packetMaxLoad p : ℝ)) *
        (2 * ((p - 1 : ℕ) : ℝ) * (harmonic (p - 1) : ℝ) ^ 2 *
          (cutoffDivisorMaximum (p - 1) : ℝ)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

theorem sqrt_le_packet_lower_cutoff (p : ℕ) : Nat.sqrt p ≤ packetLowerCutoff p := by
  by_cases hq : Nat.sqrt p ≤ 2
  · unfold packetLowerCutoff
    omega
  · have hq3 : 3 ≤ Nat.sqrt p := by omega
    have hH : Nat.sqrt p ≤ p / 3 := (Nat.le_div_iff_mul_le (by decide : 0 < 3)).mpr
      (by nlinarith [Nat.sqrt_le p])
    unfold packetLowerCutoff phaseReturnCutoff
    rw [min_eq_left hH]
    omega

theorem packet_max_load_le_sqrt {p : ℕ} (hp : 0 < p) :
    packetMaxLoad p ≤ Nat.sqrt p := by
  have hqpos := Nat.sqrt_pos.mpr hp
  have ha := sqrt_le_packet_lower_cutoff p
  have hprod := Nat.div_mul_le_self (p - 1) (2 * packetLowerCutoff p)
  change packetMaxLoad p * (2 * packetLowerCutoff p) ≤ p - 1 at hprod
  by_contra hn
  have hM : Nat.sqrt p + 1 ≤ packetMaxLoad p := by omega
  have hl := Nat.mul_le_mul hM (Nat.mul_le_mul_left 2 ha)
  nlinarith [Nat.lt_succ_sqrt p, Nat.sub_le p 1]

theorem packet_arithmetic_cost_le_phase {p : ℕ} (hp : 1 ≤ p) :
    (harmonic (p - 1) : ℝ) ^ 2 * (cutoffDivisorMaximum (p - 1) : ℝ) ≤
      phaseArithmeticCost p := by
  have hT : (cutoffDivisorMaximum (p - 1) : ℝ) ≤ (phaseDivisorMaximum p : ℝ) := by
    exact_mod_cast cutoff_divisor_maximum_le_phase p
  have h1N : 1 ≤ phaseDivisorMaximum p := by
    have h := divisor_count_le_phase_maximum (p := p) (n := 1) (by decide) (by omega)
    simpa using h
  have h1 : (1 : ℝ) ≤ (phaseDivisorMaximum p : ℝ) := by exact_mod_cast h1N
  have hsq : (cutoffDivisorMaximum (p - 1) : ℝ) ≤ (phaseDivisorMaximum p : ℝ) ^ 2 :=
    hT.trans (by nlinarith)
  exact mul_le_mul_of_nonneg_left hsq (sq_nonneg _)

theorem packet_fringe_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime →
      packetFringeWork p ≤ C * (p : ℝ) ^ (3 / 2 + ε) := by
  obtain ⟨C, hC, hc⟩ := phase_arithmetic_small_power ε hε
  refine ⟨16 * C, by positivity, ?_⟩
  intro p hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hN : ((p - 1 : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast Nat.sub_le p 1
  have hM : (packetMaxLoad p : ℝ) ≤ Real.sqrt (p : ℝ) :=
    (Nat.cast_le.mpr (packet_max_load_le_sqrt hp.pos)).trans Real.nat_sqrt_le_real_sqrt
  have hA := (packet_arithmetic_cost_le_phase hp.one_le).trans (hc p hp.one_le)
  calc
    _ ≤ 16 * ((p - 1 : ℕ) : ℝ) * (harmonic (p - 1) : ℝ) ^ 2 *
        (cutoffDivisorMaximum (p - 1) : ℝ) * (packetMaxLoad p : ℝ) := packet_fringe_finite_work hp
    _ = 16 * ((p - 1 : ℕ) : ℝ) *
        ((harmonic (p - 1) : ℝ) ^ 2 * (cutoffDivisorMaximum (p - 1) : ℝ)) *
        (packetMaxLoad p : ℝ) := by ring
    _ ≤ 16 * (p : ℝ) * (C * (p : ℝ) ^ ε) * Real.sqrt (p : ℝ) := by
      gcongr
    _ = (16 * C) * ((p : ℝ) ^ (1 + ε) * (p : ℝ) ^ (1 / 2 : ℝ)) := by
      rw [Real.rpow_add hpR, Real.rpow_one, Real.sqrt_eq_rpow]
      ring
    _ = _ := by
      rw [← Real.rpow_add hpR]
      congr 2
      ring

end NField.ResetForests.CompletePackets

/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.Coordinates
import NField.ResetForests.DivisorBudget
import NField.ResetForests.Sampling
import NField.ResetForests.OrderedWork
import NField.ResetForests.Words
import NField.ResetForests.Carry
import NField.ResetForests.Readout
import NField.ResetForests.CoherentWork
import NField.ResetForests.Targets
import NField.ResetForests.GridWork
import NField.ResetForests.Centered
import NField.ResetForests.CarryClock
import NField.ResetForests.ClockBinary
import NField.ResetForests.PhaseFringe
import NField.ResetForests.LoadTail
import NField.ResetForests.ForestRates
import NField.ResetForests.Opening
import NField.ResetForests.Complement
import NField.ResetForests.WindowExample
import NField.ResetForests.EnergyMatrices
import NField.ResetForests.FibreDirections
import NField.ResetForests.FibreBasisTrace
import NField.ResetForests.GramSectors
import NField.ResetForests.TorusIncidence
import NField.ResetForests.CompleteReset
import NField.ResetForests.OrderedMasks
/-! # Actual loaded word coordinates of the cutoff interior

The word congruences parametrize the original clocks, with their load,
centered phase and lower or upper branch retained.
-/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.LoadedWords

open CenteredPhase PhasePopulations

def packetLowerCutoff (p : ℕ) : ℕ := phaseReturnCutoff p + 2
def packetUpperCutoff (p : ℕ) : ℕ := p / 3 - 1
def packetLoad (p k : ℕ) : ℕ := (p - 1) / k
def packetMaxLoad (p : ℕ) : ℕ := (p - 1) / (2 * packetLowerCutoff p)
def packetWordCutoff (p m : ℕ) : ℕ :=
  min (packetUpperCutoff p) ((p - 1) / (2 * m + 1))
def lowerWords (p m : ℕ) : Finset ℕ :=
  (Finset.Icc (packetLowerCutoff p - 1) (packetWordCutoff p m - 1)).filter
    (fun v => v % m = (p - 1) % m)
def upperWords (p m : ℕ) : Finset ℕ :=
  (Finset.Icc (packetLowerCutoff p) (packetWordCutoff p m)).filter
    (fun s => (p + s) % (m + 1) = 0)
def lowerClock (p m v : ℕ) : ℕ := (p - 1 - v) / m
def upperClock (p m s : ℕ) : ℕ := (p + s) / (m + 1)
def lowerBranch (p k : ℕ) : Prop := p % k ≤ k - p % k

theorem retained_clock_bounds {p k : ℕ} (hk : k ∈ retainedClocks p) :
    2 ≤ k ∧ k < p ∧ packetLowerCutoff p ≤ centeredPhase p k ∧
      centeredPhase p k ≤ packetUpperCutoff p := by
  obtain ⟨hI, ha, hb⟩ := Finset.mem_filter.mp hk
  obtain ⟨hk2, hkp⟩ := Finset.mem_Icc.mp hI
  exact ⟨hk2, by omega, ha, hb⟩

theorem retained_clock_load_bounds {p k : ℕ} (hk : k ∈ retainedClocks p) :
    1 ≤ packetLoad p k ∧ packetLoad p k ≤ packetMaxLoad p ∧
      2 * packetLowerCutoff p ≤ k := by
  obtain ⟨hk2, hkp, ha, _⟩ := retained_clock_bounds hk
  have hr := Nat.mod_lt p (by omega : 0 < k)
  have hc1 : centeredPhase p k ≤ p % k := min_le_left _ _
  have hc2 : centeredPhase p k ≤ k - p % k := min_le_right _ _
  have hka : 2 * packetLowerCutoff p ≤ k := by omega
  have hapos : 0 < 2 * packetLowerCutoff p := by
    unfold packetLowerCutoff
    omega
  have hprod := Nat.div_mul_le_self (p - 1) k
  refine ⟨(Nat.le_div_iff_mul_le (by omega)).mpr (by omega), ?_, hka⟩
  apply (Nat.le_div_iff_mul_le hapos).mpr
  unfold packetLoad
  nlinarith

theorem lower_decomposition_spec {p m h k : ℕ} (hh : 0 < h)
    (hphase : 2 * h < k) (he : p = h + k * m) :
    packetLoad p k = m ∧ p % k = h ∧ centeredPhase p k = h ∧ lowerBranch p k := by
  have hk : 0 < k := by omega
  have hr : h < k := by omega
  have hm : p % k = h := by rw [he]; simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  have hn : p - 1 = (h - 1) + k * m := by omega
  refine ⟨?_, hm, ?_, ?_⟩
  · unfold packetLoad
    rw [hn]
    simp [Nat.add_mul_div_left, hk, Nat.div_eq_of_lt (by omega : h - 1 < k)]
  · unfold centeredPhase
    rw [hm]
    exact min_eq_left (by omega)
  · unfold lowerBranch
    rw [hm]
    omega

theorem upper_decomposition_spec {p m h k : ℕ} (hh : 0 < h)
    (hphase : 2 * h < k) (he : p + h = k * (m + 1)) :
    packetLoad p k = m ∧ p % k = k - h ∧ centeredPhase p k = h ∧
      ¬lowerBranch p k := by
  have hk : 0 < k := by omega
  have hr : k - h < k := by omega
  have hp : p = (k - h) + k * m := by nlinarith [Nat.sub_add_cancel (by omega : h ≤ k)]
  have hm : p % k = k - h := by rw [hp]; simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  have hn : p - 1 = (k - h - 1) + k * m := by omega
  refine ⟨?_, hm, ?_, ?_⟩
  · unfold packetLoad
    rw [hn]
    simp [Nat.add_mul_div_left, hk, Nat.div_eq_of_lt (by omega : k - h - 1 < k)]
  · unfold centeredPhase
    rw [hm]
    have heh : k - (k - h) = h := by omega
    rw [heh]
    exact min_eq_right (by omega)
  · unfold lowerBranch
    rw [hm]
    omega

theorem lower_quotient_spec {p m h : ℕ} (hm : 0 < m) (hh : 0 < h)
    (hphase : (2 * m + 1) * h < p) (hd : m ∣ p - h) :
    let k := (p - h) / m
    2 * h < k ∧ k < p ∧ p = h + k * m ∧
      packetLoad p k = m ∧ centeredPhase p k = h ∧ lowerBranch p k := by
  dsimp only
  have hhp : h < p := by nlinarith
  have he : (p - h) / m * m = p - h := Nat.div_mul_cancel hd
  have hdecomp : p = h + (p - h) / m * m := by omega
  have hwide : 2 * h < (p - h) / m := by
    by_contra hn
    have hle : (p - h) / m ≤ 2 * h := by omega
    nlinarith
  have hkp : (p - h) / m < p := by nlinarith
  obtain ⟨hload, _, hc, hb⟩ := lower_decomposition_spec hh hwide hdecomp
  exact ⟨hwide, hkp, hdecomp, hload, hc, hb⟩

theorem upper_quotient_spec {p m h : ℕ} (hm : 0 < m) (hh : 0 < h)
    (hphase : (2 * m + 1) * h < p) (hd : m + 1 ∣ p + h) :
    let k := (p + h) / (m + 1)
    2 * h < k ∧ k < p ∧ p + h = k * (m + 1) ∧
      packetLoad p k = m ∧ centeredPhase p k = h ∧ ¬lowerBranch p k := by
  dsimp only
  have he : (p + h) / (m + 1) * (m + 1) = p + h := Nat.div_mul_cancel hd
  have hwide : 2 * h < (p + h) / (m + 1) := by
    by_contra hn
    have hle : (p + h) / (m + 1) ≤ 2 * h := by omega
    nlinarith
  have hkp : (p + h) / (m + 1) < p := by nlinarith
  obtain ⟨hload, _, hc, hb⟩ := upper_decomposition_spec hh hwide he.symm
  exact ⟨hwide, hkp, he.symm, hload, hc, hb⟩

theorem retained_phase_strict {p k : ℕ} (hp : p.Prime)
    (hk : k ∈ retainedClocks p) :
    (2 * packetLoad p k + 1) * centeredPhase p k < p := by
  obtain ⟨hk2, hkp, ha, hb⟩ := retained_clock_bounds hk
  have hh : 2 ≤ centeredPhase p k := by
    unfold packetLowerCutoff at ha
    omega
  have hhp : centeredPhase p k < p := by
    unfold packetUpperCutoff at hb
    have := Nat.div_le_self p 3
    omega
  have hr := prime_remainder_pos hp hk2 hkp
  have hd := (predecessor_remainder (by omega : 0 < k) hr).2
  have he : p = p % k + k * packetLoad p k := by
    unfold packetLoad
    rw [hd]
    exact (Nat.mod_add_div p k).symm
  have hrl := Nat.mod_lt p (by omega : 0 < k)
  by_cases hl : lowerBranch p k
  · have hc : centeredPhase p k = p % k := min_eq_left hl
    have hwide := (centered_lower_branch hp hk2 hkp hl).2.1
    have hle : (2 * packetLoad p k + 1) * centeredPhase p k ≤ p := by
      rw [hc] at *
      nlinarith
    apply lt_of_le_of_ne hle
    intro hEq
    have hdp : centeredPhase p k ∣ p := ⟨2 * packetLoad p k + 1, by nlinarith [hEq]⟩
    rcases (Nat.dvd_prime hp).mp hdp with h | h <;> omega
  · have hbranch : k - p % k < p % k := by exact Nat.lt_of_not_ge hl
    have hc : centeredPhase p k = k - p % k := min_eq_right hbranch.le
    have hwide := (centered_upper_branch hp hk2 hkp hbranch).2.1
    have hpos := (retained_clock_load_bounds hk).1
    nlinarith [Nat.sub_add_cancel hrl.le]

theorem retained_phase_word_cutoff {p k : ℕ} (hp : p.Prime)
    (hk : k ∈ retainedClocks p) :
    centeredPhase p k ≤ packetWordCutoff p (packetLoad p k) := by
  have hb := (retained_clock_bounds hk).2.2.2
  have hs := retained_phase_strict hp hk
  apply le_min hb
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 2 * packetLoad p k + 1)).mpr
  nlinarith [Nat.sub_add_cancel hp.one_le]

end NField.ResetForests.LoadedWords

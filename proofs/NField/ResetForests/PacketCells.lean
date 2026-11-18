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
import NField.ResetForests.PacketPopulation
/-! # Complete cells on the integer word line

Upper congruence classes determine a unique cell for every integer word.
The literal lower congruence has one or two representatives in each cell.
-/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.CompletePackets

def cellAnchor (p m v : ℤ) : ℤ := v - (p + v) % (m + 1)
def cellDelta (p m s : ℤ) : ℤ := (p - 1 - s) % m
def lowerCellWords (p m s : ℤ) : Finset ℤ :=
  (Finset.Icc s (s + m)).filter (fun v => Int.ModEq m v (p - 1))

theorem cell_anchor_bounds (p v : ℤ) {m : ℤ} (hm : 0 < m) :
    cellAnchor p m v ≤ v ∧ v ≤ cellAnchor p m v + m := by
  have h0 := Int.emod_nonneg (p + v) (by omega : m + 1 ≠ 0)
  have hlt := Int.emod_lt_of_pos (p + v) (by omega : 0 < m + 1)
  unfold cellAnchor
  omega

theorem cell_anchor_upper (p m v : ℤ) : (m + 1) ∣ p + cellAnchor p m v := by
  unfold cellAnchor
  apply Int.dvd_iff_emod_eq_zero.mpr
  have he : p + (v - (p + v) % (m + 1)) = (p + v) - (p + v) % (m + 1) := by ring
  rw [he, Int.sub_emod, Int.emod_emod, sub_self, Int.zero_emod]

theorem cell_anchor_unique {p m v s : ℤ} (_hm : 0 < m)
    (hs : (m + 1) ∣ p + s) (hlo : s ≤ v) (hhi : v ≤ s + m) :
    cellAnchor p m v = s := by
  have hsmall : (v - s) % (m + 1) = v - s :=
    Int.emod_eq_of_lt (by omega) (by omega)
  have hzero := Int.dvd_iff_emod_eq_zero.mp hs
  have he : p + v = (p + s) + (v - s) := by ring
  unfold cellAnchor
  rw [he]
  simp only [Int.add_emod, hzero, zero_add, hsmall]
  omega

theorem upper_cells_disjoint {p m s t : ℤ} (hm : 0 < m)
    (hs : (m + 1) ∣ p + s) (ht : (m + 1) ∣ p + t) (hst : s ≠ t) :
    Disjoint (Finset.Icc s (s + m)) (Finset.Icc t (t + m)) := by
  apply Finset.disjoint_left.mpr
  intro v hvs hvt
  obtain ⟨hsl, hsu⟩ := Finset.mem_Icc.mp hvs
  obtain ⟨htl, htu⟩ := Finset.mem_Icc.mp hvt
  exact hst ((cell_anchor_unique hm hs hsl hsu).symm.trans
    (cell_anchor_unique hm ht htl htu))

theorem cell_delta_range (p s : ℤ) {m : ℤ} (hm : 0 < m) :
    0 ≤ cellDelta p m s ∧ cellDelta p m s < m := by
  exact ⟨Int.emod_nonneg _ hm.ne', Int.emod_lt_of_pos _ hm⟩

theorem lower_cell_members {p m s v : ℤ} (hm : 0 < m) :
    v ∈ lowerCellWords p m s ↔
      v = s + cellDelta p m s ∨ (cellDelta p m s = 0 ∧ v = s + m) := by
  have hδ := cell_delta_range p s hm
  constructor
  · intro hv
    obtain ⟨hI, hc⟩ := Finset.mem_filter.mp hv
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hI
    have ht : Int.ModEq m (v - s) (p - 1 - s) := hc.sub_right s
    change (v - s) % m = cellDelta p m s at ht
    by_cases hsmall : v - s < m
    · rw [Int.emod_eq_of_lt (by omega) hsmall] at ht
      exact Or.inl (by omega)
    · have he : v - s = m := by omega
      rw [he, Int.emod_self] at ht
      exact Or.inr ⟨ht.symm, by omega⟩
  · rintro (rfl | ⟨hzero, rfl⟩)
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      have h := (Int.mod_modEq (p - 1 - s) m).add_left s
      change Int.ModEq m (s + (p - 1 - s) % m) (p - 1)
      convert h using 1
      ring
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩, ?_⟩
      have hs : Int.ModEq m s (p - 1) := by
        have h := (Int.mod_modEq (p - 1 - s) m).add_left s
        change Int.ModEq m (s + cellDelta p m s) (s + (p - 1 - s)) at h
        simpa only [hzero, add_zero, add_sub_cancel] using h
      unfold Int.ModEq at hs ⊢
      simpa only [Int.add_emod, Int.emod_self, add_zero, Int.emod_emod] using hs

theorem lower_cell_eq {p m s : ℤ} (hm : 0 < m) :
    lowerCellWords p m s =
      if cellDelta p m s = 0 then {s, s + m} else {s + cellDelta p m s} := by
  ext v
  rw [lower_cell_members hm]
  by_cases hd : cellDelta p m s = 0 <;> simp [hd, or_comm]

theorem lower_cell_card {p m s : ℤ} (hm : 0 < m) :
    (lowerCellWords p m s).card = if cellDelta p m s = 0 then 2 else 1 := by
  rw [lower_cell_eq hm]
  have hne : s ≠ s + m := by omega
  split_ifs <;> simp [hne]

theorem lower_cell_card_bounds {p m s : ℤ} (hm : 0 < m) :
    1 ≤ (lowerCellWords p m s).card ∧ (lowerCellWords p m s).card ≤ 2 := by
  rw [lower_cell_card hm]
  split_ifs <;> omega

theorem sole_upper_in_cell {p m s v : ℤ} (hm : 0 < m)
    (hs : (m + 1) ∣ p + s) (hlo : s ≤ v) (hhi : v ≤ s + m) :
    (m + 1) ∣ p + v ↔ v = s := by
  constructor
  · intro hv
    have hself := cell_anchor_unique hm hv (le_refl v) (by omega : v ≤ v + m)
    have hs' := cell_anchor_unique hm hs hlo hhi
    omega
  · rintro rfl
    exact hs

end NField.ResetForests.CompletePackets

/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.PacketEquivalence
/-! # The exact offset cycle of consecutive upper cells

The integer extension of the literal cutoff offset handles the full cycle.
Within the cutoff it is exactly the original natural-valued offset.
-/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.PacketCycles

open CompletePackets

def offsetOrbit (p m s : ℤ) : Finset ℤ :=
  (Finset.Ico 0 m).image (fun t => cellDelta p m (s + t * (m + 1)))

theorem packet_delta_range (p s : ℕ) {m : ℕ} (hm : 0 < m) :
    0 ≤ packetDelta p m s ∧ packetDelta p m s < m := ⟨Nat.zero_le _, Nat.mod_lt _ hm⟩

theorem cell_delta_progression (p m s t : ℤ) :
    cellDelta p m (s + t * (m + 1)) = (cellDelta p m s - t) % m := by
  have h : Int.ModEq m (p - 1 - (s + t * (m + 1))) (p - 1 - s - t) := by
    apply Int.modEq_iff_dvd.mpr
    exact ⟨t, by ring⟩
  have hbase := (Int.mod_modEq (p - 1 - s) m).sub_right t
  exact h.trans hbase.symm

theorem cell_delta_next (p m s : ℤ) :
    cellDelta p m (s + m + 1) = (cellDelta p m s - 1) % m := by
  simpa only [one_mul, add_assoc] using cell_delta_progression p m s 1

theorem cell_delta_drift (p m s : ℤ) :
    Int.ModEq m (cellDelta p m (s + m + 1)) (cellDelta p m s - 1) := by
  rw [cell_delta_next]
  exact Int.mod_modEq _ _

theorem packet_delta_drift {p m s : ℕ} (hp : 1 ≤ p) (hs : s + m + 1 ≤ p - 1) :
    Int.ModEq (m : ℤ) (packetDelta p m (s + m + 1) : ℤ)
      ((packetDelta p m s : ℤ) - 1) := by
  rw [← nat_cell_delta hp hs, ← nat_cell_delta hp (by omega : s ≤ p - 1)]
  push_cast
  exact cell_delta_drift _ _ _

theorem delta_steps_equal_iff (p m s t u : ℤ) :
    cellDelta p m (s + t * (m + 1)) = cellDelta p m (s + u * (m + 1)) ↔
      Int.ModEq m t u := by
  rw [cell_delta_progression, cell_delta_progression]
  constructor
  · intro he
    have hc : Int.ModEq m (cellDelta p m s - t) (cellDelta p m s - u) := he
    have h := hc.sub_left (cellDelta p m s)
    convert h using 1 <;> ring
  · intro hc
    exact hc.sub_left (cellDelta p m s)

theorem delta_steps_injective (p s : ℤ) {m : ℤ} (_hm : 0 < m) :
    Set.InjOn (fun t => cellDelta p m (s + t * (m + 1))) (Finset.Ico 0 m : Set ℤ) := by
  intro t ht u hu he
  obtain ⟨ht0, htm⟩ := Finset.mem_Ico.mp ht
  obtain ⟨hu0, hum⟩ := Finset.mem_Ico.mp hu
  have hc := (delta_steps_equal_iff p m s t u).mp he
  change t % m = u % m at hc
  simpa only [Int.emod_eq_of_lt ht0 htm, Int.emod_eq_of_lt hu0 hum] using hc

theorem offset_orbit_eq (p s : ℤ) {m : ℤ} (hm : 0 < m) :
    offsetOrbit p m s = Finset.Ico 0 m := by
  have hsub : offsetOrbit p m s ⊆ Finset.Ico 0 m := by
    intro d hd
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hd
    exact Finset.mem_Ico.mpr (cell_delta_range _ _ hm)
  apply Finset.eq_of_subset_of_card_le hsub
  unfold offsetOrbit
  rw [Finset.card_image_of_injOn (delta_steps_injective p s hm)]

theorem offset_orbit_card (p s : ℤ) {m : ℤ} (hm : 0 < m) :
    (offsetOrbit p m s).card = m.toNat := by rw [offset_orbit_eq p s hm]; simp

theorem offset_zero_unique (p s : ℤ) {m : ℤ} (hm : 0 < m) :
    ∃! t : ℤ, t ∈ Finset.Ico 0 m ∧ cellDelta p m (s + t * (m + 1)) = 0 := by
  have hz : (0 : ℤ) ∈ offsetOrbit p m s := by
    rw [offset_orbit_eq p s hm]
    exact Finset.mem_Ico.mpr ⟨le_rfl, hm⟩
  obtain ⟨t, ht, he⟩ := Finset.mem_image.mp hz
  refine ⟨t, ⟨ht, he⟩, ?_⟩
  intro u hu
  exact delta_steps_injective p s hm hu.1 ht (hu.2.trans he.symm)

theorem delta_step_return_iff (p m s t : ℤ) :
    cellDelta p m (s + t * (m + 1)) = cellDelta p m s ↔ m ∣ t := by
  have h := delta_steps_equal_iff p m s t 0
  simpa only [zero_mul, add_zero, Int.modEq_zero_iff_dvd] using h

theorem delta_first_positive_return (p s : ℤ) {m t : ℤ} (ht : 0 < t) (htm : t < m) :
    cellDelta p m (s + t * (m + 1)) ≠ cellDelta p m s := by
  intro he
  have hd := (delta_step_return_iff p m s t).mp he
  have hz := Int.dvd_iff_emod_eq_zero.mp hd
  rw [Int.emod_eq_of_lt ht.le htm] at hz
  omega

theorem delta_full_period (p m s : ℤ) :
    cellDelta p m (s + m * (m + 1)) = cellDelta p m s :=
  (delta_step_return_iff p m s m).mpr dvd_rfl

end NField.ResetForests.PacketCycles

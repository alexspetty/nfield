/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.PacketWords
/-! # Complete loaded populations and their original source readings -/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.LoadedWords

open scoped BigOperators
open CenteredPhase PhasePopulations NField.Alignment

def loadClocks (p m : ℕ) : Finset ℕ :=
  (retainedClocks p).filter (fun k => packetLoad p k = m)

theorem loaded_lower_upper_disjoint {p m : ℕ} (hm : 0 < m) :
    Disjoint ((lowerWords p m).image (lowerClock p m))
      ((upperWords p m).image (upperClock p m)) := by
  apply Finset.disjoint_left.mpr
  intro k hk hl
  obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hk
  obtain ⟨s, hs, hf⟩ := Finset.mem_image.mp hl
  exact lower_upper_clock_ne hm hm hv hs (he.trans hf.symm)

theorem load_clocks_eq_word_images {p m : ℕ} (hp : p.Prime) (hm : 0 < m) :
    loadClocks p m = (lowerWords p m).image (lowerClock p m) ∪
      (upperWords p m).image (upperClock p m) := by
  ext k
  constructor
  · intro hk
    obtain ⟨hr, hload⟩ := Finset.mem_filter.mp hk
    by_cases hb : lowerBranch p k
    · obtain ⟨hv, he⟩ := retained_lower_word hp hr hb
      rw [hload] at hv he
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_, hv, he⟩)
    · obtain ⟨hs, he⟩ := retained_upper_word hp hr hb
      rw [hload] at hs he
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, hs, he⟩)
  · intro hk
    rcases Finset.mem_union.mp hk with hk | hk
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hk
      exact Finset.mem_filter.mpr ⟨(lower_word_spec hm hv).1, (lower_word_spec hm hv).2.1⟩
    · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hk
      exact Finset.mem_filter.mpr ⟨(upper_word_spec hm hs).1, (upper_word_spec hm hs).2.1⟩

theorem load_clocks_card {p m : ℕ} (hp : p.Prime) (hm : 0 < m) :
    (loadClocks p m).card = (lowerWords p m).card + (upperWords p m).card := by
  rw [load_clocks_eq_word_images hp hm,
    Finset.card_union_of_disjoint (loaded_lower_upper_disjoint hm),
    Finset.card_image_of_injOn (lower_word_injective hm),
    Finset.card_image_of_injOn (upper_word_injective hm)]

theorem distinct_loads_disjoint (p : ℕ) {m n : ℕ} (hmn : m ≠ n) :
    Disjoint (loadClocks p m) (loadClocks p n) := by
  apply Finset.disjoint_left.mpr
  intro k hk hl
  exact hmn ((Finset.mem_filter.mp hk).2.symm.trans (Finset.mem_filter.mp hl).2)

theorem loaded_word_sum {p m : ℕ} (hp : p.Prime) (hm : 0 < m) (q : ℕ → ℝ) :
    (∑ k ∈ loadClocks p m, q k) =
      (∑ v ∈ lowerWords p m, q (lowerClock p m v)) +
      (∑ s ∈ upperWords p m, q (upperClock p m s)) := by
  rw [load_clocks_eq_word_images hp hm,
    Finset.sum_union (loaded_lower_upper_disjoint hm),
    Finset.sum_image (lower_word_injective hm), Finset.sum_image (upper_word_injective hm)]

theorem lower_word_original_source {p m v : ℕ} (hp : p.Prime) (hm : 0 < m)
    (hv : v ∈ lowerWords p m) (a : ℤ) :
    CollisionRampEnergy.boundaryResponse (p - 1) ((a : ℝ) / (lowerClock p m v : ℝ)) =
      CollisionRampEnergy.boundaryResponse v ((a : ℝ) / (lowerClock p m v : ℝ)) := by
  obtain ⟨hk, _, hc, hb⟩ := lower_word_spec hm hv
  obtain ⟨hk2, hkp, _, _⟩ := retained_clock_bounds hk
  have hs := centered_lower_source_integer hp hk2 hkp hb a
  simpa only [hc, Nat.add_sub_cancel] using hs

theorem upper_word_original_source {p m s : ℕ} (hp : p.Prime) (hm : 0 < m)
    (hs : s ∈ upperWords p m) (a : ℤ) :
    CollisionRampEnergy.boundaryResponse (p - 1) ((a : ℝ) / (upperClock p m s : ℝ)) =
      CollisionRampEnergy.boundaryResponse s ((a : ℝ) / (upperClock p m s : ℝ)) := by
  obtain ⟨hk, _, hc, hb⟩ := upper_word_spec hm hs
  obtain ⟨hk2, hkp, _, _⟩ := retained_clock_bounds hk
  have hbranch : upperClock p m s - p % upperClock p m s < p % upperClock p m s :=
    Nat.lt_of_not_ge hb
  have hsource := centered_upper_source_integer hp hk2 hkp hbranch a
  simpa only [hc] using hsource

end NField.ResetForests.LoadedWords

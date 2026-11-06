/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetIntegerCounts
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! # The actual distance from a grid point to an interval modulo integers -/

noncomputable section

namespace NField.Alignment.CommonResetCircleDistance

open scoped BigOperators
open CommonResetIntegerCounts

def intervalTranslates (a b : ℝ) : Set ℝ :=
  {y | ∃ z : ℤ, a+(z : ℝ) ≤ y ∧ y ≤ b+z}

def arcDistance (a b x : ℝ) : ℝ :=
  min (max 0 (Int.fract (x-a)-(b-a))) (1-Int.fract (x-a))

theorem arcDistance_nonneg (a b x : ℝ) : 0 ≤ arcDistance a b x := by
  exact le_min (le_max_left _ _) (by linarith [Int.fract_lt_one (x-a)])

theorem arcDistance_le_iff {a b x r : ℝ} (hab : a ≤ b) (hr : 0 ≤ r) :
    arcDistance a b x ≤ r ↔ ∃ z : ℤ, a+(z : ℝ)-r ≤ x ∧ x ≤ b+z+r := by
  have hfrac0 := Int.fract_nonneg (x-a)
  have hfrac1 := Int.fract_lt_one (x-a)
  have hx : x = a+Int.fract (x-a)+(⌊x-a⌋ : ℝ) := by rw [Int.fract]; ring
  constructor
  · intro h
    rcases min_le_iff.mp h with h|h
    · refine ⟨⌊x-a⌋, ?_, ?_⟩
      · linarith
      · have hh := (le_max_right 0 (Int.fract (x-a)-(b-a))).trans h
        linarith
    · refine ⟨⌊x-a⌋+1, ?_, ?_⟩ <;> push_cast <;> linarith
  · rintro ⟨z, hlo, hhi⟩
    by_cases hz : z ≤ ⌊x-a⌋
    · have hzR : (z : ℝ) ≤ ⌊x-a⌋ := by exact_mod_cast hz
      have he : Int.fract (x-a)-(b-a) ≤ r := by linarith
      exact (min_le_left _ _).trans (max_le hr he)
    · have hzR : (⌊x-a⌋ : ℝ)+1 ≤ z := by exact_mod_cast (show ⌊x-a⌋+1 ≤ z by omega)
      have he : 1-Int.fract (x-a) ≤ r := by linarith
      exact (min_le_right _ _).trans he

/-- Title: `The explicit circular interval distance is the ordinary distance to all integer translates`. -/
theorem arcDistance_eq_infDist {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    arcDistance a b x = Metric.infDist x (intervalTranslates a b) := by
  have hne : (intervalTranslates a b).Nonempty := ⟨a, 0, by simpa using hab⟩
  apply le_antisymm
  · apply (Metric.le_infDist hne).mpr
    intro y hy
    obtain ⟨z, hlo, hhi⟩ := hy
    rw [Real.dist_eq]
    apply (arcDistance_le_iff hab (abs_nonneg _)).mpr
    refine ⟨z, ?_, ?_⟩ <;> linarith [le_abs_self (x-y), neg_le_abs (x-y)]
  · obtain ⟨z, hlo, hhi⟩ := (arcDistance_le_iff hab (arcDistance_nonneg a b x)).mp le_rfl
    by_cases hxa : x < a+z
    · have hmem : a+(z : ℝ) ∈ intervalTranslates a b := ⟨z, le_rfl, by linarith⟩
      have hb := Metric.infDist_le_dist_of_mem (x := x) hmem
      rw [Real.dist_eq, abs_of_neg (by linarith : x-(a+z) < 0)] at hb
      linarith
    · by_cases hxb : b+z < x
      · have hmem : b+(z : ℝ) ∈ intervalTranslates a b := ⟨z, by linarith, le_rfl⟩
        have hb := Metric.infDist_le_dist_of_mem (x := x) hmem
        rw [Real.dist_eq, abs_of_pos (by linarith : 0 < x-(b+z))] at hb
        linarith
      · have hmem : x ∈ intervalTranslates a b := ⟨z, by linarith, by linarith⟩
        have hb := Metric.infDist_le_dist_of_mem (x := x) hmem
        rw [dist_self] at hb
        exact hb.trans (arcDistance_nonneg a b x)

theorem arcDistance_le_half {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    arcDistance a b x ≤ 1/2 := by
  have hr := Int.fract_nonneg (x-a)
  by_cases h : Int.fract (x-a) ≤ b-a
  · unfold arcDistance
    rw [max_eq_left (by linarith)]
    exact (min_le_left _ _).trans (by norm_num)
  · have hleft : arcDistance a b x ≤ Int.fract (x-a)-(b-a) := by
      unfold arcDistance
      rw [max_eq_right (by linarith)]
      exact min_le_left _ _
    have hright : arcDistance a b x ≤ 1-Int.fract (x-a) := min_le_right _ _
    linarith

def nearGrid (u : ℕ) (a b : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range u).filter (fun h : ℕ => arcDistance a b ((h : ℝ)/u) ≤ 1/u)

/-- Title: `The modes within one grid spacing satisfy the published near-slope count`. -/
theorem near_grid_count {u : ℕ} (hu : 0 < u) {a b : ℝ} (hab : a ≤ b) :
    ((nearGrid u a b).card : ℝ) ≤ (u : ℝ)*(b-a)+4 := by
  classical
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have he : nearGrid u a b = translatedArcGrid u (a-1/u) (b+1/u) := by
    ext h
    simp only [nearGrid, translatedArcGrid, Finset.mem_filter]
    constructor
    · rintro ⟨hh, hd⟩
      obtain ⟨z, hz⟩ := (arcDistance_le_iff hab (by positivity : (0 : ℝ) ≤ 1/u)).mp hd
      refine ⟨hh, z, ?_, ?_⟩ <;> linarith [hz.1, hz.2]
    · rintro ⟨hh, z, hz⟩
      refine ⟨hh, (arcDistance_le_iff hab (by positivity : (0 : ℝ) ≤ 1/u)).mpr ⟨z, ?_, ?_⟩⟩ <;>
        linarith [hz.1, hz.2]
  rw [he]
  have hnon : (0 : ℝ) ≤ 1/u := by positivity
  have hb := translated_arc_card hu (show a-1/(u : ℝ) ≤ b+1/u by linarith)
  have heq : (u : ℝ)*((b+1/u)-(a-1/u))+1 = (u : ℝ)*(b-a)+3 := by field_simp; ring
  rw [heq] at hb
  linarith

end NField.Alignment.CommonResetCircleDistance

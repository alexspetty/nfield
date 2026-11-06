/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetCircleDistance
import Mathlib.NumberTheory.Harmonic.Bounds

/-! # Every grid-distance shell and the complete reciprocal-distance sum -/

noncomputable section

namespace NField.Alignment.CommonResetGridDistances

open scoped BigOperators
open CommonResetCircleDistance CommonResetIntegerCounts

def shellGrid (u : ℕ) (a b : ℝ) (k : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range u).filter (fun h : ℕ =>
    (k : ℝ)/u ≤ arcDistance a b ((h : ℝ)/u) ∧ arcDistance a b ((h : ℝ)/u) ≤ (k+1 : ℝ)/u)

theorem distance_shell_arcs {a b x lo hi : ℝ} (hlo : 0 < lo)
    (hdlo : lo ≤ arcDistance a b x) (hdhi : arcDistance a b x ≤ hi) :
    (∃ z : ℤ, b+lo+z ≤ x ∧ x ≤ b+hi+z) ∨
      (∃ z : ℤ, a-hi+z ≤ x ∧ x ≤ a-lo+z) := by
  have hx : x = a+Int.fract (x-a)+(⌊x-a⌋ : ℝ) := by rw [Int.fract]; ring
  have hdpos : 0 < arcDistance a b x := hlo.trans_le hdlo
  have hfrac : 0 < Int.fract (x-a)-(b-a) := by
    have hh : 0 < max 0 (Int.fract (x-a)-(b-a)) := hdpos.trans_le (min_le_left _ _)
    simpa only [lt_max_iff, lt_irrefl, false_or] using hh
  have hd : arcDistance a b x =
      min (Int.fract (x-a)-(b-a)) (1-Int.fract (x-a)) := by
    unfold arcDistance
    rw [max_eq_right hfrac.le]
  rcases le_total (Int.fract (x-a)-(b-a)) (1-Int.fract (x-a)) with h|h
  · rw [min_eq_left h] at hd
    exact Or.inl ⟨⌊x-a⌋, by linarith, by linarith⟩
  · rw [min_eq_right h] at hd
    refine Or.inr ⟨⌊x-a⌋+1, ?_, ?_⟩ <;> push_cast <;> linarith

/-- Title: `Each positive distance shell contains at most four Fourier grid points`. -/
theorem distance_shell_count {u k : ℕ} (hu : 0 < u) (hk : 1 ≤ k) (a b : ℝ) :
    ((shellGrid u a b k).card : ℝ) ≤ 4 := by
  classical
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  let R := translatedArcGrid u (b+(k : ℝ)/u) (b+(k+1 : ℝ)/u)
  let L := translatedArcGrid u (a-(k+1 : ℝ)/u) (a-(k : ℝ)/u)
  have hsub : shellGrid u a b k ⊆ R ∪ L := by
    intro h hh
    have hm := Finset.mem_filter.mp hh
    have ha := distance_shell_arcs (div_pos hkR huR) hm.2.1 hm.2.2
    rcases ha with ha|ha
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hm.1, ha⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hm.1, ha⟩))
  have hstep : (k : ℝ)/u ≤ (k+1 : ℝ)/u := div_le_div_of_nonneg_right (by linarith) huR.le
  have hR := translated_arc_card hu (show b+(k : ℝ)/u ≤ b+(k+1 : ℝ)/u by linarith)
  have hL := translated_arc_card hu (show a-(k+1 : ℝ)/u ≤ a-(k : ℝ)/u by linarith)
  have hr : (u : ℝ)*((b+(k+1 : ℝ)/u)-(b+(k : ℝ)/u))+1 = 2 := by field_simp; ring
  have hl : (u : ℝ)*((a-(k : ℝ)/u)-(a-(k+1 : ℝ)/u))+1 = 2 := by field_simp; ring
  rw [hr] at hR
  rw [hl] at hL
  have hc : ((shellGrid u a b k).card : ℝ) ≤ (R.card : ℝ)+L.card := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  exact hc.trans (by dsimp [R, L]; linarith)

def farGrid (u : ℕ) (a b : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range u).filter (fun h : ℕ => 1/(u : ℝ) < arcDistance a b ((h : ℝ)/u))

/-- Title: `All distant Fourier slopes have the complete four-harmonic reciprocal bound`. -/
theorem distant_grid_sum {u : ℕ} (hu : 0 < u) {a b : ℝ} (hab : a ≤ b) :
    (∑ h ∈ farGrid u a b, 1/arcDistance a b ((h : ℝ)/u)) ≤
      4*(u : ℝ)*(harmonic u : ℝ) := by
  classical
  let S := farGrid u a b
  let d (h : ℕ) : ℝ := arcDistance a b ((h : ℝ)/u)
  let label (h : ℕ) : ℕ := ⌊(u : ℝ)*d h⌋₊
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hdpos (h : ℕ) (hh : h ∈ S) : 0 < d h :=
    (one_div_pos.mpr huR).trans (Finset.mem_filter.mp hh).2
  have hmaps (h : ℕ) (hh : h ∈ S) : label h ∈ Finset.Icc 1 u := by
    have hhpos := hdpos h hh
    have hsmall := arcDistance_le_half hab ((h : ℝ)/u)
    have hd1 := (Finset.mem_filter.mp hh).2
    apply Finset.mem_Icc.mpr
    constructor
    · apply (Nat.one_le_floor_iff _).mpr
      have hh' := (div_lt_iff₀ huR).mp hd1
      dsimp [d] at hh' ⊢
      nlinarith
    · apply Nat.floor_le_of_le
      change (u : ℝ)*arcDistance a b ((h : ℝ)/u) ≤ u
      nlinarith
  have hsplit : (∑ h ∈ S, 1/d h) =
      ∑ k ∈ Finset.Icc 1 u, ∑ h ∈ S.filter (fun h => label h=k), 1/d h :=
    (Finset.sum_fiberwise_of_maps_to hmaps (fun h => 1/d h)).symm
  have hfiber (k : ℕ) (hk : k ∈ Finset.Icc 1 u) :
      (∑ h ∈ S.filter (fun h => label h=k), 1/d h) ≤ 4*(u : ℝ)/k := by
    let F := S.filter (fun h => label h=k)
    have hkR : (0 : ℝ) < k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
    have hfloor (h : ℕ) (hh : h ∈ F) :
        (k : ℝ) ≤ (u : ℝ)*d h ∧ (u : ℝ)*d h < k+1 := by
      have hs := Finset.mem_filter.mp hh
      have hn : 0 ≤ (u : ℝ)*d h := mul_nonneg huR.le (hdpos h hs.1).le
      have h1 := Nat.floor_le hn
      have h2 := Nat.lt_floor_add_one ((u : ℝ)*d h)
      have hlab : label h=k := hs.2
      change (label h : ℝ) ≤ (u : ℝ)*d h at h1
      change (u : ℝ)*d h < (label h : ℝ)+1 at h2
      rw [hlab] at h1 h2
      exact ⟨h1, h2⟩
    have hsub : F ⊆ shellGrid u a b k := by
      intro h hh
      have hp := hfloor h hh
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hh).1).1,
        (div_le_iff₀ huR).mpr (by nlinarith), (le_div_iff₀ huR).mpr (by nlinarith)⟩
    have hc : (F.card : ℝ) ≤ 4 :=
      (show (F.card : ℝ) ≤ (shellGrid u a b k).card by exact_mod_cast Finset.card_le_card hsub).trans
        (distance_shell_count hu (Finset.mem_Icc.mp hk).1 a b)
    calc
      _ ≤ ∑ _h ∈ F, (u : ℝ)/k := by
        apply Finset.sum_le_sum
        intro h hh
        apply (div_le_div_iff₀ (hdpos h (Finset.mem_filter.mp hh).1) hkR).mpr
        simpa only [one_mul] using (hfloor h hh).1
      _ = (F.card : ℝ)*((u : ℝ)/k) := by simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 4*((u : ℝ)/k) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = _ := by ring
  change (∑ h ∈ S, 1/d h) ≤ _
  rw [hsplit]
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 u, 4*(u : ℝ)/k := Finset.sum_le_sum hfiber
    _ = 4*(u : ℝ)*(harmonic u : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring

end NField.Alignment.CommonResetGridDistances

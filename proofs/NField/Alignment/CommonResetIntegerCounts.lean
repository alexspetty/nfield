/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetDerivativeSmooth
import Mathlib.Data.Int.Interval

/-! # Integer counts for separated slopes and translated grid arcs -/

noncomputable section

namespace NField.Alignment.CommonResetIntegerCounts

open scoped BigOperators

theorem integer_card_bound (S : Finset ℤ) {A B : ℝ}
    (hS : ∀ n ∈ S, A ≤ (n : ℝ) ∧ (n : ℝ) ≤ B) :
    (S.card : ℝ) ≤ max 0 (B-A+1) := by
  classical
  by_cases he : S.Nonempty
  · let lo := S.min' he
    let hi := S.max' he
    have hl := hS lo (S.min'_mem he)
    have hh := hS hi (S.max'_mem he)
    have horder : lo ≤ hi := S.min'_le hi (S.max'_mem he)
    have hsub : S ⊆ Finset.Icc lo hi := by
      intro n hn
      exact Finset.mem_Icc.mpr ⟨S.min'_le n hn, S.le_max' n hn⟩
    have hc := Finset.card_le_card hsub
    rw [Int.card_Icc] at hc
    have hnon : 0 ≤ hi+1-lo := by omega
    have hcR : (S.card : ℝ) ≤ (hi : ℝ)+1-lo := by
      have hcI : (S.card : ℤ) ≤ hi+1-lo := by
        have hcI : (S.card : ℤ) ≤ ((hi+1-lo).toNat : ℤ) := by exact_mod_cast hc
        simpa only [Int.toNat_of_nonneg hnon] using hcI
      exact_mod_cast hcI
    exact hcR.trans ((by linarith : (hi : ℝ)+1-lo ≤ B-A+1).trans (le_max_right _ _))
  · simp only [Finset.not_nonempty_iff_eq_empty.mp he, Finset.card_empty, Nat.cast_zero,
      le_max_iff, le_refl, true_or]

theorem natural_span_card_bound (S : Finset ℕ) (he : S.Nonempty) :
    (S.card : ℝ) ≤ (S.max' he : ℝ)-(S.min' he : ℝ)+1 := by
  classical
  have hs : S ⊆ Finset.Icc (S.min' he) (S.max' he) := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨S.min'_le n hn, S.le_max' n hn⟩
  have hc := Finset.card_le_card hs
  rw [Nat.card_Icc] at hc
  have hl : S.min' he ≤ S.max' he+1 := (S.min'_le _ (S.max'_mem he)).trans (Nat.le_succ _)
  have hreal : (S.card : ℝ) ≤ (S.max' he : ℝ)+1-S.min' he := by
    exact_mod_cast hc
  linarith

/-- Title: `Separated sampled slopes have the exact interval cardinality bound`. -/
theorem separated_slope_card_bound (S : Finset ℕ) (g : ℕ → ℝ) {lam A B : ℝ}
    (hlam : 0 < lam) (hrange : ∀ i ∈ S, A ≤ g i ∧ g i ≤ B)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≤ j → lam*((j : ℝ)-i) ≤ g j-g i) :
    (S.card : ℝ) ≤ max 0 ((B-A)/lam+1) := by
  classical
  by_cases he : S.Nonempty
  · have hs := hsep (S.min' he) (S.min'_mem he) (S.max' he) (S.max'_mem he)
      (S.min'_le _ (S.max'_mem he))
    have hl := (hrange _ (S.min'_mem he)).1
    have hh := (hrange _ (S.max'_mem he)).2
    have hb : (S.max' he : ℝ)-(S.min' he : ℝ) ≤ (B-A)/lam :=
      (le_div_iff₀ hlam).mpr (by nlinarith)
    have hbound : (S.max' he : ℝ)-(S.min' he : ℝ)+1 ≤ (B-A)/lam+1 := by linarith
    exact (natural_span_card_bound S he).trans (hbound.trans (le_max_right _ _))
  · simp only [Finset.not_nonempty_iff_eq_empty.mp he, Finset.card_empty, Nat.cast_zero,
      le_max_iff, le_refl, true_or]

def translatedArcGrid (u : ℕ) (a b : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range u).filter (fun h => ∃ z : ℤ, a+(z : ℝ) ≤ (h : ℝ)/u ∧ (h : ℝ)/u ≤ b+z)

/-- Title: `Every translated closed arc contains at most its grid length plus one points`. -/
theorem translated_arc_card {u : ℕ} (hu : 0 < u) {a b : ℝ} (hab : a ≤ b) :
    ((translatedArcGrid u a b).card : ℝ) ≤ (u : ℝ)*(b-a)+1 := by
  classical
  let S := translatedArcGrid u a b
  have hw (h : ℕ) (hh : h ∈ S) :
      ∃ z : ℤ, a+(z : ℝ) ≤ (h : ℝ)/u ∧ (h : ℝ)/u ≤ b+z :=
    (Finset.mem_filter.mp hh).2
  let z (h : ℕ) : ℤ := if hh : h ∈ S then Classical.choose (hw h hh) else 0
  let lift (h : ℕ) : ℤ := (h : ℤ)-(u : ℤ)*z h
  have hz (h : ℕ) (hh : h ∈ S) : a+(z h : ℝ) ≤ (h : ℝ)/u ∧ (h : ℝ)/u ≤ b+z h := by
    dsimp [z]
    rw [dif_pos hh]
    exact Classical.choose_spec (hw h hh)
  have hmod (h : ℕ) (hh : h ∈ S) : lift h % (u : ℤ) = h := by
    have hlt : h < u := Finset.mem_range.mp (Finset.mem_filter.mp hh).1
    dsimp [lift]
    rw [Int.sub_mul_emod_self_left]
    exact Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hlt)
  have hinj : Set.InjOn lift S := by
    intro h hh k hk he
    have hm := congrArg (fun n : ℤ => n%(u : ℤ)) he
    rw [hmod h hh, hmod k hk] at hm
    exact_mod_cast hm
  have hbnd : ∀ n ∈ S.image lift, (u : ℝ)*a ≤ (n : ℝ) ∧ (n : ℝ) ≤ (u : ℝ)*b := by
    intro n hn
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hn
    have hzz := hz h hh
    have huR : (0 : ℝ) < u := by exact_mod_cast hu
    have hlo := (le_div_iff₀ huR).mp hzz.1
    have hhi := (div_le_iff₀ huR).mp hzz.2
    dsimp [lift]
    push_cast
    constructor <;> nlinarith
  have hcount := integer_card_bound (S.image lift) hbnd
  rw [Finset.card_image_iff.mpr hinj] at hcount
  have hpos : (0 : ℝ) ≤ (u : ℝ)*b-(u : ℝ)*a+1 := by
    have : 0 ≤ (u : ℝ)*(b-a) := mul_nonneg (by positivity) (sub_nonneg.mpr hab)
    linarith
  rw [max_eq_right hpos] at hcount
  dsimp [S] at hcount
  nlinarith

end NField.Alignment.CommonResetIntegerCounts

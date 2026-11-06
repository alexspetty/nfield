/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionCharacterLValueEnclosure

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.CollisionCotangentSeriesEnclosure
open scoped BigOperators
open CollisionCotangentSeries CollisionFiniteSineTransform CollisionComplexSeriesEnclosure
open CollisionHarmonicRootSeries CollisionFourierEnclosure

def cotangentPrefix (q N : ℕ) : ℝ := ∑ n∈Finset.range (N+1),cotangentTerm q n
def unitCotangentPrefix (q N : ℕ) : ℝ := ∑ n∈Finset.range (N+1),unitCotangentTerm q n

theorem cotangent_residue_majorant {q : ℕ} (hq : 0<q) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ a : ℕ, 0<a → a<q → |Real.cot (Real.pi*(a : ℝ)/(q : ℝ))| ≤ B)
    (n : ℕ) : ‖cotangentTerm q n‖ ≤ B/(n : ℝ)^2 := by
  by_cases hd : q∣n
  · simp only [cotangentTerm,if_pos hd,norm_zero]
    positivity
  · have hm : 0<n%q := Nat.pos_of_ne_zero (fun h => hd (Nat.dvd_of_mod_eq_zero h))
    have ha := hb (n%q) hm (Nat.mod_lt n hq)
    rw [cotangent_mod hq n] at ha
    rw [cotangentTerm,if_neg hd,norm_div,norm_pow,Real.norm_natCast,Real.norm_eq_abs]
    exact div_le_div_of_nonneg_right ha (sq_nonneg _)

theorem unit_cotangent_residue_majorant {q : ℕ} (hq : 0<q) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ a : ℕ, 0<a → a<q → a.Coprime q →
      |Real.cot (Real.pi*(a : ℝ)/(q : ℝ))| ≤ B) (n : ℕ) :
    ‖unitCotangentTerm q n‖ ≤ B/(n : ℝ)^2 := by
  by_cases hc : n.Coprime q
  · rw [unitCotangentTerm,if_pos hc]
    by_cases hd : q∣n
    · simp only [cotangentTerm,if_pos hd,norm_zero]
      positivity
    · have hm : 0<n%q := Nat.pos_of_ne_zero (fun h => hd (Nat.dvd_of_mod_eq_zero h))
      have ha := hb (n%q) hm (Nat.mod_lt n hq) (by simpa using hc)
      rw [cotangent_mod hq n] at ha
      rw [cotangentTerm,if_neg hd,norm_div,norm_pow,Real.norm_natCast,Real.norm_eq_abs]
      exact div_le_div_of_nonneg_right ha (sq_nonneg _)
  · simp only [unitCotangentTerm,if_neg hc,norm_zero]
    positivity

theorem bounded_reciprocal_square_tail {f : ℕ → ℝ} (hf : Summable f)
    {N : ℕ} (hN : 1 ≤ N) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ n, ‖f n‖ ≤ B/(n : ℝ)^2) :
    |(∑' n,f n)-(∑ n∈Finset.range (N+1),f n)| ≤ B/(N : ℝ) := by
  have hg := (inverseSquare_summable.comp_injective
    (show Function.Injective (fun n : ℕ => n+N+1) from fun a b h => by dsimp at h; omega)).mul_left B
  apply real_series_tail_bound hf N hg
    (fun n => by simpa only [mul_one_div,Function.comp_def] using hb (n+N+1))
  rw [tsum_mul_left]
  simpa only [mul_one_div,Function.comp_def] using mul_le_mul_of_nonneg_left (reciprocal_square_tail hN) hB

theorem cotangent_tail {q N : ℕ} (hq : 0<q) (hN : 1 ≤ N) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ a : ℕ, 0<a → a<q → |Real.cot (Real.pi*(a : ℝ)/(q : ℝ))| ≤ B) :
    |cotangentSum q-cotangentPrefix q N| ≤ B/(N : ℝ) :=
  bounded_reciprocal_square_tail (cotangentTerm_summable hq) hN hB
    (cotangent_residue_majorant hq hB hb)

theorem unit_cotangent_tail {q N : ℕ} (hq : 0<q) (hN : 1 ≤ N) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ a : ℕ, 0<a → a<q → a.Coprime q →
      |Real.cot (Real.pi*(a : ℝ)/(q : ℝ))| ≤ B) :
    |unitCotangentSum q-unitCotangentPrefix q N| ≤ B/(N : ℝ) :=
  bounded_reciprocal_square_tail (unitCotangentTerm_summable hq) hN hB
    (unit_cotangent_residue_majorant hq hB hb)

theorem cotangent_full_enclosure {q N : ℕ} (hq : 0<q) (hN : 1 ≤ N) {B l u : ℝ}
    (hB : 0 ≤ B)
    (hb : ∀ a : ℕ, 0<a → a<q → |Real.cot (Real.pi*(a : ℝ)/(q : ℝ))| ≤ B)
    (hp : l ≤ cotangentPrefix q N ∧ cotangentPrefix q N ≤ u) :
    l-B/(N : ℝ) ≤ cotangentSum q ∧ cotangentSum q ≤ u+B/(N : ℝ) :=
  real_error_interval hp (cotangent_tail hq hN hB hb)

theorem unit_cotangent_full_enclosure {q N : ℕ} (hq : 0<q) (hN : 1 ≤ N) {B l u : ℝ}
    (hB : 0 ≤ B)
    (hb : ∀ a : ℕ, 0<a → a<q → a.Coprime q →
      |Real.cot (Real.pi*(a : ℝ)/(q : ℝ))| ≤ B)
    (hp : l ≤ unitCotangentPrefix q N ∧ unitCotangentPrefix q N ≤ u) :
    l-B/(N : ℝ) ≤ unitCotangentSum q ∧ unitCotangentSum q ≤ u+B/(N : ℝ) :=
  real_error_interval hp (unit_cotangent_tail hq hN hB hb)

theorem cotangent_prefix_one (N : ℕ) : cotangentPrefix 1 N=0 ∧ unitCotangentPrefix 1 N=0 := by
  simp [cotangentPrefix,unitCotangentPrefix,unitCotangentTerm]

theorem residue_endpoint_bound {x l u B : ℝ} (hx : l ≤ x ∧ x ≤ u)
    (hl : |l| ≤ B) (hu : |u| ≤ B) : |x| ≤ B := by
  exact abs_le.mpr ⟨(abs_le.mp hl).1.trans hx.1,hx.2.trans (abs_le.mp hu).2⟩

end NField.Alignment.CollisionCotangentSeriesEnclosure

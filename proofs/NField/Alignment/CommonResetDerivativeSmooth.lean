/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetDerivativeFirst

/-! # Smooth derivatives imply the actual sampled increment bounds -/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CommonResetDerivativeSmooth

open scoped BigOperators
open Set CommonResetDerivativeFirst

def sample (f : ℝ → ℝ) (a : ℝ) (i : ℕ) : ℝ := f (a+(i : ℝ))

theorem increment_witness (f g : ℝ → ℝ) (a : ℝ) (N i : ℕ) (hi : i < N)
    (hf : ContinuousOn f (Icc a (a+N)))
    (hfg : ∀ x ∈ Ioo a (a+N), HasDerivAt f (g x) x) :
    ∃ c ∈ Ioo (a+(i : ℝ)) (a+(i : ℝ)+1), g c = increment (sample f a) i := by
  have hiR : (i : ℝ)+1 ≤ N := by exact_mod_cast hi
  have hsub : Icc (a+(i : ℝ)) (a+(i : ℝ)+1) ⊆ Icc a (a+N) := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2, (show (0 : ℝ) ≤ i by positivity)]
  have hderiv : ∀ x ∈ Ioo (a+(i : ℝ)) (a+(i : ℝ)+1), HasDerivAt f (g x) x := by
    intro x hx
    apply hfg x
    constructor <;> linarith [hx.1, hx.2, (show (0 : ℝ) ≤ i by positivity)]
  obtain ⟨c, hc, he⟩ := exists_hasDerivAt_eq_slope f g (by linarith : a+(i : ℝ) < a+(i : ℝ)+1)
    (hf.mono hsub) hderiv
  refine ⟨c, hc, ?_⟩
  rw [show a+(i : ℝ)+1-(a+(i : ℝ)) = 1 by ring, div_one] at he
  simpa only [increment, sample, Nat.cast_add, Nat.cast_one, add_assoc,
    add_sub_cancel_left, div_one] using he

theorem increment_witness_mem (a : ℝ) (N i : ℕ) (hi : i < N) {c : ℝ}
    (hc : c ∈ Ioo (a+(i : ℝ)) (a+(i : ℝ)+1)) : c ∈ Ioo a (a+N) := by
  have hiR : (i : ℝ)+1 ≤ N := by exact_mod_cast hi
  constructor <;> linarith [hc.1, hc.2, (show (0 : ℝ) ≤ i by positivity)]

theorem increments_monotone (f g : ℝ → ℝ) (a : ℝ) (N : ℕ)
    (hf : ContinuousOn f (Icc a (a+N)))
    (hfg : ∀ x ∈ Ioo a (a+N), HasDerivAt f (g x) x)
    (hg : MonotoneOn g (Icc a (a+N))) :
    ∀ i j, i ≤ j → j < N → increment (sample f a) i ≤ increment (sample f a) j := by
  intro i j hij hj
  rcases eq_or_lt_of_le hij with rfl|hij
  · exact le_rfl
  · obtain ⟨x, hx, he⟩ := increment_witness f g a N i (by omega) hf hfg
    obtain ⟨y, hy, hf'⟩ := increment_witness f g a N j hj hf hfg
    rw [← he, ← hf']
    apply hg (Ioo_subset_Icc_self (increment_witness_mem a N i (by omega) hx))
      (Ioo_subset_Icc_self (increment_witness_mem a N j hj hy))
    have hijR : (i : ℝ)+1 ≤ j := by exact_mod_cast hij
    linarith [hx.2, hy.1]

theorem increments_antitone (f g : ℝ → ℝ) (a : ℝ) (N : ℕ)
    (hf : ContinuousOn f (Icc a (a+N)))
    (hfg : ∀ x ∈ Ioo a (a+N), HasDerivAt f (g x) x)
    (hg : AntitoneOn g (Icc a (a+N))) :
    ∀ i j, i ≤ j → j < N → increment (sample f a) j ≤ increment (sample f a) i := by
  intro i j hij hj
  rcases eq_or_lt_of_le hij with rfl|hij
  · exact le_rfl
  · obtain ⟨x, hx, he⟩ := increment_witness f g a N i (by omega) hf hfg
    obtain ⟨y, hy, hf'⟩ := increment_witness f g a N j hj hf hfg
    rw [← he, ← hf']
    apply hg (Ioo_subset_Icc_self (increment_witness_mem a N i (by omega) hx))
      (Ioo_subset_Icc_self (increment_witness_mem a N j hj hy))
    have hijR : (i : ℝ)+1 ≤ j := by exact_mod_cast hij
    linarith [hx.2, hy.1]

/-- Title: `A monotone derivative between consecutive integers gives the first-derivative estimate`. -/
theorem first_derivative_bound (f g : ℝ → ℝ) (a : ℝ) (N : ℕ) (m : ℤ) (d : ℝ)
    (hd : 0 < d) (hdh : d ≤ 1/2)
    (hf : ContinuousOn f (Icc a (a+N)))
    (hfg : ∀ x ∈ Ioo a (a+N), HasDerivAt f (g x) x)
    (hg : MonotoneOn g (Icc a (a+N)) ∨ AntitoneOn g (Icc a (a+N)))
    (hstrip : ∀ x ∈ Ioo a (a+N), (m : ℝ)+d ≤ g x ∧ g x ≤ (m : ℝ)+1-d) :
    ‖∑ i ∈ Finset.range (N+1), phase (f (a+(i : ℝ)))‖ ≤ 2/d := by
  apply discrete_first_derivative (sample f a) N m d hd hdh
  · intro i hi
    obtain ⟨c, hc, he⟩ := increment_witness f g a N i hi hf hfg
    rw [← he]
    exact hstrip c (increment_witness_mem a N i hi hc)
  · rcases hg with hg|hg
    · exact Or.inl (increments_monotone f g a N hf hfg hg)
    · exact Or.inr (increments_antitone f g a N hf hfg hg)

/-- Title: `Pointwise curvature controls the derivative over every subinterval`. -/
theorem derivative_variation (g k : ℝ → ℝ) {a b lo hi : ℝ}
    (hg : ContinuousOn g (Icc a b))
    (hgk : ∀ x ∈ Ioo a b, HasDerivAt g (k x) x)
    (hk : ∀ x ∈ Ioo a b, lo ≤ k x ∧ k x ≤ hi)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x ≤ y) :
    lo*(y-x) ≤ g y-g x ∧ g y-g x ≤ hi*(y-x) := by
  rcases eq_or_lt_of_le hxy with rfl|hxy
  · simp
  · have hsub : Icc x y ⊆ Icc a b := by
      intro z hz
      exact ⟨hx.1.trans hz.1, hz.2.trans hy.2⟩
    have hd : ∀ z ∈ Ioo x y, HasDerivAt g (k z) z := by
      intro z hz
      exact hgk z ⟨hx.1.trans_lt hz.1, hz.2.trans_le hy.2⟩
    obtain ⟨z, hz, he⟩ := exists_hasDerivAt_eq_slope g k hxy (hg.mono hsub) hd
    have hbounds := hk z ⟨hx.1.trans_lt hz.1, hz.2.trans_le hy.2⟩
    rw [he] at hbounds
    exact ⟨(le_div_iff₀ (sub_pos.mpr hxy)).mp hbounds.1,
      (div_le_iff₀ (sub_pos.mpr hxy)).mp hbounds.2⟩

theorem derivative_monotone_of_curvature (g k : ℝ → ℝ) {a b lam upper : ℝ}
    (hlam : 0 ≤ lam) (hg : ContinuousOn g (Icc a b))
    (hgk : ∀ x ∈ Ioo a b, HasDerivAt g (k x) x)
    (hk : ∀ x ∈ Ioo a b, lam ≤ k x ∧ k x ≤ upper) : MonotoneOn g (Icc a b) := by
  intro x hx y hy hxy
  have h := (derivative_variation g k hg hgk hk hx hy hxy).1
  have hh := mul_nonneg hlam (sub_nonneg.mpr hxy)
  linarith

/-- Title: `Curvature separates any two sampled increments by their actual index gap`. -/
theorem increment_separation (f g k : ℝ → ℝ) (a : ℝ) (N : ℕ) {lam upper : ℝ}
    (hlam : 0 ≤ lam) (hf : ContinuousOn f (Icc a (a+N)))
    (hfg : ∀ x ∈ Ioo a (a+N), HasDerivAt f (g x) x)
    (hg : ContinuousOn g (Icc a (a+N)))
    (hgk : ∀ x ∈ Ioo a (a+N), HasDerivAt g (k x) x)
    (hk : ∀ x ∈ Ioo a (a+N), lam ≤ k x ∧ k x ≤ upper)
    (i j : ℕ) (hij : i < j) (hj : j < N) :
    lam*((j : ℝ)-(i : ℝ)-1) ≤ increment (sample f a) j-increment (sample f a) i := by
  obtain ⟨x, hx, he⟩ := increment_witness f g a N i (by omega) hf hfg
  obtain ⟨y, hy, hf'⟩ := increment_witness f g a N j hj hf hfg
  have hijR : (i : ℝ)+1 ≤ j := by exact_mod_cast hij
  have hxy : x ≤ y := by linarith [hx.2, hy.1]
  have hv := (derivative_variation g k hg hgk hk
    (Ioo_subset_Icc_self (increment_witness_mem a N i (by omega) hx))
    (Ioo_subset_Icc_self (increment_witness_mem a N j hj hy)) hxy).1
  rw [he, hf'] at hv
  exact (mul_le_mul_of_nonneg_left (by linarith [hx.2, hy.1]) hlam).trans hv

end NField.Alignment.CommonResetDerivativeSmooth

/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetIntegerCounts

/-! # First-derivative cancellation on actual consecutive index subsets -/

noncomputable section

namespace NField.Alignment.CommonResetDerivativeIntervals

open scoped BigOperators
open Set CommonResetDerivativeFirst CommonResetDerivativeSmooth

theorem consecutive_finset_eq_Icc (S : Finset ℕ) (he : S.Nonempty)
    (hconv : ∀ i ∈ S, ∀ j ∈ S, ∀ k, i ≤ k → k ≤ j → k ∈ S) :
    S = Finset.Icc (S.min' he) (S.max' he) := by
  ext k
  constructor
  · intro hk
    exact Finset.mem_Icc.mpr ⟨S.min'_le k hk, S.le_max' k hk⟩
  · intro hk
    exact hconv _ (S.min'_mem he) _ (S.max'_mem he) k
      (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2

theorem natural_sample_mem {a : ℝ} {N i : ℕ} (hi : i ≤ N) :
    a+(i : ℝ) ∈ Icc a (a+N) := by
  have hiR : (i : ℝ) ≤ N := by exact_mod_cast hi
  constructor <;> linarith [show (0 : ℝ) ≤ i by positivity]

/-- Title: `First-derivative cancellation holds on every retained consecutive interval`. -/
theorem first_derivative_on_indices (f g : ℝ → ℝ) (a : ℝ) (N : ℕ)
    (S : Finset ℕ) (m : ℤ) (d : ℝ) (hd : 0 < d) (hdh : d ≤ 1/2)
    (hsub : S ⊆ Finset.range (N+1))
    (hconv : ∀ i ∈ S, ∀ j ∈ S, ∀ k, i ≤ k → k ≤ j → k ∈ S)
    (hf : ContinuousOn f (Icc a (a+N)))
    (hfg : ∀ x ∈ Ioo a (a+N), HasDerivAt f (g x) x)
    (hg : MonotoneOn g (Icc a (a+N)))
    (hstrip : ∀ i ∈ S, (m : ℝ)+d ≤ g (a+i) ∧ g (a+i) ≤ (m : ℝ)+1-d) :
    ‖∑ i ∈ S, phase (f (a+(i : ℝ)))‖ ≤ 2/d := by
  classical
  by_cases he : S.Nonempty
  · let lo := S.min' he
    let hi := S.max' he
    have hlhi : lo ≤ hi := S.min'_le _ (S.max'_mem he)
    have hhiN : hi ≤ N := by
      have h := Finset.mem_range.mp (hsub (S.max'_mem he))
      dsimp [hi]
      omega
    have hloN := hlhi.trans hhiN
    have hcast : ((hi-lo : ℕ) : ℝ) = (hi : ℝ)-lo := Nat.cast_sub hlhi
    have hend : a+(lo : ℝ)+(hi-lo : ℕ) = a+hi := by rw [hcast]; ring
    have hinter : Icc (a+(lo : ℝ)) (a+lo+(hi-lo : ℕ)) ⊆ Icc a (a+N) := by
      rw [hend]
      intro x hx
      exact ⟨(natural_sample_mem hloN).1.trans hx.1, hx.2.trans (natural_sample_mem hhiN).2⟩
    have hderiv : ∀ x ∈ Ioo (a+(lo : ℝ)) (a+lo+(hi-lo : ℕ)), HasDerivAt f (g x) x := by
      rw [hend]
      intro x hx
      apply hfg x
      exact ⟨(natural_sample_mem hloN).1.trans_lt hx.1,
        hx.2.trans_le (natural_sample_mem hhiN).2⟩
    have hstr : ∀ x ∈ Ioo (a+(lo : ℝ)) (a+lo+(hi-lo : ℕ)),
        (m : ℝ)+d ≤ g x ∧ g x ≤ (m : ℝ)+1-d := by
      rw [hend]
      intro x hx
      have hx' : x ∈ Icc a (a+N) := ⟨(natural_sample_mem hloN).1.trans hx.1.le,
        hx.2.le.trans (natural_sample_mem hhiN).2⟩
      exact ⟨(hstrip lo (S.min'_mem he)).1.trans
        (hg (natural_sample_mem hloN) hx' hx.1.le),
        (hg hx' (natural_sample_mem hhiN) hx.2.le).trans (hstrip hi (S.max'_mem he)).2⟩
    have hbound := first_derivative_bound f g (a+lo) (hi-lo) m d hd hdh
      (hf.mono hinter) hderiv (Or.inl (hg.mono hinter)) hstr
    have hsum : (∑ i ∈ S, phase (f (a+(i : ℝ)))) =
        ∑ i ∈ Finset.range (hi-lo+1), phase (f (a+lo+(i : ℝ))) := by
      rw [consecutive_finset_eq_Icc S he hconv]
      change (∑ i ∈ Finset.Icc lo hi, phase (f (a+(i : ℝ)))) = _
      have hset : Finset.Icc lo hi = Finset.Ico lo (hi+1) := by
        ext i
        simp only [Finset.mem_Icc, Finset.mem_Ico]
        omega
      rw [hset, Finset.sum_Ico_eq_sum_range]
      rw [show hi+1-lo=hi-lo+1 by omega]
      apply Finset.sum_congr rfl
      intro i _
      congr 2
      push_cast
      ring
    rw [hsum]
    exact hbound
  · simp only [Finset.not_nonempty_iff_eq_empty.mp he, Finset.sum_empty, norm_zero]
    positivity

end NField.Alignment.CommonResetDerivativeIntervals

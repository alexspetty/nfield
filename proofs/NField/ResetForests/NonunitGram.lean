/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.GramDiagonal
/-! # All nonunit rows, their coherent kernel and their exact trace -/

noncomputable section
set_option autoImplicit false

namespace NField.ResetForests.GramDecomposition

open scoped BigOperators Matrix
open NField.Alignment CommonResetGram SourceMetrics FibreTraces

theorem prime_square_nonunit_iff {p : ℕ} (hp : p.Prime) (a : ℕ) :
    ¬a.Coprime (p^2) ↔ p ∣ a := by
  rw [Nat.coprime_pow_right_iff (by decide : 0 < 2), Nat.coprime_comm,
    hp.coprime_iff_not_dvd, not_not]

def nonunitGram (N p : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => ∑ a : Fin (p^2), if p ∣ a.val then
    samplingMatrix N (p^2) a i*samplingMatrix N (p^2) a j else 0

theorem prime_square_multiples_sum {p : ℕ} (hp : 0 < p) (f : Fin (p^2) → ℝ) :
    (∑ a : Fin (p^2), if p ∣ a.val then f a else 0)=
      ∑ b : Fin p, f ⟨p*b.val,by nlinarith [b.isLt]⟩ := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij
    (fun b _ => (⟨p*b.val,by nlinarith [b.isLt]⟩ : Fin (p^2))) ?_ ?_ ?_ ?_
  · intro b hb
    simp
  · intro b hb c hc he
    apply Fin.ext
    have he' := congrArg Fin.val he
    exact Nat.eq_of_mul_eq_mul_left hp he'
  · intro a ha
    have hd : p ∣ a.val := (Finset.mem_filter.mp ha).2
    have hlt : a.val/p < p := (Nat.div_lt_iff_lt_mul hp).mpr (by nlinarith [a.isLt])
    refine ⟨⟨a.val/p,hlt⟩,Finset.mem_univ _,?_⟩
    apply Fin.ext
    exact Nat.mul_div_cancel' hd
  · intro b hb
    rfl

theorem nonunit_gram_entry {p : ℕ} (hp : p.Prime) (N : ℕ) (i j : Fin N) :
    nonunitGram N p i j=∑ a : Fin (p^2),
      if ¬a.val.Coprime (p^2) then
        weightedProfile N (cutoffCoefficients N (Pi.single i 1)) ((a.val : ℝ)/((p^2 : ℕ) : ℝ))*
          weightedProfile N (cutoffCoefficients N (Pi.single j 1)) ((a.val : ℝ)/((p^2 : ℕ) : ℝ))
      else 0 := by
  simp only [nonunitGram, prime_square_nonunit_iff hp, weighted_profile_basis, samplingMatrix]

theorem nonunit_gram_eq_prime_grid {p : ℕ} (hp : 0 < p) (N : ℕ) :
    nonunitGram N p=sampledGram N p := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have harg (b : Fin p) : (((p*b.val : ℕ) : ℝ)/((p^2 : ℕ) : ℝ))=(b.val : ℝ)/(p : ℝ) := by
    push_cast
    field_simp
  ext i j
  rw [nonunitGram, prime_square_multiples_sum hp, sampled_gram_entry]
  apply Finset.sum_congr rfl
  intro b hb
  simp only [samplingMatrix, weighted_profile_basis, harg]

theorem nonunit_gram_annihilates_complete {p : ℕ} (hp : p.Prime) :
    nonunitGram (p-1) p *ᵥ (fun _ => (1 : ℝ))=0 := by
  have hz : samplingMatrix (p-1) p *ᵥ (fun _ => (1 : ℝ))=0 := by
    funext b
    rw [sampling_matrix_reading, cutoff_complete_profile, coherent_prime_grid_zero hp]
    rfl
  rw [nonunit_gram_eq_prime_grid hp.pos, sampledGram, ← Matrix.mulVec_mulVec, hz,
    Matrix.mulVec_zero]

theorem nonunit_gram_trace {p : ℕ} (hp : p.Prime) :
    Matrix.trace (nonunitGram (p-1) p)=
      ((p-1 : ℕ) : ℝ)^2*((p : ℝ)-2)/(3*(p : ℝ)) := by
  rw [nonunit_gram_eq_prime_grid hp.pos, sampled_gram_trace hp.two_le]
  · rw [Nat.cast_sub hp.one_le, Nat.cast_one]
    ring
  · intro j hj
    exact (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt
      (Finset.mem_Icc.mp hj).1 (by have := hp.two_le; have := (Finset.mem_Icc.mp hj).2; omega))).symm

def offDiagonalSum {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N, if i=j then 0 else A i j

theorem diagonal_and_off_diagonal {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) :
    Matrix.trace A+offDiagonalSum A=∑ i : Fin N, ∑ j : Fin N, A i j := by
  simp only [Matrix.trace, Matrix.diag_apply, offDiagonalSum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hdiag : A i i=∑ j : Fin N, if i=j then A i j else 0 := by simp
  rw [hdiag, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> simp_all

theorem off_diagonal_cancels_trace {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (hz : A *ᵥ (fun _ => (1 : ℝ))=0) : offDiagonalSum A=-Matrix.trace A := by
  have hrows : ∀ i : Fin N, (∑ j : Fin N, A i j)=0 := by
    intro i
    simpa only [Matrix.mulVec, dotProduct, mul_one, Pi.zero_apply] using congrFun hz i
  have h := diagonal_and_off_diagonal A
  simp only [hrows, Finset.sum_const_zero] at h
  linarith

theorem nonunit_off_diagonal_cancellation {p : ℕ} (hp : p.Prime) :
    offDiagonalSum (nonunitGram (p-1) p)=
      -(((p-1 : ℕ) : ℝ)^2*((p : ℝ)-2)/(3*(p : ℝ))) := by
  rw [off_diagonal_cancels_trace _ (nonunit_gram_annihilates_complete hp), nonunit_gram_trace hp]

end NField.ResetForests.GramDecomposition

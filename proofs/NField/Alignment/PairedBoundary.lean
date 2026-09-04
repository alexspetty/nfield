/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimitiveOddBoundaryMean

namespace NField.Alignment.PairedBoundary

open scoped BigOperators ComplexConjugate

noncomputable def imageIndicator
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (f : ι → κ) (x : κ) : ℂ := by
  classical
  exact ∑ i : ι, if f i = x then 1 else 0

noncomputable def pairedBoundary
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (L R : ι → κ) (x : κ) : ℂ :=
  imageIndicator R x - imageIndicator L x

theorem imageIndicator_eq_one_or_zero
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (f : ι → κ) (hf : Function.Injective f) (x : κ) :
    imageIndicator f x = if ∃ i, f i = x then 1 else 0 := by
  classical
  unfold imageIndicator
  by_cases h : ∃ i, f i = x
  · obtain ⟨i, hi⟩ := h
    rw [if_pos ⟨i, hi⟩]
    rw [Finset.sum_eq_single i]
    · simp [hi]
    · intro j _ hji
      have hne : f j ≠ x := by
        intro hj
        exact hji (hf (hj.trans hi.symm))
      simp [hne]
    · simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro i _
    have hne : f i ≠ x := fun hi => h ⟨i, hi⟩
    simp [hne]

theorem sum_imageIndicator
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (f : ι → κ) :
    ∑ x : κ, imageIndicator f x = (Fintype.card ι : ℂ) := by
  classical
  unfold imageIndicator
  rw [Finset.sum_comm]
  calc
    (∑ i : ι, ∑ x : κ, if f i = x then (1 : ℂ) else 0) =
      ∑ _i : ι, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro i _
        simp
    _ = _ := by simp

theorem pairedBoundary_normSq_sum
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (L R : ι → κ) (hL : Function.Injective L)
    (hR : Function.Injective R)
    (hdisjoint : ∀ i j, L i ≠ R j) :
    ∑ x : κ, ‖pairedBoundary L R x‖ ^ 2 =
      2 * Fintype.card ι := by
  classical
  have hpoint (x : κ) :
      ‖pairedBoundary L R x‖ ^ 2 =
        (imageIndicator R x + imageIndicator L x).re := by
    unfold pairedBoundary
    rw [imageIndicator_eq_one_or_zero R hR,
      imageIndicator_eq_one_or_zero L hL]
    by_cases hRx : ∃ i, R i = x
    · have hnotL : ¬∃ j, L j = x := by
        rintro ⟨j, hj⟩
        obtain ⟨i, hi⟩ := hRx
        exact hdisjoint j i (hj.trans hi.symm)
      simp [hRx, hnotL]
    · by_cases hLx : ∃ i, L i = x
      · simp [hRx, hLx]
      · simp [hRx, hLx]
  simp_rw [hpoint]
  rw [← Complex.re_sum]
  simp_rw [Finset.sum_add_distrib]
  rw [sum_imageIndicator, sum_imageIndicator]
  norm_num [Complex.mul_re]
  ring

theorem pairedBoundary_fiber_balance
    {ι κ ρtype : Type*} [Fintype ι] [Fintype κ]
    [Fintype ρtype] [DecidableEq κ] [DecidableEq ρtype]
    (L R : ι → κ) (ρ : κ → ρtype)
    (hpair : ∀ i, ρ (L i) = ρ (R i)) (r : ρtype) :
    ∑ x : κ with ρ x = r, pairedBoundary L R x = 0 := by
  classical
  unfold pairedBoundary imageIndicator
  have hside (f : ι → κ) :
      (∑ x : κ with ρ x = r, ∑ i : ι, if f i = x then (1 : ℂ) else 0) =
        ∑ i : ι, if ρ (f i) = r then 1 else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hri : ρ (f i) = r
    · rw [if_pos hri]
      rw [Finset.sum_eq_single (f i)]
      · simp
      · intro x hx hne
        simp [Ne.symm hne]
      · intro hnot
        exact (hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hri⟩)).elim
    · rw [if_neg hri]
      apply Finset.sum_eq_zero
      intro x hx
      have hne : f i ≠ x := by
        intro heq
        apply hri
        rw [heq]
        exact (Finset.mem_filter.mp hx).2
      simp [hne]
  rw [Finset.sum_sub_distrib, hside, hside]
  have heq :
      (∑ i : ι, if ρ (R i) = r then (1 : ℂ) else 0) =
        ∑ i : ι, if ρ (L i) = r then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hpair]
  rw [heq, sub_self]

theorem imageIndicator_neg_reindex
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] [InvolutiveNeg κ]
    (L R : ι → κ) (σ : ι ≃ ι)
    (hneg : ∀ i, -R i = L (σ i)) (x : κ) :
    imageIndicator R (-x) = imageIndicator L x := by
  classical
  unfold imageIndicator
  calc
    (∑ i : ι, if R i = -x then (1 : ℂ) else 0) =
      ∑ i : ι, if -R i = x then (1 : ℂ) else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        have hiff : R i = -x ↔ -R i = x := by
          constructor
          · intro hi
            rw [hi]
            simp
          · intro hi
            have h := congrArg Neg.neg hi
            simpa using h
        by_cases hi : R i = -x
        · rw [if_pos hi, if_pos (hiff.mp hi)]
        · rw [if_neg hi, if_neg (fun h => hi (hiff.mpr h))]
    _ = ∑ i : ι, if L (σ i) = x then (1 : ℂ) else 0 := by
      simp_rw [hneg]
    _ = ∑ j : ι, if L j = x then (1 : ℂ) else 0 := by
      exact Equiv.sum_comp σ (fun j => if L j = x then (1 : ℂ) else 0)

theorem pairedBoundary_odd
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] [InvolutiveNeg κ]
    (L R : ι → κ) (σ τ : ι ≃ ι)
    (hnegR : ∀ i, -R i = L (σ i))
    (hnegL : ∀ i, -L i = R (τ i)) (x : κ) :
    pairedBoundary L R (-x) = -pairedBoundary L R x := by
  unfold pairedBoundary
  rw [imageIndicator_neg_reindex L R σ hnegR,
    imageIndicator_neg_reindex R L τ hnegL]
  ring

end NField.Alignment.PairedBoundary

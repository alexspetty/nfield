/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.FiniteDifferenceEnergy

/-! # Summing the off-diagonal shift distances -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.FiniteDifferenceRows
open scoped BigOperators ComplexConjugate
open FiniteDifferenceEnergy

theorem left_distances (B : ℕ → ℝ) (h : ℕ) :
    (∑ k ∈ Finset.range h, B (h-k)) = ∑ d ∈ Finset.Icc 1 h, B d := by
  apply Finset.sum_bij (fun k _ => h-k)
  · intro k hk
    have := Finset.mem_range.mp hk
    simp only [Finset.mem_Icc]
    omega
  · intro k hk l hl he
    have := Finset.mem_range.mp hk
    have := Finset.mem_range.mp hl
    omega
  · intro d hd
    have := Finset.mem_Icc.mp hd
    exact ⟨h-d,Finset.mem_range.mpr (by omega),by omega⟩
  · intro k hk; rfl

theorem right_distances (B : ℕ → ℝ) (h R : ℕ) (hh : h < R) :
    (∑ k ∈ Finset.Ico (h+1) R, B (k-h)) =
      ∑ d ∈ Finset.Icc 1 (R-h-1), B d := by
  apply Finset.sum_bij (fun k _ => k-h)
  · intro k hk
    have := Finset.mem_Ico.mp hk
    simp only [Finset.mem_Icc]
    omega
  · intro k hk l hl he
    have := Finset.mem_Ico.mp hk
    have := Finset.mem_Ico.mp hl
    omega
  · intro d hd
    have := Finset.mem_Icc.mp hd
    exact ⟨d+h,Finset.mem_Ico.mpr ⟨by omega,by omega⟩,by omega⟩
  · intro k hk; rfl

theorem symmetric_row_bound (C : ℕ → ℕ → ℝ) (B : ℕ → ℝ) (D : ℝ)
    (R h : ℕ) (hh : h < R)
    (hB : ∀ d ∈ Finset.Icc 1 R, 0 ≤ B d)
    (hsym : ∀ j k, C j k = C k j) (hdiag : C h h ≤ D)
    (hoff : ∀ j k, k < j → j < R → C j k ≤ B (j-k)) :
    (∑ k ∈ Finset.range R, C h k) ≤ D+2*∑ d ∈ Finset.Icc 1 R, B d := by
  have hl : (∑ k ∈ Finset.range h, C h k) ≤ ∑ d ∈ Finset.Icc 1 R, B d := by
    calc
      _ ≤ ∑ k ∈ Finset.range h, B (h-k) :=
        Finset.sum_le_sum (fun k hk => hoff h k (Finset.mem_range.mp hk) hh)
      _ = ∑ d ∈ Finset.Icc 1 h, B d := left_distances B h
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Icc_subset_Icc_right hh.le) (fun d hd _ => hB d hd)
  have hr : (∑ k ∈ Finset.Ico (h+1) R, C h k) ≤ ∑ d ∈ Finset.Icc 1 R, B d := by
    calc
      _ ≤ ∑ k ∈ Finset.Ico (h+1) R, B (k-h) := by
        apply Finset.sum_le_sum
        intro k hk
        have hk' := Finset.mem_Ico.mp hk
        rw [hsym h k]
        exact hoff k h (by omega) hk'.2
      _ = ∑ d ∈ Finset.Icc 1 (R-h-1), B d := right_distances B h R hh
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Icc_subset_Icc_right (by omega)) (fun d hd _ => hB d hd)
  have hs := Finset.sum_range_add_sum_Ico (f:=fun k => C h k) (by omega : h+1 ≤ R)
  rw [Finset.sum_range_succ] at hs
  linarith

theorem symmetric_matrix_bound (C : ℕ → ℕ → ℝ) (B : ℕ → ℝ) (D : ℝ) (R : ℕ)
    (hB : ∀ d ∈ Finset.Icc 1 R, 0 ≤ B d)
    (hsym : ∀ j k, C j k = C k j) (hdiag : ∀ h < R, C h h ≤ D)
    (hoff : ∀ j k, k < j → j < R → C j k ≤ B (j-k)) :
    (∑ h ∈ Finset.range R, ∑ k ∈ Finset.range R, C h k) ≤
      (R:ℝ)*(D+2*∑ d ∈ Finset.Icc 1 R, B d) := by
  calc
    _ ≤ ∑ _h ∈ Finset.range R, (D+2*∑ d ∈ Finset.Icc 1 R, B d) := by
      apply Finset.sum_le_sum
      intro h hh
      exact symmetric_row_bound C B D R h (Finset.mem_range.mp hh)
        hB hsym (hdiag h (Finset.mem_range.mp hh)) hoff
    _ = _ := by simp; ring

def correlation (f : ℕ → ℂ) (M d : ℕ) : ℂ :=
  ∑ i ∈ Finset.range (M-d), f (i+d)*conj (f i)

theorem difference_energy_bound (f : ℕ → ℂ) (M R : ℕ) (B : ℕ → ℝ)
    (hf : ∀ i < M, ‖f i‖ ≤ 1)
    (hB : ∀ d ∈ Finset.Icc 1 R, 0 ≤ B d)
    (hcorr : ∀ d ∈ Finset.Icc 1 R, ‖correlation f M d‖ ≤ B d) :
    (R:ℝ)^2*‖∑ i ∈ Finset.range M, f i‖^2 ≤
      (M+R:ℕ)*(R:ℝ)*((M:ℝ)+2*∑ d ∈ Finset.Icc 1 R, B d) := by
  let C := fun h k => ‖∑ n ∈ Finset.range (M+R),
    padded f M R (n+h)*conj (padded f M R (n+k))‖
  have hsym (h k : ℕ) : C h k = C k h := by
    dsimp [C]
    rw [← Complex.norm_conj]
    simp only [map_sum,map_mul,starRingEnd_self_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    ring
  have hdiag (h : ℕ) (hh : h < R) : C h h ≤ M := by
    dsimp [C]
    rw [padded_shift_overlap f M R h h (le_refl h) hh.le]
    simp only [Nat.sub_self,Nat.sub_zero,Nat.add_zero]
    calc
      _ ≤ ∑ i ∈ Finset.range M, ‖f i*conj (f i)‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ Finset.range M, (1:ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_mul,Complex.norm_conj]
        exact (mul_le_mul (hf i (Finset.mem_range.mp hi))
          (hf i (Finset.mem_range.mp hi)) (norm_nonneg _) (by norm_num)).trans_eq (by ring)
      _ = _ := by simp
  have hoff (h k : ℕ) (hk : k < h) (hh : h < R) : C h k ≤ B (h-k) := by
    dsimp [C]
    rw [padded_shift_overlap f M R h k hk.le hh.le]
    exact hcorr (h-k) (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)
  have hb := symmetric_matrix_bound C B M R hB hsym hdiag hoff
  apply (padded_shift_energy f M R).trans
  calc
    _ ≤ (M+R:ℕ)*((R:ℝ)*((M:ℝ)+2*∑ d ∈ Finset.Icc 1 R, B d)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

end NField.Alignment.FiniteDifferenceRows

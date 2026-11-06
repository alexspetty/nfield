/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.FejerKernel
import NField.Alignment.RealReciprocalTaylor
import NField.Alignment.FiniteDifferenceRows

/-! # Counting points in a short arc by a positive Fourier polynomial -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.FejerSmallArc
open scoped BigOperators ComplexConjugate
open FejerKernel RealReciprocalTaylor FiniteDifferenceRows

theorem fourier_nat_real (r : ℕ) (t : ℝ) :
    fourier (r:ℤ) (t : AddCircle (1:ℝ)) =
      RealPolynomialMomentBox.realCharacter ((r:ℝ)*t) := by
  change fourier (r:ℤ) (t : AddCircle (1:ℝ)) =
    fourier 1 (((r:ℝ)*t : ℝ) : AddCircle (1:ℝ))
  simp only [fourier_coe_apply]
  congr 1
  push_cast
  ring

theorem kernel_small_arc_lower (H : ℕ) (hH : 1 ≤ H) (t : ℝ)
    (ht : 16*(H:ℝ)*|t| ≤ 1) :
    (H:ℝ)/4 ≤ kernel H (t : AddCircle (1:ℝ)) := by
  have hH0 : (0:ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hterm (r : ℕ) (hr : r ∈ Finset.range H) :
      ‖fourier (r:ℤ) (t : AddCircle (1:ℝ))-1‖ ≤ 1/2 := by
    rw [fourier_nat_real]
    have hb := realCharacter_sub_one_bound ((r:ℝ)*t)
    rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg r)] at hb
    have hrH : (r:ℝ) ≤ H := by exact_mod_cast (Finset.mem_range.mp hr).le
    have hh : 2*Real.pi*((r:ℝ)*|t|) ≤ 8*((H:ℝ)*|t|) := by
      have hp : 2*Real.pi ≤ 8 := by linarith [Real.pi_lt_four]
      exact mul_le_mul hp (mul_le_mul_of_nonneg_right hrH (abs_nonneg t))
        (by positivity) (by norm_num)
    exact hb.trans (hh.trans (by nlinarith))
  have hs : ‖characterSum H (t : AddCircle (1:ℝ))-(H:ℂ)‖ ≤ (H:ℝ)/2 := by
    have he : characterSum H (t : AddCircle (1:ℝ))-(H:ℂ) =
        ∑ r ∈ Finset.range H, (fourier (r:ℤ) (t : AddCircle (1:ℝ))-1) := by
      simp [characterSum,Finset.sum_sub_distrib]
    rw [he]
    calc
      _ ≤ ∑ r ∈ Finset.range H, ‖fourier (r:ℤ) (t : AddCircle (1:ℝ))-1‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _r ∈ Finset.range H, (1/2:ℝ) := Finset.sum_le_sum hterm
      _ = _ := by simp; ring
  have hn : (H:ℝ)/2 ≤ ‖characterSum H (t : AddCircle (1:ℝ))‖ := by
    have hh := norm_le_norm_add_norm_sub (characterSum H (t : AddCircle (1:ℝ))) (H:ℂ)
    rw [Complex.norm_natCast] at hh
    linarith
  unfold kernel
  apply (le_div_iff₀ hH0).mpr
  nlinarith [sq_nonneg (‖characterSum H (t : AddCircle (1:ℝ))‖-(H:ℝ)/2)]

theorem kernel_sample_sum_bound (t : ℕ → AddCircle (1:ℝ)) (M H : ℕ) (hH : 1 ≤ H)
    (B : ℕ → ℝ) (hB : ∀ d ∈ Finset.Icc 1 H, 0 ≤ B d)
    (hsum : ∀ d ∈ Finset.Icc 1 H,
      ‖∑ i ∈ Finset.range M, fourier (d:ℤ) (t i)‖ ≤ B d) :
    (∑ i ∈ Finset.range M, kernel H (t i)) ≤
      (M:ℝ)+2*∑ d ∈ Finset.Icc 1 H, B d := by
  let C : ℕ → ℕ → ℝ := fun r s => ‖∑ i ∈ Finset.range M, fourier ((r:ℤ)-s) (t i)‖
  have hsym (r s : ℕ) : C r s = C s r := by
    have he : (∑ i ∈ Finset.range M, fourier ((s:ℤ)-r) (t i)) =
        conj (∑ i ∈ Finset.range M, fourier ((r:ℤ)-s) (t i)) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← fourier_neg]
      congr 1
      ring
    dsimp only [C]
    rw [he,Complex.norm_conj]
  have hdiag (r : ℕ) (_hr : r < H) : C r r ≤ M := by
    simp [C]
  have hoff (r s : ℕ) (hs : s < r) (hr : r < H) : C r s ≤ B (r-s) := by
    dsimp only [C]
    rw [← Nat.cast_sub hs.le]
    exact hsum (r-s) (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)
  have hm := symmetric_matrix_bound C B M H hB hsym hdiag hoff
  have he : ((∑ i ∈ Finset.range M, kernel H (t i):ℝ):ℂ) =
      (H:ℂ)⁻¹*∑ r ∈ Finset.range H, ∑ s ∈ Finset.range H,
        ∑ i ∈ Finset.range M, fourier ((r:ℤ)-s) (t i) := by
    push_cast
    simp_rw [kernel_expansion]
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.sum_comm]
  have hH0 : (0:ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hn : ‖∑ r ∈ Finset.range H, ∑ s ∈ Finset.range H,
      ∑ i ∈ Finset.range M, fourier ((r:ℤ)-s) (t i)‖ ≤
      (H:ℝ)*((M:ℝ)+2*∑ d ∈ Finset.Icc 1 H, B d) := by
    apply le_trans (norm_sum_le _ _)
    apply le_trans _ hm
    apply Finset.sum_le_sum
    intro r hr
    exact norm_sum_le _ _
  have hnon : 0 ≤ ∑ i ∈ Finset.range M, kernel H (t i) :=
    Finset.sum_nonneg fun i _ => kernel_nonneg H (t i)
  have hh := congrArg norm he
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hnon,norm_mul,norm_inv,
    Complex.norm_natCast] at hh
  rw [hh]
  calc
    _ ≤ (H:ℝ)⁻¹*((H:ℝ)*((M:ℝ)+2*∑ d ∈ Finset.Icc 1 H, B d)) :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    _ = _ := by field_simp

theorem short_arc_count (s : Finset ℕ) (t : ℕ → ℝ) (M H : ℕ)
    (hH : 1 ≤ H) (hs : s ⊆ Finset.range M)
    (hsmall : ∀ i ∈ s, ∃ z : ℤ, 16*(H:ℝ)*|t i-z| ≤ 1)
    (B : ℕ → ℝ) (hB : ∀ d ∈ Finset.Icc 1 H, 0 ≤ B d)
    (hsum : ∀ d ∈ Finset.Icc 1 H,
      ‖∑ i ∈ Finset.range M, fourier (d:ℤ) (t i:AddCircle (1:ℝ))‖ ≤ B d) :
    (s.card:ℝ) ≤ 4/(H:ℝ)*((M:ℝ)+2*∑ d ∈ Finset.Icc 1 H, B d) := by
  have hH0 : (0:ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hl (i : ℕ) (hi : i ∈ s) : (H:ℝ)/4 ≤ kernel H (t i:AddCircle (1:ℝ)) := by
    obtain ⟨z,hz⟩ := hsmall i hi
    have hz0 : ((z:ℝ):AddCircle (1:ℝ)) = 0 := by
      apply (AddCircle.coe_eq_zero_iff (1:ℝ)).mpr
      exact ⟨z,by simp⟩
    have he : ((t i-z:ℝ):AddCircle (1:ℝ)) = (t i:AddCircle (1:ℝ)) := by
      rw [AddCircle.coe_sub,hz0,sub_zero]
    simpa only [he] using kernel_small_arc_lower H hH (t i-z) hz
  have hb : (s.card:ℝ)*((H:ℝ)/4) ≤ (M:ℝ)+2*∑ d ∈ Finset.Icc 1 H, B d := by
    calc
      _ = ∑ _i ∈ s, (H:ℝ)/4 := by simp
      _ ≤ ∑ i ∈ s, kernel H (t i:AddCircle (1:ℝ)) := Finset.sum_le_sum hl
      _ ≤ ∑ i ∈ Finset.range M, kernel H (t i:AddCircle (1:ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hs (fun i _ _ => kernel_nonneg _ _)
      _ ≤ _ := kernel_sample_sum_bound (fun i => (t i:AddCircle (1:ℝ))) M H hH B hB hsum
  calc
    _ ≤ ((M:ℝ)+2*∑ d ∈ Finset.Icc 1 H, B d)/((H:ℝ)/4) :=
      (le_div_iff₀ (show (0:ℝ) < (H:ℝ)/4 by positivity)).mpr hb
    _ = _ := by field_simp

end NField.Alignment.FejerSmallArc

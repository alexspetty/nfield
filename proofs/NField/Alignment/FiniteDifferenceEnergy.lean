/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KaratsubaHolder

/-! # Exact finite shift energy with zero padding -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.FiniteDifferenceEnergy
open scoped BigOperators ComplexConjugate

def padded (f : ℕ → ℂ) (M R n : ℕ) : ℂ :=
  if R ≤ n ∧ n < R+M then f (n-R) else 0

theorem padded_support (f : ℕ → ℂ) (M R n : ℕ)
    (hn : padded f M R n ≠ 0) : R ≤ n ∧ n < R+M := by
  by_contra h
  exact hn (by simp [padded,h])

theorem padded_shift_sum (f : ℕ → ℂ) (M R h : ℕ) (hh : h ≤ R) :
    (∑ n ∈ Finset.range (M+R), padded f M R (n+h)) =
      ∑ i ∈ Finset.range M, f i := by
  apply Finset.sum_bij_ne_zero (fun n _ _ => n+h-R)
  · intro n hn hnz
    have hs := padded_support f M R (n+h) hnz
    simp only [Finset.mem_range]
    omega
  · intro n hn hnz n' hn' hnz' he
    have hs := padded_support f M R (n+h) hnz
    have hs' := padded_support f M R (n'+h) hnz'
    omega
  · intro i hi hiz
    have hi' := Finset.mem_range.mp hi
    have he : R+i-h+h-R = i := by omega
    refine ⟨R+i-h,Finset.mem_range.mpr (by omega),?_,he⟩
    simpa [padded,show R ≤ R+i-h+h ∧ R+i-h+h < R+M by omega,he] using hiz
  · intro n hn hnz
    simp [padded,padded_support f M R (n+h) hnz]

theorem padded_shift_overlap (f : ℕ → ℂ) (M R h k : ℕ)
    (hk : k ≤ h) (hh : h ≤ R) :
    (∑ n ∈ Finset.range (M+R),
      padded f M R (n+h)*conj (padded f M R (n+k))) =
      ∑ i ∈ Finset.range (M-(h-k)), f (i+(h-k))*conj (f i) := by
  have support (n : ℕ)
      (hn : padded f M R (n+h)*conj (padded f M R (n+k)) ≠ 0) :
      (R ≤ n+h ∧ n+h < R+M) ∧ (R ≤ n+k ∧ n+k < R+M) := by
    have ha := (mul_ne_zero_iff.mp hn).1
    have hb : padded f M R (n+k) ≠ 0 := by
      intro hz
      simp [hz] at hn
    exact ⟨padded_support f M R _ ha,padded_support f M R _ hb⟩
  apply Finset.sum_bij_ne_zero (fun n _ _ => n+k-R)
  · intro n hn hnz
    have hs := support n hnz
    simp only [Finset.mem_range]
    omega
  · intro n hn hnz n' hn' hnz' he
    have hs := support n hnz
    have hs' := support n' hnz'
    omega
  · intro i hi hiz
    have hi' := Finset.mem_range.mp hi
    have he : R+i-k+k-R = i := by omega
    have heh : R+i-k+h-R = i+(h-k) := by omega
    refine ⟨R+i-k,Finset.mem_range.mpr (by omega),?_,he⟩
    simpa [padded,show R ≤ R+i-k+h ∧ R+i-k+h < R+M by omega,
      show R ≤ R+i-k+k ∧ R+i-k+k < R+M by omega,he,heh] using hiz
  · intro n hn hnz
    have hs := support n hnz
    have he : n+h-R = n+k-R+(h-k) := by omega
    simp [padded,hs.1,hs.2,he]

theorem norm_sq_sum (s : Finset ℕ) (f : ℕ → ℂ) :
    ‖∑ i ∈ s, f i‖^2 =
      (∑ i ∈ s, ∑ j ∈ s, f i*conj (f j)).re := by
  have he : (∑ i ∈ s, ∑ j ∈ s, f i*conj (f j)) =
      (∑ i ∈ s, f i)*conj (∑ i ∈ s, f i) := by
    simp only [map_sum,Finset.sum_mul,Finset.mul_sum]
    exact Finset.sum_comm
  rw [he,Complex.mul_conj]
  norm_cast
  exact Complex.normSq_eq_norm_sq _ |>.symm

theorem padded_shift_energy (f : ℕ → ℂ) (M R : ℕ) :
    (R:ℝ)^2*‖∑ i ∈ Finset.range M, f i‖^2 ≤
      (M+R:ℕ)*∑ h ∈ Finset.range R, ∑ k ∈ Finset.range R,
        ‖∑ n ∈ Finset.range (M+R),
          padded f M R (n+h)*conj (padded f M R (n+k))‖ := by
  have hs : (∑ n ∈ Finset.range (M+R),
      ∑ h ∈ Finset.range R, padded f M R (n+h)) =
        (R:ℂ)*(∑ i ∈ Finset.range M, f i) := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ _h ∈ Finset.range R, ∑ i ∈ Finset.range M, f i := by
        apply Finset.sum_congr rfl
        intro h hh
        exact padded_shift_sum f M R h (by have := Finset.mem_range.mp hh; omega)
      _ = _ := by simp
  have hc := KaratsubaHolder.norm_sum_pow_le (Finset.range (M+R))
    (fun n => ∑ h ∈ Finset.range R, padded f M R (n+h)) (n:=2) (by norm_num)
  rw [hs,norm_mul,Complex.norm_natCast,mul_pow] at hc
  simp only [Finset.card_range,show 2-1=1 by norm_num,pow_one] at hc
  apply hc.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simp_rw [norm_sq_sum,Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro h hh
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro k hk
  rw [← Complex.re_sum]
  exact Complex.re_le_norm _

end NField.Alignment.FiniteDifferenceEnergy

/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionIntegerPrimeTailMajorants

/-!
# The square-root split for finite prime-factor losses

A sequence bounded both by 1/m and by 1/n^2 has total at most 3/sqrt(m)
on any finite set of positive integers. The small indices are counted;
the large indices are bounded by the proved infinite integer tail.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionSqrtPrimeSplit

open scoped Classical
open CollisionIntegerPrimeTailMajorants CollisionZetaMoments

theorem finite_small_index_sum_bound (s : Finset ℕ) (f : ℕ → ℝ) {y c : ℝ}
    (hy : 0 ≤ y) (hc : 0 ≤ c) (hpos : ∀ n ∈ s, 0 < n) (hf : ∀ n ∈ s, f n ≤ c) :
    (∑ n ∈ s.filter (fun (n : ℕ) => (n : ℝ) ≤ y), f n) ≤ y*c := by
  let t := s.filter (fun (n : ℕ) => (n : ℝ) ≤ y)
  have ht : t ⊆ Finset.Icc 1 ⌊y⌋₊ := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    exact Finset.mem_Icc.mpr ⟨hpos n hn'.1,(Nat.le_floor_iff hy).mpr hn'.2⟩
  have hcard : t.card ≤ ⌊y⌋₊ := by simpa using Finset.card_le_card ht
  have hcardR : (t.card : ℝ) ≤ y :=
    (by exact_mod_cast hcard : (t.card : ℝ) ≤ (⌊y⌋₊ : ℝ)).trans (Nat.floor_le hy)
  calc
    _ ≤ ∑ _n ∈ t, c := Finset.sum_le_sum (fun n hn => hf n (Finset.mem_filter.mp hn).1)
    _ = (t.card : ℝ)*c := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcardR hc

theorem finite_large_index_sum_bound (s : Finset ℕ) (f : ℕ → ℝ) {y : ℝ}
    (hy : 2 ≤ y) (hf : ∀ n ∈ s, f n ≤ powerKernel 2 n) :
    (∑ n ∈ s.filter (fun (n : ℕ) => y < (n : ℝ)), f n) ≤ 2/y := by
  calc
    _ ≤ ∑ n ∈ s.filter (fun (n : ℕ) => y < (n : ℝ)), inverseSquareTailTerm y n := by
      apply Finset.sum_le_sum
      intro n hn
      rw [inverseSquareTailTerm,if_pos (Finset.mem_filter.mp hn).2]
      exact hf n (Finset.mem_filter.mp hn).1
    _ ≤ ∑' n : ℕ, inverseSquareTailTerm y n :=
      (inverseSquareTailTerm_summable y).sum_le_tsum _ (fun n hn => inverseSquareTailTerm_nonneg y n)
    _ ≤ _ := integer_inverse_square_tail_bound hy

theorem finite_inverse_square_split (s : Finset ℕ) (f : ℕ → ℝ) {m : ℝ}
    (hm : 4 ≤ m) (hpos : ∀ n ∈ s, 0 < n)
    (hunif : ∀ n ∈ s, f n ≤ 1/m) (hsquare : ∀ n ∈ s, f n ≤ powerKernel 2 n) :
    (∑ n ∈ s, f n) ≤ 3/Real.sqrt m := by
  have hm0 : 0 < m := by linarith
  have hs0 := Real.sqrt_pos.mpr hm0
  have hs2 : 2 ≤ Real.sqrt m := by nlinarith [Real.sq_sqrt hm0.le,Real.sqrt_nonneg m]
  have hsplit : (∑ n ∈ s, f n)=
      (∑ n ∈ s.filter (fun (n : ℕ) => (n : ℝ) ≤ Real.sqrt m), f n)+
      (∑ n ∈ s.filter (fun (n : ℕ) => Real.sqrt m < (n : ℝ)), f n) := by
    rw [Finset.sum_filter,Finset.sum_filter,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases h : (n : ℝ) ≤ Real.sqrt m
    · simp only [if_pos h,if_neg (not_lt.mpr h),add_zero]
    · simp only [if_neg h,if_pos (lt_of_not_ge h),zero_add]
  rw [hsplit]
  calc
    _ ≤ Real.sqrt m*(1/m)+2/Real.sqrt m := add_le_add
      (finite_small_index_sum_bound s f hs0.le (by positivity) hpos hunif)
      (finite_large_index_sum_bound s f hs2 hsquare)
    _ = _ := by
      have hs : Real.sqrt m^2=m := Real.sq_sqrt hm0.le
      field_simp
      nlinarith

end NField.Alignment.CollisionSqrtPrimeSplit

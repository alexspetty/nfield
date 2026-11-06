/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.EndpointReciprocityBridge
import NField.Alignment.SecondaryPrintedBounds

/-! # The literal intermediate elementary reservoir inequality -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.SecondaryReservoirIntermediate
open scoped BigOperators Classical
open ExactSamplingReservoirBridge PrimeSquareReducedRatio DedekindReciprocity

theorem reciprocal_ratio_row {a : ℕ} (ha : 0 < a) :
    (∑ k ∈ Finset.Ico 1 a, ((a : ℝ)/(k : ℝ)+(k : ℝ)/(a : ℝ))) =
      (a : ℝ)*(harmonic (a-1) : ℝ)+(1/(a : ℝ))*∑ k ∈ Finset.range a,(k : ℝ) := by
  have hi : Finset.Ico 1 a=Finset.Icc 1 (a-1) := by ext k; simp; omega
  have hh : (harmonic (a-1) : ℝ)=∑ k ∈ Finset.Ico 1 a,(k : ℝ)⁻¹ := by
    rw [harmonic_eq_sum_Icc,hi]
    push_cast
    rfl
  rw [hh,sum_range_eq_sum_Ico_one (fun k => (k : ℝ)) ha (by simp),
    Finset.sum_add_distrib,Finset.mul_sum,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro k hk <;> ring

/-- Title: `The literal elementary reservoir bound before the harmonic estimate`. -/
theorem elementary_reservoir_intermediate {p : ℕ} (hp : 2 ≤ p) :
    elementaryRatioReservoir p ≤
      ∑ a ∈ Finset.Icc 2 (p-1), (((p-1 : ℕ) : ℝ)/(a : ℝ))*
        ((a : ℝ)*(harmonic (a-1) : ℝ)+(1/(a : ℝ))*∑ k ∈ Finset.range a,(k : ℝ)) := by
  let f : ℕ → ℕ → ℝ := fun a k => (((p-1 : ℕ) : ℝ)/(a : ℝ))*
    ((a : ℝ)/(k : ℝ)+(k : ℝ)/(a : ℝ))
  have he : elementaryRatioReservoir p = ∑ a ∈ Finset.range p, ∑ k ∈ Finset.range p,
      if 0<a ∧ 0<k ∧ k<a ∧ k.Coprime a then
        (((p-1)/a : ℕ) : ℝ)*((a : ℝ)/(k : ℝ)+(k : ℝ)/(a : ℝ)) else 0 := by
    unfold elementaryRatioReservoir reducedRatioPairs
    rw [Finset.sum_filter]
    exact Finset.sum_product (Finset.range p) (Finset.range p) _
  rw [he]
  calc
    _ ≤ ∑ a ∈ Finset.range p,∑ k ∈ Finset.range p,
        if 2≤a ∧ 1≤k ∧ k<a then f a k else 0 := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro k hk
      by_cases h : 0<a ∧ 0<k ∧ k<a ∧ k.Coprime a
      · have h' : 2≤a ∧ 1≤k ∧ k<a := by omega
        rw [if_pos h,if_pos h']
        exact mul_le_mul_of_nonneg_right Nat.cast_div_le (by positivity)
      · rw [if_neg h]
        split_ifs
        · dsimp [f]
          positivity
        · exact le_rfl
    _ = ∑ a ∈ Finset.Icc 2 (p-1),∑ k ∈ Finset.Ico 1 a,f a k := by
      have hout : (Finset.range p).filter (fun a => 2≤a)=Finset.Icc 2 (p-1) := by
        ext a
        simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Icc]
        omega
      rw [← hout,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a ha
      by_cases ha2 : 2≤a
      · simp only [ha2,true_and,if_true]
        rw [← Finset.sum_filter]
        congr 1
        ext k
        simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Ico]
        have hap := Finset.mem_range.mp ha
        omega
      · simp only [ha2,false_and,if_false,Finset.sum_const_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [← Finset.mul_sum,reciprocal_ratio_row (by have := (Finset.mem_Icc.mp ha).1; omega)]


def elementaryUpperSum (N : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 2 N, ((N : ℝ)/(a : ℝ))*
    ((a : ℝ)*(harmonic (a-1) : ℝ)+(1/(a : ℝ))*∑ k ∈ Finset.range a,(k : ℝ))

theorem elementary_row_log_bound (N : ℕ) {a : ℕ} (ha : 2 ≤ a) :
    ((N : ℝ)/(a : ℝ))*
      ((a : ℝ)*(harmonic (a-1) : ℝ)+(1/(a : ℝ))*∑ k ∈ Finset.range a,(k : ℝ)) ≤
        5*(N : ℝ)*Real.log (2*(a : ℝ)) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hH : (harmonic (a-1) : ℝ) ≤ 3*Real.log (2*(a : ℝ)) :=
    (DedekindFourierMoment.harmonic_cast_mono (Nat.sub_le a 1)).trans
      (SecondaryPrintedBounds.harmonic_le_three_log_double (by omega))
  have hhalf : (1/2 : ℝ) ≤ Real.log (2*(a : ℝ)) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ)<2)
    norm_num at h
    exact h.trans (Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ 2*a by omega)))
  have hs : (∑ k ∈ Finset.range a,(k : ℝ)) ≤ (a : ℝ)^2 := by
    calc
      _ ≤ ∑ _k ∈ Finset.range a,(a : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        exact_mod_cast (Finset.mem_range.mp hk).le
      _ = _ := by simp [pow_two]
  have hr : (1/(a : ℝ))*∑ k ∈ Finset.range a,(k : ℝ) ≤ a := by
    rw [one_div,inv_mul_eq_div]
    exact (div_le_iff₀ haR).mpr (by nlinarith)
  have hb : (a : ℝ)*(harmonic (a-1) : ℝ)+
      (1/(a : ℝ))*∑ k ∈ Finset.range a,(k : ℝ) ≤ 5*(a : ℝ)*Real.log (2*(a : ℝ)) := by
    nlinarith [mul_le_mul_of_nonneg_left hH haR.le,
      mul_le_mul_of_nonneg_left hhalf haR.le]
  calc
    _ ≤ ((N : ℝ)/(a : ℝ))*(5*(a : ℝ)*Real.log (2*(a : ℝ))) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by field_simp

/-- The first logarithmic comparison in the displayed intermediate reservoir estimate. -/
theorem elementary_upper_sum_logarithmic (N : ℕ) :
    elementaryUpperSum N ≤ 5*(N : ℝ)*∑ a ∈ Finset.Icc 1 N,Real.log (2*(a : ℝ)) := by
  calc
    _ ≤ ∑ a ∈ Finset.Icc 2 N,5*(N : ℝ)*Real.log (2*(a : ℝ)) := by
      apply Finset.sum_le_sum
      intro a ha
      exact elementary_row_log_bound N (Finset.mem_Icc.mp ha).1
    _ = 5*(N : ℝ)*∑ a ∈ Finset.Icc 2 N,Real.log (2*(a : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (show Finset.Icc 2 N ⊆ Finset.Icc 1 N by intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega)
      intro a ha hnot
      exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2*a by have := (Finset.mem_Icc.mp ha).1; omega))

/-- Title: `The intermediate reservoir sum has its printed quadratic logarithmic scale`. -/
theorem elementary_upper_sum_quadratic_logarithmic {N : ℕ} (hN : 1 ≤ N) :
    elementaryUpperSum N ≤ 5*(N : ℝ)^2*Real.log (2*(N : ℝ)) := by
  have hs : (∑ a ∈ Finset.Icc 1 N,Real.log (2*(a : ℝ))) ≤
      (N : ℝ)*Real.log (2*(N : ℝ)) := by
    calc
      _ ≤ ∑ _a ∈ Finset.Icc 1 N,Real.log (2*(N : ℝ)) := by
        apply Finset.sum_le_sum
        intro a ha
        apply Real.log_le_log (by have := (Finset.mem_Icc.mp ha).1; positivity)
        exact_mod_cast Nat.mul_le_mul_left 2 (Finset.mem_Icc.mp ha).2
      _ = _ := by simp
  calc
    _ ≤ 5*(N : ℝ)*∑ a ∈ Finset.Icc 1 N,Real.log (2*(a : ℝ)) := elementary_upper_sum_logarithmic N
    _ ≤ 5*(N : ℝ)*((N : ℝ)*Real.log (2*(N : ℝ))) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

end NField.Alignment.SecondaryReservoirIntermediate

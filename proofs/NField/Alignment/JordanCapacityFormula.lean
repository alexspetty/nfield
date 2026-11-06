/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.RealBernoulliCapacityIntegral
import NField.Alignment.CollisionJordanVariance

/-! # The exact Jordan formula used to compute continuous capacity -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.JordanCapacityFormula
open scoped BigOperators Classical
open CollisionJordanVariance GcdLcmCapacity RealBernoulliCapacityIntegral
  SecondaryCapacityLedger

theorem gcd_jordan_Icc {N k l : ℕ} (hk : k ∈ Finset.Icc 1 N) :
    (k.gcd l:ℝ)^2=∑ d ∈ Finset.Icc 1 N,
      if d ∣ k ∧ d ∣ l then jordanTwo d else 0 := by
  have hk0 : 0<k := (Finset.mem_Icc.mp hk).1
  have hg0 := Nat.gcd_pos_of_pos_left l hk0
  have he : (Finset.Icc 1 N).filter (fun d => d ∣ k ∧ d ∣ l)=(k.gcd l).divisors := by
    ext d
    simp only [Finset.mem_filter,Finset.mem_Icc,Nat.mem_divisors]
    constructor
    · rintro ⟨hd,hdk,hdl⟩
      exact ⟨Nat.dvd_gcd hdk hdl,hg0.ne'⟩
    · rintro ⟨hd,hg⟩
      have hd0 := Nat.pos_of_dvd_of_pos hd hg0
      have hdk := Nat.dvd_trans hd (Nat.gcd_dvd_left k l)
      exact ⟨⟨hd0,(Nat.le_of_dvd hk0 hdk).trans (Finset.mem_Icc.mp hk).2⟩,
        Nat.dvd_gcd_iff.mp hd⟩
  rw [← Finset.sum_filter,he,sum_jordanTwo_divisors]

theorem harmonic_multiples (N d : ℕ) (hd : 0<d) :
    (∑ k ∈ Finset.Icc 1 N, if d ∣ k then (k:ℝ)⁻¹ else 0)=
      (harmonic (N/d):ℝ)/(d:ℝ) := by
  rw [← Finset.sum_filter,harmonic_eq_sum_Icc]
  push_cast only [Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
  rw [Finset.sum_div]
  symm
  apply Finset.sum_bij (fun j hj => d*j)
  · intro j hj
    have hjI := Finset.mem_Icc.mp hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨Nat.mul_pos hd hjI.1,by
        have := (Nat.le_div_iff_mul_le hd).mp hjI.2
        simpa [Nat.mul_comm] using this⟩,dvd_mul_right d j⟩
  · intro j hj k hk he
    exact Nat.eq_of_mul_eq_mul_left hd he
  · intro k hk
    rcases Finset.mem_filter.mp hk with ⟨hkI,hdk⟩
    have hk0 := (Finset.mem_Icc.mp hkI).1
    refine ⟨k/d,Finset.mem_Icc.mpr ⟨?_,?_⟩,Nat.mul_div_cancel' hdk⟩
    · exact Nat.div_pos (Nat.le_of_dvd hk0 hdk) hd
    · exact Nat.div_le_div_right (Finset.mem_Icc.mp hkI).2
  · intro j hj
    push_cast
    rw [mul_inv_rev]
    ring

theorem square_capacity_Icc (N : ℕ) :
    3*continuousCapacity N=
      ∑ k ∈ Finset.Icc 1 N, ∑ l ∈ Finset.Icc 1 N, gcdLcmKernel k l := by
  rw [← gcdLcmSquareSum_eq_three_continuousCapacity,gcd_lcm_square_sum_ranges]
  have he (f : ℕ → ℝ) : (∑ k ∈ Finset.range N,f (k+1))=∑ k ∈ Finset.Icc 1 N,f k := by
    apply Finset.sum_bij (fun k hk => k+1)
    · intro k hk
      exact Finset.mem_Icc.mpr ⟨by omega,by have := Finset.mem_range.mp hk; omega⟩
    · intro k hk l hl hkl
      omega
    · intro k hk
      have := Finset.mem_Icc.mp hk
      exact ⟨k-1,Finset.mem_range.mpr (by omega),by omega⟩
    · intro k hk
      rfl
  simp_rw [he]
  exact he (fun k => ∑ l ∈ Finset.Icc 1 N,gcdLcmKernel k l)

/-- Title: `Exact Jordan and harmonic formula for continuous capacity`. -/
theorem capacity_jordan_formula (N : ℕ) :
    3*continuousCapacity N=∑ d ∈ Finset.Icc 1 N,
      jordanTwo d/(d:ℝ)^2*(harmonic (N/d):ℝ)^2 := by
  rw [square_capacity_Icc]
  calc
    _ = ∑ k ∈ Finset.Icc 1 N, ∑ l ∈ Finset.Icc 1 N,
        ∑ d ∈ Finset.Icc 1 N,
          (if d ∣ k ∧ d ∣ l then jordanTwo d else 0)/((k:ℝ)*(l:ℝ)) := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      rw [gcdLcmKernel,gcd_jordan_Icc hk,Finset.sum_div]
    _ = ∑ d ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        ∑ l ∈ Finset.Icc 1 N,
          (if d ∣ k ∧ d ∣ l then jordanTwo d else 0)/((k:ℝ)*(l:ℝ)) := by
      conv_lhs => arg 2; ext k; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
    _ = ∑ d ∈ Finset.Icc 1 N, jordanTwo d*
        (∑ k ∈ Finset.Icc 1 N,if d ∣ k then (k:ℝ)⁻¹ else 0)^2 := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [pow_two,Finset.sum_mul_sum]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      by_cases hdk : d ∣ k <;> by_cases hdl : d ∣ l <;>
        simp [hdk,hdl,div_eq_mul_inv,mul_inv_rev,mul_assoc,mul_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [harmonic_multiples N d (Finset.mem_Icc.mp hd).1]
      ring

end NField.Alignment.JordanCapacityFormula

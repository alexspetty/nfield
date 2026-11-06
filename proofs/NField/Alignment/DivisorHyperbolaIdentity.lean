/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.TriangularAdditiveConvolution

/-! # The exact finite divisor hyperbola identity -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.DivisorHyperbolaIdentity
open scoped BigOperators Classical

def divisorCount (N : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ)

theorem divisor_count_floor_sum (N : ℕ) :
    divisorCount N=∑ a ∈ Finset.Icc 1 N, ((N/a : ℕ) : ℝ) := by
  have h := TriangularAdditiveConvolution.sum_divisor_lifetimes N (fun _ => 1)
  simp only [Finset.sum_const,mul_one,nsmul_eq_mul] at h
  unfold divisorCount
  exact_mod_cast h

theorem hyperbola_row (N a : ℕ) (ha : 1≤a) :
    (∑ b ∈ Finset.Icc 1 N, if a*b≤N then (1 : ℝ) else 0)=((N/a : ℕ) : ℝ) := by
  have he : (Finset.Icc 1 N).filter (fun b => a*b≤N)=Finset.Icc 1 (N/a) := by
    ext b
    simp only [Finset.mem_filter,Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hb,hbN⟩,hab⟩
      exact ⟨hb,(Nat.le_div_iff_mul_le (by omega : 0<a)).mpr (by simpa [Nat.mul_comm] using hab)⟩
    · rintro ⟨hb,hba⟩
      have hab := (Nat.le_div_iff_mul_le (by omega : 0<a)).mp hba
      exact ⟨⟨hb,hba.trans (Nat.div_le_self _ _)⟩,by simpa [Nat.mul_comm] using hab⟩
  rw [← Finset.sum_filter,he]
  simp

theorem square_strip_sum (N M : ℕ) (hMN : M≤N) (f : ℕ → ℝ) :
    (∑ a ∈ Finset.Icc 1 N, if a≤M then f a else 0)=∑ a ∈ Finset.Icc 1 M,f a := by
  rw [← Finset.sum_filter]
  congr 1
  ext a
  simp only [Finset.mem_filter,Finset.mem_Icc]
  omega

theorem floor_sum_hyperbola (N M : ℕ) (hMN : M≤N)
    (hlo : M^2≤N) (hhi : N<(M+1)^2) :
    (∑ a ∈ Finset.Icc 1 N,((N/a : ℕ) : ℝ) : ℝ)+(M : ℝ)^2=
      2*∑ a ∈ Finset.Icc 1 M,((N/a : ℕ) : ℝ) := by
  let g : ℕ → ℕ → ℝ := fun a b => if a*b≤N then 1 else 0
  have hp (a b : ℕ) : g a b+(if a≤M ∧ b≤M then 1 else 0)=
      (if a≤M then g a b else 0)+(if b≤M then g a b else 0) := by
    by_cases ha : a≤M <;> by_cases hb : b≤M
    · have hab : a*b≤N := (Nat.mul_le_mul ha hb).trans (by simpa [pow_two] using hlo)
      simp [g,ha,hb,hab]
    · simp [ha,hb]
    · simp [ha,hb]
    · have hab : ¬a*b≤N := by
        have hm := Nat.mul_le_mul (show M+1≤a by omega) (show M+1≤b by omega)
        nlinarith
      simp [g,ha,hb,hab]
  have hs := congrArg (fun f : ℕ → ℕ → ℝ => ∑ a ∈ Finset.Icc 1 N,
      ∑ b ∈ Finset.Icc 1 N,f a b) (funext fun a => funext fun b => hp a b)
  have hleft : (∑ a ∈ Finset.Icc 1 N,∑ b ∈ Finset.Icc 1 N,g a b)=
      ∑ a ∈ Finset.Icc 1 N,((N/a : ℕ) : ℝ) := by
    apply Finset.sum_congr rfl
    intro a ha
    exact hyperbola_row N a (Finset.mem_Icc.mp ha).1
  have hcorner : (∑ a ∈ Finset.Icc 1 N,∑ b ∈ Finset.Icc 1 N,
      if a≤M ∧ b≤M then (1 : ℝ) else 0)=(M : ℝ)^2 := by
    have he (a : ℕ) : (∑ b ∈ Finset.Icc 1 N,if a≤M ∧ b≤M then (1 : ℝ) else 0)=
        if a≤M then (M : ℝ) else 0 := by
      by_cases ha : a≤M
      · simp only [ha,true_and,if_true]
        rw [square_strip_sum N M hMN]
        simp
      · simp [ha]
    simp_rw [he]
    rw [square_strip_sum N M hMN]
    simp [pow_two]
  have hstrip : (∑ a ∈ Finset.Icc 1 N,∑ b ∈ Finset.Icc 1 N,
      if a≤M then g a b else 0)=∑ a ∈ Finset.Icc 1 M,((N/a : ℕ) : ℝ) := by
    simp_rw [Finset.sum_ite_irrel,Finset.sum_const_zero]
    rw [square_strip_sum N M hMN]
    apply Finset.sum_congr rfl
    intro a ha
    exact hyperbola_row N a (Finset.mem_Icc.mp ha).1
  have hstrip' : (∑ a ∈ Finset.Icc 1 N,∑ b ∈ Finset.Icc 1 N,
      if b≤M then g a b else 0)=∑ a ∈ Finset.Icc 1 M,((N/a : ℕ) : ℝ) := by
    rw [Finset.sum_comm]
    simpa only [g,Nat.mul_comm] using hstrip
  simp only [Finset.sum_add_distrib] at hs
  rw [hleft,hcorner,hstrip,hstrip'] at hs
  linarith

theorem divisor_hyperbola (N M : ℕ) (hMN : M≤N)
    (hlo : M^2≤N) (hhi : N<(M+1)^2) :
    divisorCount N=2*∑ a ∈ Finset.Icc 1 M,((N/a : ℕ) : ℝ)-(M : ℝ)^2 := by
  rw [divisor_count_floor_sum]
  linarith [floor_sum_hyperbola N M hMN hlo hhi]

end NField.Alignment.DivisorHyperbolaIdentity

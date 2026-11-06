/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.PrimitiveAdditiveConvolution

/-! # Lifetime weights and the literal triangular Dedekind convolution -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.TriangularAdditiveConvolution
open scoped BigOperators Classical
open PrimitiveAdditiveConvolution RademacherThreeTerm

theorem sum_divisor_lifetimes (N : ℕ) (f : ℕ → ℚ) :
    (∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors,f d)=
      ∑ d ∈ Finset.Icc 1 N,(N/d:ℕ)*f d := by
  have he (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      n.divisors=(Finset.Icc 1 N).filter (fun d => d ∣ n) := by
    ext d
    have hn0 : 0<n := (Finset.mem_Icc.mp hn).1
    simp only [Nat.mem_divisors,Finset.mem_filter,Finset.mem_Icc]
    constructor
    · rintro ⟨hd,hne⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd hn0,
        (Nat.le_of_dvd hn0 hd).trans (Finset.mem_Icc.mp hn).2⟩,hd⟩
    · rintro ⟨hI,hd⟩
      exact ⟨hd,hn0.ne'⟩
  calc
    _ = ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 N,if d ∣ n then f d else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [he n hn,Finset.sum_filter]
    _ = ∑ d ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,if d ∣ n then f d else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Finset.sum_filter,Finset.sum_const]
      have hcard : ((Finset.Icc 1 N).filter (fun n => d ∣ n)).card=N/d := by
        have hs : Finset.Icc 1 N=Finset.Ioc 0 N := by ext n; simp; omega
        rw [hs]
        exact Nat.Ioc_filter_dvd_card_eq_div N d
      rw [hcard,nsmul_eq_mul]

def triangularDedekindConvolution (p N : ℕ) : ℚ :=
  ∑ ab ∈ ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter (fun ab => ab.1+ab.2≤N),
    arithmeticCoefficientDedekindTerm ab.1 ab.2 (p^2)

theorem triangular_sum_antidiagonals (p N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,fullAdditiveConvolution p n)=triangularDedekindConvolution p N := by
  unfold fullAdditiveConvolution additiveIndices triangularDedekindConvolution
  rw [Finset.sum_sigma']
  apply Finset.sum_bij (fun a ha => (a.2,a.1-a.2))
  · intro a ha
    rcases Finset.mem_sigma.mp ha with ⟨hn,hk⟩
    have hnI := Finset.mem_Icc.mp hn
    have hkI := Finset.mem_Ico.mp hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hkI.1,by omega⟩,Finset.mem_Icc.mpr ⟨by omega,by omega⟩⟩,
      by omega⟩
  · intro a ha b hb he
    have haI := Finset.mem_Ico.mp (Finset.mem_sigma.mp ha).2
    have hbI := Finset.mem_Ico.mp (Finset.mem_sigma.mp hb).2
    have hk := congrArg Prod.fst he
    have hn := congrArg Prod.snd he
    have he1 : a.1=b.1 := by dsimp at hk hn; omega
    cases a
    cases b
    simp only [Sigma.mk.inj_iff]
    exact ⟨he1,by simpa using hk⟩
  · intro ab hab
    rcases Finset.mem_filter.mp hab with ⟨hprod,hsum⟩
    rcases Finset.mem_product.mp hprod with ⟨ha,hb⟩
    have haI := Finset.mem_Icc.mp ha
    have hbI := Finset.mem_Icc.mp hb
    refine ⟨⟨ab.1+ab.2,ab.1⟩,Finset.mem_sigma.mpr
      ⟨Finset.mem_Icc.mpr ⟨by change 1≤ab.1+ab.2; omega,hsum⟩,
        Finset.mem_Ico.mpr ⟨haI.1,by change ab.1<ab.1+ab.2; omega⟩⟩,?_⟩
    simp
  · intro a ha
    rfl

/-- Title: `Lifetime-weighted primitive packets form the triangular convolution`. -/
theorem primitive_lifetime_triangle {p N : ℕ} (hp : p.Prime) (hNp : N<p) :
    (∑ X ∈ Finset.Icc 1 N,(N/X:ℕ)*primitiveAdditiveConvolution p X)=
      triangularDedekindConvolution p N := by
  rw [← sum_divisor_lifetimes,← triangular_sum_antidiagonals]
  apply Finset.sum_congr rfl
  intro n hn
  exact (full_additive_convolution_divisor_sum hp (Finset.mem_Icc.mp hn).1
    ((Finset.mem_Icc.mp hn).2.trans_lt hNp)).symm

end NField.Alignment.TriangularAdditiveConvolution

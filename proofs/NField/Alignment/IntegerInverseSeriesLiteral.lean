/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.IntegerInversePrefix

/-! # The signed inverse series as the literal real sawtooth sum -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.IntegerInverseSeriesLiteral
open scoped BigOperators Topology Classical
open Filter CollisionDedekindPairing CarryBoundarySpectra IntegerInverseResidue
  IntegerInversePrefix DedekindInverseResidueTransform

theorem centered_sawtooth_int {q : ℕ} (hq : 0<q) (a : ℤ) :
    letI : NeZero q := ⟨hq.ne'⟩
    centeredSawtooth (a:ZMod q)=(periodicSawtooth ((a:ℝ)/(q:ℝ)):ℂ) := by
  letI : NeZero q := ⟨hq.ne'⟩
  have hnat (n : ℕ) : centeredSawtooth (n:ZMod q)=(periodicSawtooth ((n:ℝ)/(q:ℝ)):ℂ) := by
    rw [← midpointSawtooth_complex,midpointSawtooth_fract]
  cases a with
  | ofNat a => simpa using hnat a
  | negSucc a =>
      rw [show Int.negSucc a = -((a+1:ℕ):ℤ) by rfl]
      simp only [Int.cast_neg,Int.cast_natCast,centered_sawtooth_neg_all,neg_div,real_sawtooth_neg,
        Complex.ofReal_neg,hnat]

theorem integer_inverse_coefficient_literal {q n : ℕ} (hq : 0<q) (hn : n.Coprime q) (r : ℤ) :
    integerInverseCoefficient q r n=
      (periodicSawtooth ((r:ℝ)*(inverseResidue n q:ℝ)/(q:ℝ)):ℂ) := by
  letI : NeZero q := ⟨hq.ne'⟩
  have hprod : (r:ZMod q)*(ZMod.unitOfCoprime n hn)⁻¹.val=
      (((r*(inverseResidue n q:ℤ)):ℤ):ZMod q) := by
    simp only [Int.cast_mul,Int.cast_natCast,inverseResidue,dif_neg hq.ne',dif_pos hn,
      ZMod.natCast_zmod_val]
  simp only [integerInverseCoefficient,dif_neg hq.ne',dif_pos hn,hprod]
  rw [centered_sawtooth_int hq]
  push_cast
  rfl

def integerLiteralPartial (q : ℕ) (r : ℤ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, if n.Coprime q then
    (periodicSawtooth ((r:ℝ)*(inverseResidue n q:ℝ)/(q:ℝ)):ℂ)/(n:ℂ) else 0

theorem integer_literal_partial_eq {q : ℕ} (hq : 0<q) (r : ℤ) (N : ℕ) :
    integerLiteralPartial q r N=integerInversePartial q r N := by
  unfold integerLiteralPartial integerInversePartial
  symm
  apply Finset.sum_bij (fun n hn => n+1)
  · intro n hn
    have := Finset.mem_range.mp hn
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  · intro n hn m hm he
    omega
  · intro n hn
    have hi := Finset.mem_Icc.mp hn
    exact ⟨n-1,Finset.mem_range.mpr (by omega),by omega⟩
  · intro n hn
    by_cases hcop : (n+1).Coprime q
    · rw [if_pos hcop,integer_inverse_coefficient_literal hq hcop]
      simp only [Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_natCast,div_eq_mul_inv]
      ring
    · simp [integerInverseCoefficient,hq.ne',hcop]

/-- Title: `Natural-order convergence of the literal signed inverse series`. -/
theorem integer_literal_series_tendsto {q : ℕ} (hq : 0<q) (r : ℤ) :
    Tendsto (integerLiteralPartial q r) atTop (𝓝 (integerInverseSeries q r)) := by
  have he : integerLiteralPartial q r=integerInversePartial q r :=
    funext (integer_literal_partial_eq hq r)
  rw [he]
  exact integer_inverse_series_tendsto q r

end NField.Alignment.IntegerInverseSeriesLiteral

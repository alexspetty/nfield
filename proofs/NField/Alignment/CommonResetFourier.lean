/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetDedekind
import NField.Alignment.CollisionFiniteSineTransform

/-! # Finite cotangent formulas with nonunit numerator indices -/

noncomputable section

namespace NField.Alignment.CommonResetFourier

open scoped BigOperators
open CarryBoundarySpectra DedekindFourierMoment DedekindInverseResidueTransform
open DedekindReciprocity CommonResetGrid CollisionFiniteSineTransform

def cotangentResidue {m : ℕ} (x : ZMod m) : ℝ :=
  Real.cot (Real.pi*(x.val : ℝ)/(m : ℝ))

def cotangentTerm (m a : ℕ) : ℝ :=
  if m ∣ a then 0 else Real.cot (Real.pi*(a : ℝ)/(m : ℝ))

/-- Title: `The finite sawtooth Fourier coefficient is the cotangent coefficient`. -/
theorem dft_cotangent {m : ℕ} [NeZero m] (x : ZMod m) :
    ZMod.dft (centeredSawtooth : ZMod m → ℂ) x =
      Complex.I/2*(cotangentResidue x : ℂ) := by
  have hm := NeZero.pos m
  by_cases hx : x = 0
  · subst x
    have hz := sawtoothFourier_zero hm
    rw [sawtoothFourier_eq_dft] at hz
    simpa [cotangentResidue, Real.cot_eq_cos_div_sin] using hz
  · have hv : 0 < x.val := ZMod.val_pos.mpr hx
    have h := sawtoothFourier_eq_cotangent hm hv x.val_lt
    rw [sawtoothFourier_eq_dft, ZMod.natCast_zmod_val] at h
    rw [h]
    congr 1
    rw [cotangentResidue, Complex.ofReal_cot]
    congr 1
    push_cast
    ring

theorem cotangentResidue_nat {m : ℕ} [NeZero m] (a : ℕ) :
    cotangentResidue (a : ZMod m) = cotangentTerm m a := by
  unfold cotangentResidue cotangentTerm
  rw [ZMod.val_natCast]
  by_cases h : m ∣ a
  · simp [h, Nat.mod_eq_zero_of_dvd h, Real.cot_eq_cos_div_sin]
  · rw [if_neg h, cotangent_mod (NeZero.pos m)]

def residueDedekind {m : ℕ} [NeZero m] (h : ZMod m) : ℂ :=
  ∑ x : ZMod m, centeredSawtooth x * centeredSawtooth (h*x)

theorem dft_sawtooth_odd {m : ℕ} [NeZero m] (hm : 2 ≤ m) :
    Function.Odd (ZMod.dft (centeredSawtooth : ZMod m → ℂ)) :=
  ZMod.dft_odd_iff.mpr (centeredSawtooth_neg hm)

/-- Title: `Fourier inversion retains every numerator index in a Dedekind sum`. -/
theorem residueDedekind_fourier {m : ℕ} [NeZero m] (hm : 2 ≤ m) (h : ZMod m) :
    residueDedekind h = -(m : ℂ)⁻¹ * ∑ n : ZMod m,
      ZMod.dft (centeredSawtooth : ZMod m → ℂ) n *
        ZMod.dft (centeredSawtooth : ZMod m → ℂ) (h*n) := by
  have ht (n : ZMod m) :
      (∑ x : ZMod m, centeredSawtooth x * ZMod.stdAddChar (n*(h*x))) =
        -ZMod.dft (centeredSawtooth : ZMod m → ℂ) (h*n) := by
    rw [← dft_sawtooth_odd hm, ZMod.dft_apply]
    apply Finset.sum_congr rfl
    intro x _
    simp only [smul_eq_mul, mul_neg, neg_neg, mul_comm, mul_left_comm]
  unfold residueDedekind
  simp_rw [centeredSawtooth_fourier_inversion (h*_)]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  calc
    _ = (m : ℂ)⁻¹*ZMod.dft (centeredSawtooth : ZMod m → ℂ) n *
        ∑ x : ZMod m, centeredSawtooth x * ZMod.stdAddChar (n*(h*x)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by rw [ht]; ring

/-- Title: `The cotangent Dedekind formula includes nonunit numerators`. -/
theorem residueDedekind_cotangent {m : ℕ} [NeZero m] (hm : 2 ≤ m) (h : ZMod m) :
    residueDedekind h = (1/(4*(m : ℂ))) *
      ∑ n : ZMod m, (cotangentResidue n : ℂ)*(cotangentResidue (h*n) : ℂ) := by
  rw [residueDedekind_fourier hm]
  simp only [dft_cotangent, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem residueDedekind_eq_rational {m : ℕ} [NeZero m] (h : ℕ) :
    residueDedekind (h : ZMod m) = (arithmeticDedekindSum h m : ℂ) := by
  unfold residueDedekind arithmeticDedekindSum
  push_cast
  rw [← (ZMod.finEquiv m).toEquiv.sum_comp
    (fun x : ZMod m => centeredSawtooth x * centeredSawtooth ((h : ZMod m)*x)),
    ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro x _
  change centeredSawtooth (ZMod.finEquiv m x)*
    centeredSawtooth ((h : ZMod m)*ZMod.finEquiv m x) = _
  rw [ConductorDepthSawtooth.finEquiv_eq_natCast]
  have he (a : ℕ) : centeredSawtooth (a : ZMod m) = (rationalSawtooth a m : ℂ) := by
    have hc := rationalSawtooth_val_eq_centeredSawtooth (a : ZMod m)
    simp only [ZMod.val_natCast, rationalSawtooth, Nat.mod_mod] at hc
    exact hc.symm
  rw [← Nat.cast_mul, he, he]

/-- Title: `The literal cotangent sum gives every arithmetic Dedekind value`. -/
theorem arithmeticDedekind_cotangent {m : ℕ} (hm : 2 ≤ m) (h : ℕ) :
    (m : ℝ)*(arithmeticDedekindSum h m : ℝ) =
      (1/4 : ℝ)*∑ a ∈ Finset.range m, cotangentTerm m a*cotangentTerm m (h*a) := by
  letI : NeZero m := ⟨by omega⟩
  have hc := residueDedekind_cotangent hm (h : ZMod m)
  rw [residueDedekind_eq_rational] at hc
  have hs : (∑ n : ZMod m, (cotangentResidue n : ℂ)*
      (cotangentResidue ((h : ZMod m)*n) : ℂ)) =
      ((∑ a ∈ Finset.range m, cotangentTerm m a*cotangentTerm m (h*a) : ℝ) : ℂ) := by
    push_cast
    rw [← (ZMod.finEquiv m).toEquiv.sum_comp
      (fun n : ZMod m => (cotangentResidue n : ℂ)*(cotangentResidue ((h : ZMod m)*n) : ℂ)),
      ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro a _
    change (cotangentResidue (ZMod.finEquiv m a) : ℂ)*
      (cotangentResidue ((h : ZMod m)*ZMod.finEquiv m a) : ℂ) = _
    rw [ConductorDepthSawtooth.finEquiv_eq_natCast, ← Nat.cast_mul,
      cotangentResidue_nat, cotangentResidue_nat]
  rw [hs] at hc
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  apply Complex.ofReal_injective
  push_cast
  rw [hc]
  field_simp
  push_cast
  rfl

end NField.Alignment.CommonResetFourier

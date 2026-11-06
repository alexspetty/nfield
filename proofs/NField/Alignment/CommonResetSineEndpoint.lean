/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetHalfFrequencies

/-! # The complete endpoint sine expansion -/

noncomputable section

namespace NField.Alignment.CommonResetSineEndpoint

open scoped BigOperators
open CommonResetEndpoint CommonResetHalfFrequencies

def characterSine {t : ℕ} [NeZero t] (x : ZMod t) : ℝ :=
  (ZMod.stdAddChar x).im

def sinePrefix {t : ℕ} [NeZero t] (r : ℕ) (j : ZMod t) : ℝ :=
  ∑ a ∈ Finset.Icc 1 r, characterSine ((a : ZMod t)*j)

theorem characterSine_odd {t : ℕ} [NeZero t] (x : ZMod t) :
    characterSine (-x) = -characterSine x := by
  simp [characterSine, AddChar.map_neg_eq_conj]

theorem character_difference {t : ℕ} [NeZero t] (x : ZMod t) :
    ZMod.stdAddChar (-x)-ZMod.stdAddChar x =
      (-2*Complex.I)*(characterSine x : ℂ) := by
  rw [AddChar.map_neg_eq_conj]
  apply Complex.ext <;> simp [characterSine, Complex.mul_re, Complex.mul_im] <;> ring

theorem complex_prefixIndicator_sum {t : ℕ} [NeZero t] (r : ℕ) (hr : r < t)
    (f : ZMod t → ℂ) :
    (∑ a : ZMod t, (prefixIndicator r a : ℂ)*f a) =
      ∑ a ∈ Finset.Icc 1 r, f (a : ZMod t) := by
  apply Complex.ext
  · simpa only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using
      prefixIndicator_sum r hr (fun a => (f a).re)
  · simpa only [Complex.im_sum, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero] using
      prefixIndicator_sum r hr (fun a => (f a).im)

/-- Title: `The endpoint Fourier coefficient includes every linear frequency`. -/
theorem endpoint_dft {t : ℕ} [NeZero t] (r : ℕ) (hr : r < t) (j : ZMod t) :
    ZMod.dft (fun a : ZMod t => (endpointDifference r a : ℂ)) j =
      (-2*Complex.I)*(sinePrefix r j : ℂ) := by
  rw [ZMod.dft_apply]
  have hneg := Equiv.sum_comp (Equiv.neg (ZMod t)) (fun a : ZMod t =>
    (prefixIndicator r (-a) : ℂ)*ZMod.stdAddChar (-(a*j)))
  simp only [Equiv.neg_apply, neg_neg, neg_mul] at hneg
  calc
    (∑ a : ZMod t, ZMod.stdAddChar (-(a*j)) • (endpointDifference r a : ℂ)) =
        (∑ a : ZMod t, (prefixIndicator r a : ℂ)*ZMod.stdAddChar (-(a*j)))-
        ∑ a : ZMod t, (prefixIndicator r (-a) : ℂ)*ZMod.stdAddChar (-(a*j)) := by
      simp only [endpointDifference, Complex.ofReal_sub, smul_eq_mul,
        mul_sub, Finset.sum_sub_distrib]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro a _ <;> ring
    _ = ∑ a : ZMod t, (prefixIndicator r a : ℂ)*
        (ZMod.stdAddChar (-(a*j))-ZMod.stdAddChar (a*j)) := by
      rw [← hneg]
      simp only [mul_sub, Finset.sum_sub_distrib]
    _ = ∑ a ∈ Finset.Icc 1 r,
        (ZMod.stdAddChar (-((a : ZMod t)*j))-ZMod.stdAddChar ((a : ZMod t)*j)) :=
      complex_prefixIndicator_sum r hr _
    _ = _ := by
      simp only [character_difference, sinePrefix, Complex.ofReal_sum, Finset.mul_sum]

theorem sinePrefix_odd {t : ℕ} [NeZero t] (r : ℕ) (j : ZMod t) :
    sinePrefix r (-j) = -sinePrefix r j := by
  simp only [sinePrefix, mul_neg, characterSine_odd, Finset.sum_neg_distrib]

/-- Title: `The full endpoint response is its finite sine series`. -/
theorem endpoint_full_sine {t : ℕ} [NeZero t] (r : ℕ) (hr : r < t) (x : ZMod t) :
    endpointDifference r x = (2/(t : ℝ))*
      ∑ j : ZMod t, sinePrefix r j*characterSine (j*x) := by
  have hi := congrFun
    (ZMod.dft.symm_apply_apply (fun a : ZMod t => (endpointDifference r a : ℂ))) x
  rw [ZMod.invDFT_apply] at hi
  simp only [smul_eq_mul, endpoint_dft r hr] at hi
  have hiR := congrArg Complex.re hi
  have hinv : (t : ℂ)⁻¹ = Complex.ofReal ((t : ℝ)⁻¹) := by simp
  rw [hinv] at hiR
  norm_num [Complex.mul_re, Complex.mul_im, Complex.re_sum] at hiR
  dsimp only [characterSine]
  rw [← hiR]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Title: `The endpoint sine series pairs every nonzero opposite frequency`. -/
theorem endpoint_half_sine {t : ℕ} [NeZero t] (r : ℕ) (hr : r < t) (x : ZMod t) :
    endpointDifference r x = (4/(t : ℝ))*
      ∑ j ∈ lowerResidues t, sinePrefix r j*characterSine (j*x) := by
  rw [endpoint_full_sine r hr]
  have he := residue_sum_pair (fun j : ZMod t => sinePrefix r j*characterSine (j*x))
    (fun j => by simp only [sinePrefix_odd, neg_mul, characterSine_odd, mul_neg, neg_neg])
    (fun j hj => by
      have hzero : sinePrefix r j = 0 := by
        have h := sinePrefix_odd r j
        rw [hj] at h
        linarith
      rw [hzero, zero_mul])
  rw [he]
  ring

end NField.Alignment.CommonResetSineEndpoint

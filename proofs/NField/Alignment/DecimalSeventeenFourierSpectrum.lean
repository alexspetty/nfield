/-
Author: Alexander S. Petty
-/

import NField.Alignment.DecimalPrimeMatrixSpectra

/-!
# Complete Fourier spectrum of the decimal orbit modulo seventeen

The concrete primitive-orbit word is transported to `ZMod 16`, where the
general Fourier basis theorem applies.  Its cyclic equality kernel is then
evaluated exactly and connected to the nine printed real harmonic values.
-/

namespace NField.Alignment.DecimalSeventeenFourierSpectrum

open scoped BigOperators
open NField.Alignment
open NField.Alignment.CrossAlignmentMatrix
open NField.Alignment.CosetFourierReduction
open NField.Alignment.DecimalOrbitSpectra
open NField.Alignment.DecimalPrimeMatrixSpectra

local instance : NeZero 16 := ⟨by norm_num⟩

/-- The displayed primitive-orbit word, with its phase coordinate represented
by `ZMod 16`. -/
noncomputable def decimalSeventeenWordZMod (t : ZMod 16) : Fin 10 :=
  decimalSeventeenWord ((ZMod.finEquiv 16).symm t)

/-- Its normalized cyclic equality autocorrelation. -/
noncomputable def decimalSeventeenCorrelationKernel (u : ZMod 16) : ℂ :=
  (16 : ℂ)⁻¹ * ∑ t : ZMod 16,
    if decimalSeventeenWordZMod (t + u) = decimalSeventeenWordZMod t
    then 1 else 0

/-- Exact support and normalization of the primitive decimal kernel. -/
theorem decimalSeventeenCorrelationKernel_certificate (u : ZMod 16) :
    decimalSeventeenCorrelationKernel u =
      if u = 0 then 1
      else if u.val ∈ ([1, 3, 5, 11, 13, 15] : List ℕ)
        then (1 : ℂ) / 8 else 0 := by
  let uf : Fin 16 := (ZMod.finEquiv 16).symm u
  have hcount :
      (∑ t : ZMod 16,
        if decimalSeventeenWordZMod (t + u) = decimalSeventeenWordZMod t
        then 1 else 0) =
        crossCorrelation decimalSeventeenWord decimalSeventeenWord uf := by
    unfold crossCorrelation
    apply Fintype.sum_equiv (ZMod.finEquiv 16).symm
    intro t
    unfold decimalSeventeenWordZMod uf
    congr 2
  have hsum :
      (∑ t : ZMod 16,
        if decimalSeventeenWordZMod (t + u) = decimalSeventeenWordZMod t
        then (1 : ℂ) else 0) =
        (crossCorrelation decimalSeventeenWord decimalSeventeenWord uf : ℂ) := by
    exact_mod_cast hcount
  unfold decimalSeventeenCorrelationKernel
  rw [hsum, decimalSeventeenCorrelation_certificate]
  have hval : uf.val = u.val := by
    unfold uf
    rfl
  have hzero : uf = 0 ↔ u = 0 := by
    exact (ZMod.finEquiv 16).symm.injective.eq_iff
  rw [hval]
  by_cases hu : u = 0
  · simp [hu, hzero]
  · have huf : uf ≠ 0 := by simpa [hzero] using hu
    by_cases hs : u.val ∈ ([1, 3, 5, 11, 13, 15] : List ℕ)
    · simp [hu, huf, hs]
      norm_num
    · simp [hu, huf, hs]

/-- A standard character and its inverse add to twice the corresponding real
cosine. -/
theorem stdAddChar_add_neg_eq_two_cos (m : ℤ) :
    ZMod.stdAddChar (m : ZMod 16) + ZMod.stdAddChar (-m : ZMod 16) =
      2 * (Real.cos (Real.pi * m / 8) : ℂ) := by
  rw [ZMod.stdAddChar_coe]
  rw [show (-m : ZMod 16) = ((-m : ℤ) : ZMod 16) by
    exact Int.cast_neg m |>.symm]
  rw [ZMod.stdAddChar_coe]
  let angle : ℝ := Real.pi * m / 8
  have hpos : 2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) / 16 =
      (angle : ℂ) * Complex.I := by
    unfold angle
    push_cast
    ring
  have hneg : 2 * (Real.pi : ℂ) * Complex.I * ((-m : ℤ) : ℂ) / 16 =
      -(angle : ℂ) * Complex.I := by
    unfold angle
    push_cast
    ring
  have hpos' : 2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) /
      (16 : ℂ) = (angle : ℂ) * Complex.I := by simpa using hpos
  have hneg' : 2 * (Real.pi : ℂ) * Complex.I * ((-m : ℤ) : ℂ) /
      (16 : ℂ) = -(angle : ℂ) * Complex.I := by simpa using hneg
  norm_num only [Nat.cast_ofNat] at ⊢
  rw [hpos', hneg', ← Complex.two_cos, ← Complex.ofReal_cos]

/-- Character-pair identity with a natural frequency multiplier and the
canonical representative of a `ZMod 16` frequency. -/
theorem stdAddChar_mul_add_neg_eq_two_cos
    (k : ℕ) (j : ZMod 16) :
    ZMod.stdAddChar ((k : ZMod 16) * j) +
        ZMod.stdAddChar (-((k : ZMod 16) * j)) =
      2 * (Real.cos (Real.pi * k * j.val / 8) : ℂ) := by
  have h := stdAddChar_add_neg_eq_two_cos ((k * j.val : ℕ) : ℤ)
  have hj : (j.val : ZMod 16) = j := ZMod.natCast_zmod_val j
  simpa [Nat.cast_mul, hj, mul_assoc] using h

/-- The transform of the exact six-shift kernel is the three-cosine harmonic
formula. -/
theorem decimalSeventeenKernel_dft_eq_harmonic (j : ZMod 16) :
    ZMod.dft decimalSeventeenCorrelationKernel (-j) =
      (decimalSeventeenHarmonicValue j.val : ℂ) := by
  have hexpansion :
      ZMod.dft decimalSeventeenCorrelationKernel (-j) =
        1 + (1 / 8 : ℂ) *
          ((ZMod.stdAddChar ((1 : ZMod 16) * j) +
              ZMod.stdAddChar (-((1 : ZMod 16) * j))) +
            (ZMod.stdAddChar ((3 : ZMod 16) * j) +
              ZMod.stdAddChar (-((3 : ZMod 16) * j))) +
            (ZMod.stdAddChar ((5 : ZMod 16) * j) +
              ZMod.stdAddChar (-((5 : ZMod 16) * j)))) := by
    rw [ZMod.dft_apply]
    simp only [mul_neg, neg_neg, smul_eq_mul]
    have hsum :
        (∑ u : ZMod 16,
          ZMod.stdAddChar (u * j) * decimalSeventeenCorrelationKernel u) =
        ∑ u : Fin 16,
          ZMod.stdAddChar ((ZMod.finEquiv 16 u) * j) *
            decimalSeventeenCorrelationKernel (ZMod.finEquiv 16 u) := by
      apply Fintype.sum_equiv (ZMod.finEquiv 16).symm
      intro u
      simp
    rw [hsum]
    simp [Fin.sum_univ_succ, decimalSeventeenCorrelationKernel_certificate,
      NField.Alignment.PrimeCosetFourierSpectrum.zmod_finEquiv_apply_eq_natCast]
    norm_num
    rw [show (15 : ZMod 16) = -(1 : ZMod 16) by decide,
      show (13 : ZMod 16) = -(3 : ZMod 16) by decide,
      show (11 : ZMod 16) = -(5 : ZMod 16) by decide]
    simp only [neg_mul]
    simp only [show (1 : ZMod 16) ≠ 0 by decide,
      show (2 : ZMod 16) ≠ 0 by decide,
      show (3 : ZMod 16) ≠ 0 by decide,
      show (4 : ZMod 16) ≠ 0 by decide,
      show (5 : ZMod 16) ≠ 0 by decide,
      show (6 : ZMod 16) ≠ 0 by decide,
      show (7 : ZMod 16) ≠ 0 by decide,
      show (8 : ZMod 16) ≠ 0 by decide,
      show (9 : ZMod 16) ≠ 0 by decide,
      show (10 : ZMod 16) ≠ 0 by decide,
      show (-(5 : ZMod 16)) ≠ 0 by decide,
      show (12 : ZMod 16) ≠ 0 by decide,
      show (-(3 : ZMod 16)) ≠ 0 by decide,
      show (14 : ZMod 16) ≠ 0 by decide,
      show (-(1 : ZMod 16)) ≠ 0 by decide,
      if_false, zero_add]
    ring_nf
  rw [hexpansion]
  have hpairOne :
      ZMod.stdAddChar ((1 : ZMod 16) * j) +
          ZMod.stdAddChar (-((1 : ZMod 16) * j)) =
        2 * (Real.cos (Real.pi * 1 * j.val / 8) : ℂ) := by
    simpa using stdAddChar_mul_add_neg_eq_two_cos 1 j
  have hpairThree :
      ZMod.stdAddChar ((3 : ZMod 16) * j) +
          ZMod.stdAddChar (-((3 : ZMod 16) * j)) =
        2 * (Real.cos (Real.pi * 3 * j.val / 8) : ℂ) := by
    simpa using stdAddChar_mul_add_neg_eq_two_cos 3 j
  have hpairFive :
      ZMod.stdAddChar ((5 : ZMod 16) * j) +
          ZMod.stdAddChar (-((5 : ZMod 16) * j)) =
        2 * (Real.cos (Real.pi * 5 * j.val / 8) : ℂ) := by
    simpa using stdAddChar_mul_add_neg_eq_two_cos 5 j
  rw [hpairOne, hpairThree, hpairFive]
  unfold decimalSeventeenHarmonicValue
  push_cast
  ring_nf

end NField.Alignment.DecimalSeventeenFourierSpectrum

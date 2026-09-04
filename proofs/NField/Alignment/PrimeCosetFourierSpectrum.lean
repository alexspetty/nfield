/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimeCosetOrdering

/-!
# Prime coset Fourier spectrum

This module identifies the actual prime cross-alignment matrix, after the
proved multiplicative-coset permutation, with the block-circulant equality
kernel whose complete Fourier decomposition was established in
`CosetFourierReduction`.
-/

namespace NField.Alignment.PrimeCosetFourierSpectrum

open scoped BigOperators
open NField.Alignment
open NField.Alignment.CrossAlignmentMatrix
open NField.Alignment.CoherenceDecomposition
open NField.Alignment.CosetFourierReduction
open NField.Alignment.PrimeCosetOrdering

noncomputable local instance primeOrbitQuotientFintype {b p : ℕ}
    (hp : p.Prime) (hpb : ¬p ∣ b) : Fintype (PrimeOrbitQuotient hp hpb) :=
  Fintype.ofFinite _

theorem zmod_finEquiv_apply_val (n : ℕ) [NeZero n] (x : Fin n) :
    (ZMod.finEquiv n x).val = x.val := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

theorem zmod_finEquiv_apply_eq_natCast (n : ℕ) [NeZero n] (x : Fin n) :
    ZMod.finEquiv n x = (x.val : ZMod n) := by
  apply ZMod.val_injective n
  rw [zmod_finEquiv_apply_val, ZMod.val_natCast,
    Nat.mod_eq_of_lt x.isLt]

/-- Canonical conversion from a cyclic `ZMod L` phase to its exponent in
`0, ..., L-1`. -/
noncomputable def primePeriodZModFinEquiv {b p : ℕ}
    (hp : p.Prime) (hpb : ¬p ∣ b) :
    ZMod (primeBasePeriod b p hp hpb) ≃
      Fin (primeBasePeriod b p hp hpb) := by
  letI : NeZero (primeBasePeriod b p hp hpb) :=
    ⟨(primeBasePeriod_pos hp hpb).ne'⟩
  exact (ZMod.finEquiv (primeBasePeriod b p hp hpb)).symm.toEquiv

@[simp] theorem primePeriodZModFinEquiv_val {b p : ℕ}
    (hp : p.Prime) (hpb : ¬p ∣ b)
    (r : ZMod (primeBasePeriod b p hp hpb)) :
    (primePeriodZModFinEquiv hp hpb r).val = r.val := by
  let L := primeBasePeriod b p hp hpb
  letI : NeZero L := ⟨(primeBasePeriod_pos hp hpb).ne'⟩
  have h := (ZMod.finEquiv L).apply_symm_apply r
  calc
    ((ZMod.finEquiv L).symm r).val =
        (ZMod.finEquiv L ((ZMod.finEquiv L).symm r)).val :=
      (zmod_finEquiv_apply_val L _).symm
    _ = r.val := congrArg ZMod.val h

/-- The manuscript's coset and cyclic exponent ordering, with exponent
coordinates represented by `ZMod L` for Fourier analysis. -/
noncomputable def primeCosetResidueEquiv {b p : ℕ}
    (hp : p.Prime) (hpb : ¬p ∣ b) :
    PrimeOrbitQuotient hp hpb × ZMod (primeBasePeriod b p hp hpb) ≃
      PrimeResidue p := by
  letI : NeZero (primeBasePeriod b p hp hpb) :=
    ⟨(primeBasePeriod_pos hp hpb).ne'⟩
  exact (Equiv.prodCongr (Equiv.refl (PrimeOrbitQuotient hp hpb))
      (primePeriodZModFinEquiv hp hpb)).trans
    ((primeCosetOrderingEquiv hp hpb).trans
      (primeResidueUnitEquiv hp).symm)

/-- The unit behind an ordered natural residue is exactly representative
times the declared power of the base. -/
theorem primeResidueUnitEquiv_primeCosetResidueEquiv {b p : ℕ}
    (hp : p.Prime) (hpb : ¬p ∣ b)
    (C : PrimeOrbitQuotient hp hpb)
    (r : ZMod (primeBasePeriod b p hp hpb)) :
    primeResidueUnitEquiv hp (primeCosetResidueEquiv hp hpb (C, r)) =
      primeCosetOrdering hp hpb
        (C, primePeriodZModFinEquiv hp hpb r) := by
  letI : NeZero (primeBasePeriod b p hp hpb) :=
    ⟨(primeBasePeriod_pos hp hpb).ne'⟩
  simp [primeCosetResidueEquiv, primePeriodZModFinEquiv,
    primeCosetOrderingEquiv_apply]

/-- Base-`b` digit word carried by the fixed representative of each prime
orbit coset. -/
noncomputable def primeCosetDigitWord {b p : ℕ}
    (hb : 0 < b) (hp : p.Prime) (hpb : ¬p ∣ b) :
    PrimeOrbitQuotient hp hpb →
      ZMod (primeBasePeriod b p hp hpb) → Fin b := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Fact p.Prime := ⟨hp⟩
  intro C t
  exact ⟨primeOrbitDigit hp hpb (primeOrbitRepresentative hp hpb C) t.val,
    digitBin_lt_base hb hp.pos (ZMod.val_lt _)⟩

@[simp] theorem primeCosetDigitWord_val {b p : ℕ}
    (hb : 0 < b) (hp : p.Prime) (hpb : ¬p ∣ b)
    (C : PrimeOrbitQuotient hp hpb)
    (t : ZMod (primeBasePeriod b p hp hpb)) :
    (primeCosetDigitWord hb hp hpb C t).val =
      primeOrbitDigit hp hpb (primeOrbitRepresentative hp hpb C) t.val := by
  rfl

/-- The digit emitted by an actually ordered residue at a natural clock
position is the coset word at the translated cyclic coordinate. -/
theorem digitAt_primeCosetResidueEquiv {b p : ℕ}
    (hb : 0 < b) (hp : p.Prime) (hpb : ¬p ∣ b)
    (C : PrimeOrbitQuotient hp hpb)
    (r : ZMod (primeBasePeriod b p hp hpb)) (position : ℕ) :
    digitAt b p (primeCosetResidueEquiv hp hpb (C, r)).val position =
      (primeCosetDigitWord hb hp hpb C
        ((position : ZMod (primeBasePeriod b p hp hpb)) + r)).val := by
  let L := primeBasePeriod b p hp hpb
  letI : NeZero L := ⟨(primeBasePeriod_pos hp hpb).ne'⟩
  have hunit := primeResidueUnitEquiv_primeCosetResidueEquiv hp hpb C r
  have hdigit := primeOrbitDigit_primeResidue hp hpb
    (primeCosetResidueEquiv hp hpb (C, r)) position
  rw [hunit, primeCosetOrdering_digit_shift] at hdigit
  rw [primeCosetDigitWord_val, ← hdigit,
    primePeriodZModFinEquiv_val]
  have hval :
      ((position : ZMod L) + r).val = (position + r.val) % L := by
    rw [ZMod.val_add, ZMod.val_natCast]
    simp [Nat.add_mod]
  rw [hval]
  exact (primeOrbitDigit_mod_period hp hpb
    (primeOrbitRepresentative hp hpb C) (position + r.val)).symm

/-! ## Actual prime matrix as the equality-word block kernel -/

/-- Complex scalar extension of the literal rational prime matrix. -/
noncomputable def primeCrossAlignmentMatrixComplex
    (b p length : ℕ) : Matrix (PrimeResidue p) (PrimeResidue p) ℂ :=
  (primeCrossAlignmentMatrix b p length).map (Rat.castHom ℂ)

/-- Equality-correlation kernel of the actual coset words, with the positivity
of the prime period packaged inside the definition. -/
noncomputable def primeCosetCorrelationKernel {b p : ℕ}
    (hb : 0 < b) (hp : p.Prime) (hpb : ¬p ∣ b) :
    PrimeOrbitQuotient hp hpb → PrimeOrbitQuotient hp hpb →
      ZMod (primeBasePeriod b p hp hpb) → ℂ := by
  letI : NeZero (primeBasePeriod b p hp hpb) :=
    ⟨(primeBasePeriod_pos hp hpb).ne'⟩
  exact wordCorrelationKernel (primeCosetDigitWord hb hp hpb)

/-- Block-circulant matrix assembled from the actual prime coset words. -/
noncomputable def primeCosetBlockCirculantMatrix {b p : ℕ}
    (hb : 0 < b) (hp : p.Prime) (hpb : ¬p ∣ b) :
    Matrix
      (PrimeOrbitQuotient hp hpb × ZMod (primeBasePeriod b p hp hpb))
      (PrimeOrbitQuotient hp hpb × ZMod (primeBasePeriod b p hp hpb)) ℂ := by
  letI : NeZero (primeBasePeriod b p hp hpb) :=
    ⟨(primeBasePeriod_pos hp hpb).ne'⟩
  exact blockCirculantMatrix (primeCosetCorrelationKernel hb hp hpb)

/-- One actual prime-matrix entry, in coset coordinates, equals the declared
normalized cyclic equality-correlation block. -/
theorem primeCrossAlignmentMatrixComplex_coset_entry {b p : ℕ}
    (hb : 0 < b) (hp : p.Prime) (hpb : ¬p ∣ b)
    (C D : PrimeOrbitQuotient hp hpb)
    (r s : ZMod (primeBasePeriod b p hp hpb)) :
    primeCrossAlignmentMatrixComplex b p (primeBasePeriod b p hp hpb)
        (primeCosetResidueEquiv hp hpb (C, r))
        (primeCosetResidueEquiv hp hpb (D, s)) =
      primeCosetCorrelationKernel hb hp hpb C D (r - s) := by
  let L := primeBasePeriod b p hp hpb
  letI : NeZero L := ⟨(primeBasePeriod_pos hp hpb).ne'⟩
  unfold primeCrossAlignmentMatrixComplex primeCrossAlignmentMatrix
  simp only [Matrix.map_apply]
  unfold primePairPositionMatchCount primeCosetCorrelationKernel
  unfold wordCorrelationKernel
  change
    (((((Finset.range L).filter
      (fun position =>
        digitAt b p (primeCosetResidueEquiv hp hpb (C, r)).val position =
          digitAt b p (primeCosetResidueEquiv hp hpb (D, s)).val position)).card : ℚ) /
      (L : ℚ) : ℚ) : ℂ) =
      (L : ℂ)⁻¹ *
        ∑ t : ZMod L,
          if primeCosetDigitWord hb hp hpb C (t + (r - s)) =
              primeCosetDigitWord hb hp hpb D t
          then 1 else 0
  rw [Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast]
  rw [Finset.card_eq_sum_ones]
  push_cast
  rw [div_eq_inv_mul]
  congr 1
  rw [Finset.sum_filter]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Fintype.sum_equiv
    ((ZMod.finEquiv L).toEquiv.trans (Equiv.addRight s))
  intro t
  rw [digitAt_primeCosetResidueEquiv hb hp hpb C r t.val,
    digitAt_primeCosetResidueEquiv hb hp hpb D s t.val]
  simp only [Equiv.trans_apply]
  have hphase :
      (Equiv.addRight s) ((ZMod.finEquiv L).toEquiv t) =
        (t.val : ZMod L) + s := by
    exact congrArg (fun z : ZMod L => z + s)
      (zmod_finEquiv_apply_eq_natCast L t)
  simp only [hphase]
  change
    (if (primeCosetDigitWord hb hp hpb C ((t : ZMod L) + r)).val =
          (primeCosetDigitWord hb hp hpb D ((t : ZMod L) + s)).val
      then (1 : ℂ) else 0) =
      if primeCosetDigitWord hb hp hpb C
            (((t : ZMod L) + s) + (r - s)) =
          primeCosetDigitWord hb hp hpb D ((t : ZMod L) + s)
      then 1 else 0
  rw [show ((t : ZMod L) + s) + (r - s) = (t : ZMod L) + r by ring]
  simp only [Fin.val_inj]

/-- Exact permutation equality between the literal prime matrix and the
block-circulant equality kernel. -/
theorem primeCrossAlignmentMatrixComplex_reindex_eq_blockCirculant
    {b p : ℕ} (hb : 0 < b) (hp : p.Prime) (hpb : ¬p ∣ b) :
    Matrix.reindex (primeCosetResidueEquiv hp hpb).symm
        (primeCosetResidueEquiv hp hpb).symm
        (primeCrossAlignmentMatrixComplex b p
          (primeBasePeriod b p hp hpb)) =
      primeCosetBlockCirculantMatrix hb hp hpb := by
  ext i j
  rcases i with ⟨C, r⟩
  rcases j with ⟨D, s⟩
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
  unfold primeCosetBlockCirculantMatrix blockCirculantMatrix
  exact primeCrossAlignmentMatrixComplex_coset_entry hb hp hpb C D r s

/-! ## Complete direct-sum Fourier conjugation -/

/-- The concrete small Fourier matrix at frequency `j`. -/
noncomputable def primeCosetFourierSymbol {b p : ℕ}
    (hb : 0 < b) (hp : p.Prime) (hpb : ¬p ∣ b)
    (j : ZMod (primeBasePeriod b p hp hpb)) :
    Matrix (PrimeOrbitQuotient hp hpb) (PrimeOrbitQuotient hp hpb) ℂ := by
  letI : NeZero (primeBasePeriod b p hp hpb) :=
    ⟨(primeBasePeriod_pos hp hpb).ne'⟩
  exact blockFourierSymbol (primeCosetCorrelationKernel hb hp hpb) j

/-- Declared negative-sign Fourier coefficient of one concrete coset word. -/
noncomputable def primeCosetFourierCoefficient {b p : ℕ}
    (hb : 0 < b) (hp : p.Prime) (hpb : ¬p ∣ b)
    (C : PrimeOrbitQuotient hp hpb) (d : Fin b)
    (j : ZMod (primeBasePeriod b p hp hpb)) : ℂ := by
  letI : NeZero (primeBasePeriod b p hp hpb) :=
    ⟨(primeBasePeriod_pos hp hpb).ne'⟩
  exact wordFourierCoefficient
    (primeCosetDigitWord hb hp hpb) C d j

/-- Complete synthesis from all concrete frequency slices. -/
noncomputable def primeCosetFourierSynthesis {b p : ℕ}
    (hp : p.Prime) (hpb : ¬p ∣ b) :
    (ZMod (primeBasePeriod b p hp hpb) →
      PrimeOrbitQuotient hp hpb → ℂ) →ₗ[ℂ]
    (PrimeOrbitQuotient hp hpb ×
      ZMod (primeBasePeriod b p hp hpb) → ℂ) := by
  letI : NeZero (primeBasePeriod b p hp hpb) :=
    ⟨(primeBasePeriod_pos hp hpb).ne'⟩
  exact blockFourierSynthesis

/-- One concrete frequency slice embedded in the full coset matrix space. -/
noncomputable def primeCosetFrequencyEmbed {b p : ℕ}
    (hp : p.Prime) (hpb : ¬p ∣ b)
    (j : ZMod (primeBasePeriod b p hp hpb))
    (z : PrimeOrbitQuotient hp hpb → ℂ) :
    PrimeOrbitQuotient hp hpb ×
      ZMod (primeBasePeriod b p hp hpb) → ℂ := by
  letI : NeZero (primeBasePeriod b p hp hpb) :=
    ⟨(primeBasePeriod_pos hp hpb).ne'⟩
  exact frequencyEmbed j z

/-- Linear action of the concrete full block matrix, with its finite cyclic
index instance packaged inside the definition. -/
noncomputable def primeCosetBlockAction {b p : ℕ}
    (hb : 0 < b) (hp : p.Prime) (hpb : ¬p ∣ b) :
    (PrimeOrbitQuotient hp hpb ×
        ZMod (primeBasePeriod b p hp hpb) → ℂ) →
      (PrimeOrbitQuotient hp hpb ×
        ZMod (primeBasePeriod b p hp hpb) → ℂ) := by
  letI : NeZero (primeBasePeriod b p hp hpb) :=
    ⟨(primeBasePeriod_pos hp hpb).ne'⟩
  exact Matrix.mulVec (primeCosetBlockCirculantMatrix hb hp hpb)

/-- The concrete small matrix is exactly the Hermitian Fourier-coefficient
Gram matrix displayed in the manuscript. -/
theorem primeCosetFourierSymbol_eq_frequencyGram {b p : ℕ}
    (hb : 0 < b) (hp : p.Prime) (hpb : ¬p ∣ b)
    (j : ZMod (primeBasePeriod b p hp hpb)) :
    primeCosetFourierSymbol hb hp hpb j =
      fun C D => ((primeBasePeriod b p hp hpb : ℕ) : ℂ)⁻¹ *
        ∑ d : Fin b,
          starRingEnd ℂ (primeCosetFourierCoefficient hb hp hpb C d j) *
            primeCosetFourierCoefficient hb hp hpb D d j := by
  letI : NeZero (primeBasePeriod b p hp hpb) :=
    ⟨(primeBasePeriod_pos hp hpb).ne'⟩
  unfold primeCosetFourierSymbol primeCosetCorrelationKernel
  simp only [primeCosetFourierCoefficient]
  exact blockFourierSymbol_wordCorrelationKernel
    (primeCosetDigitWord hb hp hpb) j

/-- Complete Fourier certificate.  Synthesis is bijective, and under that
change of coordinates the actual reindexed prime matrix acts independently
by the declared small matrix at each frequency.  This is the exact
multiplicity-preserving spectral-union statement. -/
theorem primeCosetFourier_directSum_complete {b p : ℕ}
    (hb : 0 < b) (hp : p.Prime) (hpb : ¬p ∣ b) :
    Function.Bijective (primeCosetFourierSynthesis hp hpb) ∧
    ∀ c : ZMod (primeBasePeriod b p hp hpb) →
        PrimeOrbitQuotient hp hpb → ℂ,
      primeCosetBlockAction hb hp hpb
          (primeCosetFourierSynthesis hp hpb c) =
        primeCosetFourierSynthesis hp hpb
          (fun j => Matrix.mulVec
            (primeCosetFourierSymbol hb hp hpb j) (c j)) := by
  letI : NeZero (primeBasePeriod b p hp hpb) :=
    ⟨(primeBasePeriod_pos hp hpb).ne'⟩
  constructor
  · unfold primeCosetFourierSynthesis
    exact blockFourierSynthesis_bijective
  · intro c
    unfold primeCosetBlockAction primeCosetBlockCirculantMatrix
      primeCosetFourierSymbol primeCosetFourierSynthesis
    exact blockCirculantMatrix_mulVec_blockFourierSynthesis
      (primeCosetCorrelationKernel hb hp hpb) c

/-- A synthesized vector lies in the full kernel exactly when every one of
its frequency slices lies in the corresponding small-symbol kernel. -/
theorem primeCosetBlockAction_eq_zero_iff {b p : ℕ}
    (hb : 0 < b) (hp : p.Prime) (hpb : ¬p ∣ b)
    (c : ZMod (primeBasePeriod b p hp hpb) →
      PrimeOrbitQuotient hp hpb → ℂ) :
    primeCosetBlockAction hb hp hpb
        (primeCosetFourierSynthesis hp hpb c) = 0 ↔
      ∀ j, Matrix.mulVec (primeCosetFourierSymbol hb hp hpb j) (c j) = 0 := by
  have hdirect := primeCosetFourier_directSum_complete hb hp hpb
  rw [hdirect.2 c]
  constructor
  · intro hzero j
    have hslices :
        (fun j => Matrix.mulVec
          (primeCosetFourierSymbol hb hp hpb j) (c j)) = 0 := by
      apply hdirect.1.1
      simpa using hzero
    exact congrFun hslices j
  · intro hslices
    have hzero :
        (fun j => Matrix.mulVec
          (primeCosetFourierSymbol hb hp hpb j) (c j)) = 0 := by
      funext j
      exact hslices j
    rw [hzero]
    exact LinearMap.map_zero _

/-- The full reindexed block action is kernel-free exactly when every small
Fourier symbol is kernel-free. -/
theorem primeCosetBlockAction_kernel_free_iff_symbols {b p : ℕ}
    (hb : 0 < b) (hp : p.Prime) (hpb : ¬p ∣ b) :
    (∀ v, primeCosetBlockAction hb hp hpb v = 0 → v = 0) ↔
      ∀ j z, Matrix.mulVec (primeCosetFourierSymbol hb hp hpb j) z = 0 →
        z = 0 := by
  have hdirect := primeCosetFourier_directSum_complete hb hp hpb
  constructor
  · intro hfull j z hz
    let c : ZMod (primeBasePeriod b p hp hpb) →
        PrimeOrbitQuotient hp hpb → ℂ :=
      fun k => if k = j then z else 0
    have hslices : ∀ k,
        Matrix.mulVec (primeCosetFourierSymbol hb hp hpb k) (c k) = 0 := by
      intro k
      by_cases hkj : k = j
      · subst k
        simpa [c] using hz
      · simp [c, hkj]
    have hvector : primeCosetFourierSynthesis hp hpb c = 0 :=
      hfull _ ((primeCosetBlockAction_eq_zero_iff hb hp hpb c).2 hslices)
    have hc : c = 0 := hdirect.1.1 (by simpa using hvector)
    have hj := congrFun hc j
    simpa [c] using hj
  · intro hsymbols v hv
    obtain ⟨c, rfl⟩ := hdirect.1.2 v
    have hslices :=
      (primeCosetBlockAction_eq_zero_iff hb hp hpb c).1 hv
    have hc : c = 0 := by
      funext j
      exact hsymbols j (c j) (hslices j)
    rw [hc]
    exact LinearMap.map_zero _

/-- Every eigenvector of a concrete small Fourier block lifts to an
eigenvector of the actual reindexed prime matrix. -/
theorem primeCosetFourier_eigenvector_lift {b p : ℕ}
    (hb : 0 < b) (hp : p.Prime) (hpb : ¬p ∣ b)
    (j : ZMod (primeBasePeriod b p hp hpb))
    (z : PrimeOrbitQuotient hp hpb → ℂ) (eigenvalue : ℂ)
    (hz : Matrix.mulVec (primeCosetFourierSymbol hb hp hpb j) z =
      eigenvalue • z) :
    primeCosetBlockAction hb hp hpb
        (primeCosetFrequencyEmbed hp hpb j z) =
      eigenvalue • primeCosetFrequencyEmbed hp hpb j z := by
  letI : NeZero (primeBasePeriod b p hp hpb) :=
    ⟨(primeBasePeriod_pos hp hpb).ne'⟩
  unfold primeCosetFourierSymbol at hz
  unfold primeCosetBlockAction primeCosetBlockCirculantMatrix
    primeCosetFrequencyEmbed
  exact frequencyEmbed_eigenvector
    (primeCosetCorrelationKernel hb hp hpb) j z eigenvalue hz

end NField.Alignment.PrimeCosetFourierSpectrum

/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.BaseTwoSevenSpectrum
import NField.Alignment.DecimalPrimeMatrixSpectra
import NField.Alignment.SpectralExcessIdentity
import NField.Alignment.TwoLevelFourierRigidity

/-!
# The Spectral Structure of Fractional Fields

## Coverage

The finite spectral structure is formalized through digit-bin rank and nullity
bounds, Fourier Gram blocks, the squared-eigenvalue identity and two-level
rigidity. The results apply to the actual prime cross-alignment matrix under
the stated prime and coprimality hypotheses.

## Scope and assumptions

The occupied-bin and prime-matrix statements retain their prime and
coprimality hypotheses. The overlap rigidity theorem uses nonnegative overlap;
its converse is also proved. The forced-nullity conclusion retains the
conditions `L > 1` and `C ≥ ν`. The finite examples have exact rational
values. The additive digit-bin transform and later analytic objects are
outside this multiplicative orbit-frequency formalization.
-/

namespace NField.Papers.SpectralStructure

open scoped BigOperators
open NField.Alignment
open NField.Alignment.BaseTwoSevenSpectrum
open NField.Alignment.CrossAlignmentMatrix
open NField.Alignment.CosetFourierReduction
open NField.Alignment.DecimalOrbitSpectra
open NField.Alignment.DecimalPrimeMatrixSpectra
open NField.Alignment.PrimeCosetOrdering
open NField.Alignment.PrimeCosetFourierSpectrum
open NField.Alignment.SpectralExcessIdentity
open NField.Alignment.SpectralStructure
open NField.Alignment.TwoLevelFourierRigidity

noncomputable local instance primeOrbitQuotientFintype {b p : ℕ}
    (hp : p.Prime) (hpb : ¬p ∣ b) : Fintype (PrimeOrbitQuotient hp hpb) :=
  Fintype.ofFinite _

/-- Exact occupied-digit count from the intrinsic long-division digit map. -/
theorem occupied_digit_count {b p : ℕ} (hb : 0 < b) (hp : Nat.Prime p)
    (hpb : ¬p ∣ b) :
    (occupiedDigits b p).card = min b (p - 1) :=
  occupiedDigits_card hb hp hpb

/-- The digit indicators partition unity, so their Fourier coefficients sum
to zero at every nonzero orbit frequency. -/
theorem orbit_symbol_partition_of_unity
    {L : ℕ} [NeZero L] {a κ : Type*} [Fintype κ] [DecidableEq κ]
    (word : a → ZMod L → κ) (i : a) {j : ZMod L} (hj : j ≠ 0) :
    ∑ d, wordFourierCoefficient word i d j = 0 :=
  sum_wordFourierCoefficient_eq_zero word i hj

/-- Changing the chosen cyclic representative of an orbit contributes exactly
the corresponding Fourier phase. -/
theorem orbit_representative_shift_phase
    {L : ℕ} [NeZero L] {a κ : Type*} [DecidableEq κ]
    (word : a → ZMod L → κ) (q : a → ZMod L)
    (i : a) (d : κ) (j : ZMod L) :
    wordFourierCoefficient (fun i t => word i (t + q i)) i d j =
      ZMod.stdAddChar (q i * j) * wordFourierCoefficient word i d j :=
  wordFourierCoefficient_shift word q i d j

/-- Opposite orbit frequencies carry conjugate Fourier coefficients. -/
theorem conjugate_orbit_frequency_coefficients
    {L : ℕ} [NeZero L] {a κ : Type*} [DecidableEq κ]
    (word : a → ZMod L → κ) (i : a) (d : κ) (j : ZMod L) :
    wordFourierCoefficient word i d (-j) =
      starRingEnd ℂ (wordFourierCoefficient word i d j) :=
  wordFourierCoefficient_neg word i d j

/-- The literal prime matrix, its Fourier Gram symbols, and the complete
simultaneous direct-sum action agree exactly. -/
theorem actual_prime_fourier_factorization
    {b p : ℕ} (hb : 0 < b) (hp : p.Prime) (hpb : ¬p ∣ b) :
    Matrix.reindex (primeCosetResidueEquiv hp hpb).symm
        (primeCosetResidueEquiv hp hpb).symm
        (primeCrossAlignmentMatrixComplex b p
          (primeBasePeriod b p hp hpb)) =
      primeCosetBlockCirculantMatrix hb hp hpb ∧
    (∀ j : ZMod (primeBasePeriod b p hp hpb),
      primeCosetFourierSymbol hb hp hpb j =
        fun C D => ((primeBasePeriod b p hp hpb : ℕ) : ℂ)⁻¹ *
          ∑ d : Fin b,
            starRingEnd ℂ (primeCosetFourierCoefficient hb hp hpb C d j) *
              primeCosetFourierCoefficient hb hp hpb D d j) ∧
    Function.Bijective (primeCosetFourierSynthesis hp hpb) ∧
    ∀ c : ZMod (primeBasePeriod b p hp hpb) →
        PrimeOrbitQuotient hp hpb → ℂ,
      primeCosetBlockAction hb hp hpb
          (primeCosetFourierSynthesis hp hpb c) =
        primeCosetFourierSynthesis hp hpb
          (fun j => Matrix.mulVec
            (primeCosetFourierSymbol hb hp hpb j) (c j)) := by
  have hdirect := primeCosetFourier_directSum_complete hb hp hpb
  exact ⟨primeCrossAlignmentMatrixComplex_reindex_eq_blockCirculant
      hb hp hpb,
    primeCosetFourierSymbol_eq_frequencyGram hb hp hpb,
    hdirect.1, hdirect.2⟩

/-- The full reindexed prime action is kernel-free exactly when every one of
its finite orbit-frequency symbols is kernel-free. -/
theorem actual_prime_kernel_free_iff_frequency_blocks
    {b p : ℕ} (hb : 0 < b) (hp : p.Prime) (hpb : ¬p ∣ b) :
    (∀ v, primeCosetBlockAction hb hp hpb v = 0 → v = 0) ↔
      ∀ j z, Matrix.mulVec (primeCosetFourierSymbol hb hp hpb j) z = 0 →
        z = 0 :=
  primeCosetBlockAction_kernel_free_iff_symbols hb hp hpb

/-- The manuscript's global rank and rank-nullity ledger from the symbol
matrices and their partition-of-unity Fourier constraint. -/
theorem rank_nullity_ledger {L ν C : ℕ}
    (hL : 0 < L) (hν : 0 < ν) (hνC : ν ≤ C)
    (Y : Fin L → Matrix (Fin ν) (Fin C) ℂ)
    (hpartition : ∀ j : Fin L, j.val ≠ 0 → ∀ a, ∑ d, Y j d a = 0) :
    spectralRank Y ≤ min C ν + (L - 1) * min C (ν - 1) ∧
      spectralRank Y + spectralNullity Y = C * L ∧
      L * (C - ν + 1) - 1 ≤ spectralNullity Y := by
  exact ⟨spectralRank_bound hL hν Y hpartition,
    spectralRank_add_spectralNullity Y,
    spectralNullity_forced hL hν hνC Y hpartition⟩

/-- The forced-nullity bound is strictly positive in every nontrivial
multi-frequency field covered by the corollary. -/
theorem forced_kernel {L ν C : ℕ}
    (hL : 1 < L) (hν : 0 < ν) (hνC : ν ≤ C)
    (Y : Fin L → Matrix (Fin ν) (Fin C) ℂ)
    (hpartition : ∀ j : Fin L, j.val ≠ 0 → ∀ a, ∑ d, Y j d a = 0) :
    0 < spectralNullity Y :=
  spectralNullity_positive hL hν hνC Y hpartition

/-- Exact local kernel identity for every positive normalized Fourier Gram
block. -/
theorem fourier_block_kernel
    {a d : Type*} [Fintype a] [Fintype d]
    {length : ℕ} (hlength : 0 < length)
    (X : a → EuclideanSpace ℂ d) (z : a → ℂ) :
    Matrix.mulVec (frequencyGram length X) z = 0 ↔
      ∑ i, z i • X i = 0 :=
  frequencyGram_mulVec_eq_zero_iff hlength X z

/-- The primitive one-channel eigenvalue is nonnegative and is bounded by
the corresponding zero-frequency count energy. -/
theorem primitive_fiber_energy_bound
    {d : Type*} [Fintype d] (length : ℕ) (X : d → ℂ)
    (counts : d → ℝ) (hbound : ∀ digit, ‖X digit‖ ≤ counts digit) :
    0 ≤ primitiveFiberEnergy length X ∧
      primitiveFiberEnergy length X ≤
        (length : ℝ)⁻¹ * ∑ digit, (counts digit) ^ 2 :=
  ⟨primitiveFiberEnergy_nonnegative length X,
    primitiveFiberEnergy_le_countEnergy length X counts hbound⟩

/-- The exact quadratic branch formula, expressed through its trace,
determinant, and characteristic equation. -/
theorem two_coset_branch_formula {length q₁ q₂ zSq : ℝ}
    (hlength : length ≠ 0) (hz : 0 ≤ zSq) :
    twoCosetPlus length q₁ q₂ zSq +
        twoCosetMinus length q₁ q₂ zSq = (q₁ + q₂) / length ∧
      twoCosetPlus length q₁ q₂ zSq *
        twoCosetMinus length q₁ q₂ zSq =
          (q₁ * q₂ - zSq) / length ^ 2 ∧
      ∀ branch ∈ [twoCosetPlus length q₁ q₂ zSq,
          twoCosetMinus length q₁ q₂ zSq],
        branch ^ 2 - ((q₁ + q₂) / length) * branch +
          (q₁ * q₂ - zSq) / length ^ 2 = 0 := by
  exact ⟨twoCoset_branches_sum hlength,
    twoCoset_branches_product hlength hz,
    twoCoset_branch_characteristic hlength hz⟩

/-- Exact support-rigidity theorem used in the two-level collapse argument. -/
theorem two_level_overlap_rigidity
    {G : Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]
    (Q : G → ℕ) (hmass : 0 < ∑ t, Q t) :
    (∀ shift : G, shift ≠ 0 → overlapMass Q shift = 0) ↔
      ∃ s : G, ∃ mass : ℕ, mass = ∑ u, Q u ∧
        Q = fun t => if t = s then mass else 0 :=
  overlap_zero_iff_point_mass Q hmass

/-- Complete Fourier form of the two-level rigidity theorem: a nonzero
nonnegative cyclic count has constant squared Fourier magnitude exactly when
it is supported at one shift. -/
theorem two_level_fourier_rigidity
    {L : ℕ} [NeZero L] (Q : ZMod L → ℕ)
    (hmass : 0 < ∑ t, Q t) :
    (∃ mass : ℕ, 0 < mass ∧ ∀ j,
        Complex.normSq (naturalDFT Q j) = (mass : ℝ) ^ 2) ↔
      ∃ s : ZMod L, ∃ mass : ℕ, 0 < mass ∧
        Q = fun t => if t = s then mass else 0 :=
  constant_normSq_iff_pointMass Q hmass

/-- Exact zero characterization of the manuscript's off-diagonal energy for
the actual synchronized prime matrix. -/
theorem spectral_excess_zero_characterization
    {b p length : ℕ} (hb : 0 < b) (hp : Nat.Prime p)
    (hpb : ¬p ∣ b) (hlength : 0 < length) :
    offDiagonalSquareEnergy (primeCrossAlignmentMatrix b p length) = 0 ↔
      p ≤ b + 1 :=
  prime_offDiagonalEnergy_eq_zero_iff_le hb hp hpb hlength

/-- The full squared-eigenvalue excess identity and its sharp zero boundary
for the actual synchronized prime matrix. -/
theorem actual_prime_spectral_excess
    {b p length : ℕ} (hb : 0 < b) (hp : Nat.Prime p)
    (hpb : ¬p ∣ b) (hlength : 0 < length) :
    (∑ i,
        ((primeCrossAlignmentMatrixReal_isHermitian b p length).eigenvalues i -
          1) ^ 2 =
        realOffDiagonalSquareEnergy
          (primeCrossAlignmentMatrixReal b p length)) ∧
      (realOffDiagonalSquareEnergy
          (primeCrossAlignmentMatrixReal b p length) = 0 ↔
        p ≤ b + 1) :=
  ⟨primeCrossAlignmentMatrix_spectral_excess hlength,
    primeCrossAlignmentMatrix_realOffDiagonal_eq_zero_iff_le
      hb hp hpb hlength⟩

/-- The four displayed base-seven orbit words are the literal digit streams,
not stand-in fixtures. -/
theorem base_seven_literal_orbit_words :
    (List.ofFn fun t : Fin 3 => digitAt 2 7 1 t.val) = [0, 0, 1] ∧
    (List.ofFn fun t : Fin 3 => digitAt 2 7 3 t.val) = [0, 1, 1] ∧
    (List.ofFn fun t : Fin 3 => digitAt 4 7 1 t.val) = [0, 2, 1] ∧
    (List.ofFn fun t : Fin 3 => digitAt 4 7 3 t.val) = [1, 2, 3] :=
  baseSeven_orbit_words_actual

/-- Exact sharpness for the literal base-two prime-seven matrix: its rank is
four and its nullity is two. -/
theorem base_two_seven_actual_sharpness :
    (primeCrossAlignmentMatrix 2 7 3).rank = 4 ∧
      Module.finrank ℚ
        (primeCrossAlignmentMatrix 2 7 3).mulVecLin.ker = 2 :=
  baseTwoSeven_actual_rank_nullity

/-- Exact prime-thirteen correlation support: the cross-word count is two
only at relative shift three, while both nonzero self-shifts vanish. -/
theorem decimal_thirteen_single_shift_certificate :
    (∀ shift : Fin 6,
      crossCorrelation decimalThirteenLeft decimalThirteenLeft shift =
        if shift = 0 then 6 else 0) ∧
    (∀ shift : Fin 6,
      crossCorrelation decimalThirteenRight decimalThirteenRight shift =
        if shift = 0 then 6 else 0) ∧
    (∀ shift : Fin 6,
      crossCorrelation decimalThirteenLeft decimalThirteenRight shift =
        if shift = 3 then 2 else 0) :=
  decimalThirteenCorrelation_certificate

/-- The literal decimal prime matrix reindexes to the certified two-word
matrix, whose two six-dimensional branches give its complete spectrum. -/
theorem decimal_thirteen_actual_complete_spectrum :
    Matrix.reindex decimalThirteenResidueEquiv.symm
        decimalThirteenResidueEquiv.symm
        (primeCrossAlignmentMatrix 10 13 6) = decimalThirteenMatrix ∧
    ((∀ x : Fin 6 → ℚ,
        Matrix.mulVec decimalThirteenMatrix (decimalThirteenPlusVector x) =
          ((4 : ℚ) / 3) • decimalThirteenPlusVector x) ∧
      (∀ x : Fin 6 → ℚ,
        Matrix.mulVec decimalThirteenMatrix (decimalThirteenMinusVector x) =
          ((2 : ℚ) / 3) • decimalThirteenMinusVector x) ∧
      Function.Injective decimalThirteenPlusVector ∧
      Function.Injective decimalThirteenMinusVector ∧
      (∀ v : Sum (Fin 6) (Fin 6) → ℚ,
        v = decimalThirteenPlusVector
            (decimalThirteenSymmetricCoordinate v) +
          decimalThirteenMinusVector
            (decimalThirteenAntisymmetricCoordinate v)) ∧
      (∀ x y : Fin 6 → ℚ,
        decimalThirteenPlusVector x = decimalThirteenMinusVector y →
          x = 0 ∧ y = 0)) :=
  ⟨decimalThirteen_primeMatrix_reindex, decimalThirteenSpectrum_complete⟩

/-- Exact finite data for the sharp base-two case and both two-coset
contrasts. -/
theorem finite_contrast_certificate :
    ((List.ofFn fun shift : Fin 3 =>
        crossCorrelation baseTwoSevenLeft baseTwoSevenLeft shift) = [3, 1, 1] ∧
      (List.ofFn fun shift : Fin 3 =>
        crossCorrelation baseTwoSevenRight baseTwoSevenRight shift) = [3, 1, 1] ∧
      (List.ofFn fun shift : Fin 3 =>
        crossCorrelation baseTwoSevenLeft baseTwoSevenRight shift) = [2, 2, 0]) ∧
    ((List.ofFn fun shift : Fin 3 =>
        crossCorrelation baseFourSevenLeft baseFourSevenLeft shift) = [3, 0, 0] ∧
      (List.ofFn fun shift : Fin 3 =>
        crossCorrelation baseFourSevenRight baseFourSevenRight shift) = [3, 0, 0] ∧
      (List.ofFn fun shift : Fin 3 =>
        crossCorrelation baseFourSevenRight baseFourSevenLeft shift) = [1, 1, 0]) ∧
    (min 2 2 + (3 - 1) * min 2 (2 - 1) = 4 ∧
      3 * (2 - 2 + 1) - 1 = 2) ∧
    (twoCosetPlus 6 6 6 4 = (4 : ℝ) / 3 ∧
      twoCosetMinus 6 6 6 4 = (2 : ℝ) / 3) ∧
    (twoCosetPlus 3 3 3 4 = (5 : ℝ) / 3 ∧
      twoCosetMinus 3 3 3 4 = (1 : ℝ) / 3) ∧
    (twoCosetPlus 3 3 3 1 = (4 : ℝ) / 3 ∧
      twoCosetMinus 3 3 3 1 = (2 : ℝ) / 3) := by
  exact ⟨baseTwoSeven_word_certificate,
    baseFourSeven_word_certificate,
    baseTwoSeven_rank_bound_certificate,
    exact_two_coset_levels⟩

-- Occupied digit theorem.
#check occupiedDigits_card
#check occupied_digit_count

-- Rank and nullity structure.
#check coordinateSum_ker_finrank
#check symbolRank_le_min
#check symbolRank_le_nonzero_bound
#check spectralRank_bound
#check spectralRank_add_spectralNullity
#check forcedNullityBound_eq
#check spectralNullity_forced
#check spectralNullity_positive
#check rank_nullity_ledger
#check forced_kernel

-- Representative choice, conjugate frequencies, and the full kernel.
#check orbit_representative_shift_phase
#check conjugate_orbit_frequency_coefficients
#check actual_prime_kernel_free_iff_frequency_blocks

-- Gram kernel and two-coset branches.
#check frequencyGram_mulVec_eq_zero_iff
#check fourier_block_kernel
#check primitive_fiber_energy_bound
#check twoCoset_branches_sum
#check twoCoset_branches_product
#check twoCoset_branch_characteristic
#check two_coset_branch_formula

-- Rigidity and energy.
#check overlap_zero_support_unique
#check overlap_zero_iff_point_mass
#check two_level_overlap_rigidity
#check two_level_fourier_rigidity
#check offDiagonalSquareEnergy_eq_zero_iff_matrix_one
#check prime_offDiagonalEnergy_eq_zero_iff_le
#check spectral_excess_zero_characterization
#check actual_prime_spectral_excess

-- Exact examples.
#check base_seven_literal_orbit_words
#check base_two_seven_actual_sharpness
#check decimal_thirteen_single_shift_certificate
#check decimal_thirteen_actual_complete_spectrum
#check decimalThirteen_plus_eigenvector
#check decimalThirteen_minus_eigenvector
#check baseTwoSeven_word_certificate
#check baseFourSeven_word_certificate
#check baseTwoSeven_rank_bound_certificate
#check exact_two_coset_levels
#check finite_contrast_certificate

end NField.Papers.SpectralStructure

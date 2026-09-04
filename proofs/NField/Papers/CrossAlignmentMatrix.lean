/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CrossAlignmentScalarRecovery
import NField.Alignment.DecimalSeventeenFourierSpectrum
import NField.Alignment.PrimeCosetFourierSpectrum
import NField.Alignment.SupportedBlockRealSpectrum

/-!
# The Cross-Alignment Matrix

Reader-facing correspondence manifest for the stable manuscript title.  The
reusable modules retain their dependency-driven order; this file only gathers
the exact declarations that support the manuscript's claims.

The checked boundary includes the canonical supported/rough factorization,
the literal synchronized matrix and its clearing-depth independence, Gram
realization and scalar recovery, the prime identity characterization, exact
multiplicative-coset ordering, complete Fourier conjugation, the full decimal
spectra at thirteen and seventeen, and the real rank/kernel/eigenvalue ledger
for supported lifts.  No numerical eigensolver output is used as a proof.
-/

namespace NField.Papers.CrossAlignmentMatrix

open scoped BigOperators
open NField.Alignment
open NField.Alignment.CrossAlignmentMatrix
open NField.Alignment.CrossAlignmentScalarRecovery
open NField.Alignment.DecimalOrbitSpectra
open NField.Alignment.DecimalPrimeMatrixSpectra
open NField.Alignment.DecimalSeventeenFourierSpectrum
open NField.Alignment.PrimeCosetFourierSpectrum
open NField.Alignment.PrimeCosetOrdering
open NField.Alignment.SupportedBlockReindexing
open NField.Alignment.SupportedBlockRealSpectrum
open NField.Alignment.SynchronizedCrossAlignment
open NField.Alignment.SynchronizedPairwiseAlignment
open NField.Alignment.ThreeTier

noncomputable local instance primeOrbitQuotientFintype {b p : ℕ}
    (hp : p.Prime) (hpb : ¬p ∣ b) :
    Fintype (PrimeOrbitQuotient hp hpb) :=
  Fintype.ofFinite _

/-- The denominator has the unique maximal supported/rough factorization used
to construct the canonical matrix. -/
theorem canonical_denominator_factorization {b n : ℕ} (hn : 0 < n) :
    Supported b (supportedPart b n) ∧
      supportedPart b n ∣ n ∧
      roughPart b n * supportedPart b n = n ∧
      Nat.Coprime (roughPart b n) b ∧
      (∀ d : ℕ, Supported b d → d ∣ n → d ≤ supportedPart b n) ∧
      (∀ q s : ℕ, n = q * s → 0 < q → 0 < s → Supported b s →
        Nat.Coprime q b →
          supportedPart b n = s ∧ roughPart b n = q) := by
  exact canonicalSupportedRoughFactorization hn

/-- Every valid common clearing depth produces the same canonical matrix. -/
theorem canonical_matrix_clock_independence
    {b n D E : ℕ} (hn : 0 < n)
    (hD : supportedPart b n ∣ b ^ D)
    (hE : supportedPart b n ∣ b ^ E) :
    canonicalCrossAlignmentMatrix b n D hn =
      canonicalCrossAlignmentMatrix b n E hn := by
  exact canonicalCrossAlignmentMatrix_independent_of_clearing_depth hn hD hE

/-- The canonical divisibility marker is exactly ordinary base termination. -/
theorem canonical_matrix_termination_marker
    {b n : ℕ} (hn : 0 < n) (i : ProperNumerator n) :
    roughPart b n ∣ numeratorValue i ↔
      TerminatesInBase b (numeratorValue i) n := by
  exact canonical_matrix_marker_iff_terminates hn i

/-- The literal canonical matrix is symmetric, positive semidefinite, and has
unit diagonal. -/
theorem canonical_matrix_gram_certificate
    {b n D : ℕ} (hb : 0 < b) (hn : 0 < n) :
    let A := canonicalCrossAlignmentMatrix b n D hn
    A.IsSymm ∧ Matrix.PosSemidef A ∧ ∀ i, A i i = 1 := by
  exact canonicalCrossAlignmentMatrix_gram_realization hb hn

/-- A fully supported denominator gives the all-ones matrix exactly. -/
theorem supported_denominator_all_ones
    {b n D : ℕ} (hn : 0 < n) (hsupported : Supported b n) :
    canonicalCrossAlignmentMatrix b n D hn = fun _ _ => 1 := by
  exact canonicalCrossAlignmentMatrix_eq_allOnes_of_supported hn hsupported

/-- The denominator-two field contains no distinct unordered pair. -/
theorem denominator_two_pair_space_empty :
    (numeratorPairs 2 1).card = 0 := by
  rw [numeratorPairs_card]
  norm_num

/-- For a symmetric matrix, the all-ones quadratic form minus the trace is
twice the strict-upper-triangle mass. -/
theorem pairwise_matrix_recovery
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (A : Matrix ι ι ℝ) (hsym : A.IsSymm) :
    dotProduct (fun _ : ι => (1 : ℝ))
        (Matrix.mulVec A (fun _ : ι => (1 : ℝ))) - Matrix.trace A =
      2 * ∑ z ∈ (Finset.univ : Finset ι).offDiag with z.1 < z.2,
        A z.1 z.2 := by
  rw [allOnes_quadratic_eq_total,
    total_sub_trace_eq_offDiagonal,
    ordered_offDiagonal_sum_eq_two_mul_upper A hsym]

/-- The marked reference row plus the terminating correction recovers the
literal synchronized reference statistic. -/
theorem reference_alignment_from_marked_row
    {b q s D L : ℕ} (hq : 1 < q) (hs : 0 < s)
    (hn : 2 ≤ q * s) (hL : 0 < L) :
    let A := synchronizedCrossAlignmentMatrix b (q * s) q D L
    let ref := referenceNumerator (q * s) hn
    clearedAlignmentReal b q s D L =
      ((∑ j, A ref j) + (s - 1)) / (q * s - 1) := by
  exact reference_alignment_recovery hq hs hn hL

/-- Focused alignment remains the signed residual between reference and
pairwise alignment. -/
theorem focused_alignment_signed_identity (alpha sigma : ℝ) :
    alpha = (alpha - sigma) + sigma := by
  ring

/-- For a prime denominator, the matrix is the identity exactly at the sharp
digit-partitioning boundary. -/
theorem prime_identity_characterization
    {b p length : ℕ} (hb : 0 < b) (hp : Nat.Prime p)
    (hpb : ¬p ∣ b) (hlength : 0 < length) :
    primeCrossAlignmentMatrix b p length = 1 ↔
      DigitPartitioning b p ∧ p ≤ b + 1 := by
  rw [primeCrossAlignmentMatrix_eq_one_iff_digitPartitioning
    hp hpb hlength]
  exact ⟨fun h => ⟨h, (digitPartitioning_iff hb hp hpb).mp h⟩,
    fun h => h.1⟩

/-- Multiplicative-coset coordinates enumerate every nonzero prime residue
exactly once. -/
theorem prime_coset_ordering_is_bijective
    {b p : ℕ} (hp : p.Prime) (hpb : ¬p ∣ b) :
    Function.Bijective (primeCosetOrdering hp hpb) := by
  exact ⟨primeCosetOrdering_injective hp hpb,
    primeCosetOrdering_surjective hp hpb⟩

/-- In exact coset order, the literal prime matrix is the stated matrix of
circulant blocks. -/
theorem prime_matrix_block_circulant
    {b p : ℕ} (hb : 0 < b) (hp : p.Prime) (hpb : ¬p ∣ b) :
    Matrix.reindex (primeCosetResidueEquiv hp hpb).symm
        (primeCosetResidueEquiv hp hpb).symm
        (primeCrossAlignmentMatrixComplex b p
          (primeBasePeriod b p hp hpb)) =
      primeCosetBlockCirculantMatrix hb hp hpb := by
  exact primeCrossAlignmentMatrixComplex_reindex_eq_blockCirculant
    hb hp hpb

/-- Every small frequency matrix is exactly the Fourier-coefficient Gram
matrix displayed in the manuscript. -/
theorem prime_fourier_symbol_is_gram
    {b p : ℕ} (hb : 0 < b) (hp : p.Prime) (hpb : ¬p ∣ b)
    (j : ZMod (primeBasePeriod b p hp hpb)) :
    primeCosetFourierSymbol hb hp hpb j =
      fun C D => ((primeBasePeriod b p hp hpb : ℕ) : ℂ)⁻¹ *
        ∑ d : Fin b,
          starRingEnd ℂ (primeCosetFourierCoefficient hb hp hpb C d j) *
            primeCosetFourierCoefficient hb hp hpb D d j := by
  exact primeCosetFourierSymbol_eq_frequencyGram hb hp hpb j

/-- Fourier synthesis is bijective and conjugates the full prime matrix into
the complete direct sum of the small frequency actions. -/
theorem prime_fourier_direct_sum
    {b p : ℕ} (hb : 0 < b) (hp : p.Prime) (hpb : ¬p ∣ b) :
    Function.Bijective (primeCosetFourierSynthesis hp hpb) ∧
    ∀ c : ZMod (primeBasePeriod b p hp hpb) →
        PrimeOrbitQuotient hp hpb → ℂ,
      primeCosetBlockAction hb hp hpb
          (primeCosetFourierSynthesis hp hpb c) =
        primeCosetFourierSynthesis hp hpb
          (fun j => Matrix.mulVec
            (primeCosetFourierSymbol hb hp hpb j) (c j)) := by
  exact primeCosetFourier_directSum_complete hb hp hpb

/-- In the displayed residue order, the decimal prime-thirteen matrix is the
exact two-word block matrix used by the spectral proof. -/
theorem decimal_thirteen_literal_matrix :
    Matrix.reindex decimalThirteenResidueEquiv.symm
        decimalThirteenResidueEquiv.symm
        (primeCrossAlignmentMatrix 10 13 6) =
      decimalThirteenMatrix := by
  exact decimalThirteen_primeMatrix_reindex

/-- The two six-dimensional prime-thirteen eigenspaces span the full matrix
space, are disjoint, and carry the two claimed eigenvalues. -/
theorem decimal_thirteen_complete_spectrum :
    (∀ x : Fin 6 → ℚ,
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
        x = 0 ∧ y = 0) := by
  exact decimalThirteenSpectrum_complete

/-- In primitive-orbit order, the literal decimal prime-seventeen matrix is
the exact cyclic word matrix. -/
theorem decimal_seventeen_literal_matrix :
    Matrix.reindex decimalSeventeenResidueEquiv.symm
        decimalSeventeenResidueEquiv.symm
        (primeCrossAlignmentMatrix 10 17 16) =
      orbitMatrix decimalSeventeenWord decimalSeventeenWord := by
  exact decimalSeventeen_primeMatrix_reindex

/-- The exact autocorrelation transform at seventeen takes precisely nine
values and attains the claimed endpoints. -/
theorem decimal_seventeen_complete_spectrum :
    (∀ j : ZMod 16,
      ZMod.dft decimalSeventeenCorrelationKernel (-j) =
        (decimalSeventeenHarmonicValue j.val : ℂ)) ∧
    decimalSeventeenDistinctValues.card = 9 ∧
    (∀ j : Fin 16,
      (1 : ℝ) / 4 ≤ decimalSeventeenHarmonicValue j.val ∧
        decimalSeventeenHarmonicValue j.val ≤ (7 : ℝ) / 4) ∧
    decimalSeventeenHarmonicValue 8 = (1 : ℝ) / 4 ∧
      decimalSeventeenHarmonicValue 0 = (7 : ℝ) / 4 := by
  exact ⟨decimalSeventeenKernel_dft_eq_harmonic,
    decimalSeventeenDistinctValues_card,
    decimalSeventeenHarmonicValue_bounds,
    decimalSeventeenHarmonicValue_extrema_attained⟩

/-- A digit-partitioning supported lift of the literal real matrix is exactly
the terminating block plus the `p-1` residue blocks. -/
theorem supported_lift_block_decomposition
    {b p s D L : ℕ} (hp : Nat.Prime p) (hpb : ¬p ∣ b)
    (hdp : DigitPartitioning b p) (hs : 0 < s) (hD : s ∣ b ^ D)
    (hL : 0 < L) :
    Matrix.reindex (supportedBlockEquivProperNumerator hp.pos hs).symm
        (supportedBlockEquivProperNumerator hp.pos hs).symm
        (synchronizedCrossAlignmentMatrix b (p * s) p D L) =
      supportedBlockMatrixReal p s := by
  exact synchronizedCrossAlignmentMatrix_reindex_eq_supportedBlockMatrix
    hp hpb hdp hs hD hL

/-- At supported scale one, the real block model is the identity and has
rank `p-1`. -/
theorem supported_lift_prime_case (p : ℕ) :
    supportedBlockMatrixReal p 1 = 1 ∧
      (supportedBlockMatrixReal p 1).rank = p - 1 := by
  exact ⟨supportedBlockMatrixReal_one p,
    supportedBlockMatrixReal_rank_one p⟩

/-- At every positive supported scale `s ≥ 2`, the real block model has the
claimed rank, zero multiplicity, and complete nonzero block eigendirections. -/
theorem supported_lift_positive_scale_spectrum
    {p s : ℕ} (hp : 1 ≤ p) (hs : 2 ≤ s) :
    (supportedBlockMatrixReal p s).rank = p ∧
    Module.finrank ℝ (supportedBlockMatrixReal p s).mulVecLin.ker =
      p * s - p - 1 ∧
    (∀ c : Fin (p - 1),
      Matrix.mulVec (supportedBlockMatrixReal p s)
          (residueBlockVectorReal p s c) =
        (s : ℝ) • residueBlockVectorReal p s c) ∧
    Matrix.mulVec (supportedBlockMatrixReal p s)
        (terminatingBlockVectorReal p s) =
      ((s - 1 : ℕ) : ℝ) • terminatingBlockVectorReal p s ∧
    (∀ v : SupportedBlockIndex p s → ℝ,
      Matrix.mulVec (supportedBlockMatrixReal p s) v = 0 ↔
        (∑ i : Fin (s - 1), v (Sum.inl i) = 0) ∧
        (∀ c : Fin (p - 1),
          ∑ i : Fin s, v (Sum.inr (c, i)) = 0)) := by
  exact supportedBlockMatrixReal_spectrum_complete hp hs

end NField.Papers.CrossAlignmentMatrix

/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.PacketFigure
/-! # Integer evaluation of the original source metric and detector rows -/

set_option autoImplicit false

namespace NField.ResetForests.ExactCost

open scoped BigOperators Matrix
open NField.Alignment DedekindReciprocity RademacherThreeTerm

def waveNumerator (j a q : ℕ) : ℤ :=
  if j * a % q = 0 then 0 else 2 * (j * a % q : ℕ) - (q : ℤ)

def coefficientNumerator (i j q : ℕ) : ℤ :=
  ∑ a ∈ Finset.range q, waveNumerator i a q * waveNumerator j a q

def detectorNumerator (Q k j : ℕ) : ℤ :=
  ∑ a ∈ BranchTransport.unitAddresses k, waveNumerator j a k * waveNumerator Q a k

def exactDetector (Q k j : ℕ) : ℚ :=
  (detectorNumerator Q k j : ℚ) / (2 * (k : ℚ) ^ 2)

theorem sawtooth_integer {q : ℕ} (hq : 0 < q) (j a : ℕ) :
    rationalSawtooth (j * a) q = (waveNumerator j a q : ℚ) / (2 * (q : ℚ)) := by
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  unfold rationalSawtooth waveNumerator
  split_ifs
  · norm_num
  · simp only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
    field_simp [hq']

theorem coefficient_integer {q : ℕ} (hq : 0 < q) (i j : ℕ) :
    arithmeticCoefficientDedekindTerm i j q =
      (coefficientNumerator i j q : ℚ) / (4 * (q : ℚ) ^ 2) := by
  unfold arithmeticCoefficientDedekindTerm coefficientNumerator
  simp_rw [sawtooth_integer hq]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem exact_detector_eq {Q k : ℕ} (hk : 0 < k) (j : ℕ) :
    exactDetector Q k j = SeedRecord.rationalDetector Q k j := by
  unfold exactDetector detectorNumerator SeedRecord.rationalDetector
  simp_rw [sawtooth_integer hk]
  push_cast
  rw [Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem detector_row_exact {N Q k : ℕ} (hk : 0 < k) (j : Fin N) :
    PacketQueries.detectorRow N Q k j = (exactDetector Q k (j.val + 1) : ℝ) := by
  rw [exact_detector_eq hk, SeedRecord.detector_row_rational hk]

/-- Reciprocity evaluates a grid entry using only the two short moduli.
Every common factor and the original midpoint convention are retained. -/
def exactGramEntry (Q i j : ℕ) : ℚ :=
  (Q : ℚ) * (i.gcd j : ℚ)^2 / (3 * i * j) - ((i.gcd j).gcd Q : ℚ) -
    (coefficientNumerator Q j i : ℚ) / (i : ℚ)^2 -
    (coefficientNumerator Q i j : ℚ) / (j : ℚ)^2 +
    ((i : ℚ) * (j.gcd Q : ℚ)^2 / j + (j : ℚ) * (i.gcd Q : ℚ)^2 / i) / (3 * Q)

theorem exact_gram_entry {Q i j : ℕ} (hQ : 0 < Q) (hi : 0 < i) (hj : 0 < j) :
    (exactGramEntry Q i j : ℝ) =
      4 * (arithmeticCoefficientDedekindTerm i j Q : ℝ) := by
  have h := CommonResetWeightedSampling.pair_sampling_identity hi hj hQ
  rw [coefficient_integer hi, coefficient_integer hj] at h
  push_cast at h
  unfold exactGramEntry
  push_cast
  have hi' : (i : ℝ) ≠ 0 := by exact_mod_cast hi.ne'
  have hj' : (j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
  have hQ' : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  field_simp [hi', hj', hQ'] at h ⊢
  nlinarith

def exactGram (N Q : ℕ) : Matrix (Fin N) (Fin N) ℚ :=
  fun i j => exactGramEntry Q (i.val + 1) (j.val + 1)

theorem sampled_gram_exact {Q : ℕ} (hQ : 0 < Q) (N : ℕ) :
    SourceMetrics.sampledGram N Q = (exactGram N Q).map (Rat.castHom ℝ) := by
  ext i j
  rw [QuadraticResponse.sampled_gram_coefficient hQ]
  exact (exact_gram_entry hQ (by omega) (by omega)).symm

end NField.ResetForests.ExactCost

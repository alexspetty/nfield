/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PhaseFilteredRamanujanClosure

/-!
# Phase-Filtered Ramanujan Sums and the Spectral Gate

## Coverage

The finite Ramanujan kernel gives the spectral-line collision formula and the
phase gate, including its bounds, zero criterion and identity value. The digit
populations, Euclidean excess words and four printed decimal
continued-fraction values are formalized.

## Scope and assumptions

The phase gate has a positive denominator for a nonempty digit partition; the
intrinsic prime digit word has assigned mass `p - 1`. Its collision formula
retains normalization `1 / p^2`. The classical Ramanujan Dirichlet-series
identity is cited background and is not used in the finite collision proof.
Continued fractions use the standard finite Euclidean convention; the four
printed decimal values are checked exactly.
-/

namespace NField.Papers.PhaseFilteredRamanujan

open scoped BigOperators
open ZMod
open NField.Alignment
open NField.Alignment.SpectralPower
open NField.Alignment.AutocorrelationFormula
open NField.Alignment.PhaseFilteredRamanujan
open NField.Alignment.PhaseFilteredRamanujanClosure

/-- The manuscript's cross-spectrum is exactly the transform of its same-bin
kernel. -/
theorem same_bin_cross_spectrum {N κ : ℕ} [NeZero N]
    (word : ZMod N → Option (Fin κ)) (k k' : ZMod N) :
    crossSpectrum word k k' =
      ∑ x : ZMod N, ∑ y : ZMod N,
        sameBinKernel word x y *
          stdAddChar (-(x * k) - y * k') :=
  crossSpectrum_eq_kernel_transform word k k'

/-- The two Ramanujan selector values. -/
theorem ramanujan_two_values {p : ℕ} [NeZero p] (m : ZMod p) :
    primeRamanujan p m =
      if m = 0 then ((p - 1 : ℕ) : ℂ) else (-1 : ℂ) :=
  primeRamanujan_eq m

/-- Exact Ramanujan-weighted collision identity for the intrinsic prime word. -/
theorem intrinsic_ramanujan_collision {b p : ℕ}
    (hb : 0 < b) (hp : Nat.Prime p) [NeZero p] (a : ZMod p) :
    (collisionCount (primeDigitWord b p hb hp.pos) a : ℂ) =
      ((p : ℂ)⁻¹) ^ 2 * ∑ k : ZMod p, ∑ k' : ZMod p,
        crossSpectrum (primeDigitWord b p hb hp.pos) k k' *
          primeRamanujan p (k + a * k') := by
  rw [← multiplicativeCollision_eq_collisionCount]
  exact ramanujan_collision_identity _ a
    (primeDigitWord_zero b p hb hp.pos)

/-- The Ramanujan double sum and the spectral line are exactly equal. -/
theorem ramanujan_spectral_slice {b p : ℕ}
    (hb : 0 < b) (hp : Nat.Prime p) [NeZero p]
    (a aInv : ZMod p) (hinv : a * aInv = 1) :
    ((p : ℂ)⁻¹) ^ 2 * ∑ k : ZMod p, ∑ k' : ZMod p,
        crossSpectrum (primeDigitWord b p hb hp.pos) k k' *
          primeRamanujan p (k + a * k') =
      (p : ℂ)⁻¹ * ∑ k : ZMod p,
        crossSpectrum (primeDigitWord b p hb hp.pos) k (-aInv * k) :=
  ramanujan_identity_eq_line_slice _ a aInv
    (primeDigitWord_zero b p hb hp.pos) hinv

/-- Complete prime phase-gate bounds, zero criterion, identity value, and
positive discrete gap. -/
theorem spectral_gate_certificate {b p : ℕ}
    (hb : 0 < b) (hp : Nat.Prime p) [NeZero p]
    (a aInv : ZMod p) (hinv : a * aInv = 1) :
    (collisionCount (primeDigitWord b p hb hp.pos) a : ℝ) /
          ((p - 1 : ℕ) : ℝ) ≤
        phaseGate (primeDigitWord b p hb hp.pos) aInv ∧
      phaseGate (primeDigitWord b p hb hp.pos) aInv ≤ 1 ∧
      (phaseGate (primeDigitWord b p hb hp.pos) aInv = 0 ↔
        collisionCount (primeDigitWord b p hb hp.pos) a = 0) ∧
      phaseGate (primeDigitWord b p hb hp.pos) 1 = 1 ∧
      (0 < collisionCount (primeDigitWord b p hb hp.pos) a →
        ((p - 1 : ℕ) : ℝ)⁻¹ ≤
          phaseGate (primeDigitWord b p hb hp.pos) aInv) :=
  prime_phaseGate_certificate hb hp a aInv hinv

/-- The unsigned phase mass is a genuine positive denominator. -/
theorem phase_gate_denominator_positive {b p : ℕ}
    (hb : 0 < b) (hp : Nat.Prime p) [NeZero p]
    (aInv : ZMod p) :
    0 < phaseMass (primeDigitWord b p hb hp.pos) aInv := by
  apply phaseMass_pos_of_assigned
  rw [prime_assignedMass hb hp.pos]
  exact Nat.sub_pos_of_lt hp.one_lt

/-- The identity multiplier fixes every assigned nonzero residue. -/
theorem identity_collision {b p : ℕ}
    (hb : 0 < b) (hp : Nat.Prime p) [NeZero p] :
    collisionCount (primeDigitWord b p hb hp.pos) 1 = p - 1 := by
  rw [collisionCount_one, prime_assignedMass hb hp.pos]

/-- Canonical primitive-root repetend autocorrelation, with both exact
Ramanujan and spectral-line forms. -/
local instance paperPrimeBasePeriodNeZero {b p : ℕ}
    (hp : Nat.Prime p) (hpb : ¬p ∣ b) :
    NeZero (primeBasePeriod b p hp hpb) :=
  ⟨(primeBasePeriod_pos hp hpb).ne'⟩

theorem canonical_repetend_specialization
    {b p : ℕ} (hb : 0 < b) (hp : Nat.Prime p) (hpb : ¬p ∣ b)
    [NeZero p]
    (hprimitive : IsPrimitiveRoot (primeBaseUnit b p hp hpb) (p - 1))
    (lag : ZMod (primeBasePeriod b p hp hpb)) :
    let hfull :=
      primeBasePeriod_eq_full_of_isPrimitiveRoot hp hpb hprimitive
    let a : (ZMod p)ˣ := (primeBaseUnit b p hp hpb) ^ lag.val
    fullOrbitAutocorrelation (primeDigitWord b p hb hp.pos)
        (canonicalPrimeOrbitEquiv hp hpb hfull) lag =
      ((p : ℂ)⁻¹) ^ 2 * ∑ k : ZMod p, ∑ k' : ZMod p,
        crossSpectrum (primeDigitWord b p hb hp.pos) k k' *
          primeRamanujan p (k + (a : ZMod p) * k') ∧
    fullOrbitAutocorrelation (primeDigitWord b p hb hp.pos)
        (canonicalPrimeOrbitEquiv hp hpb hfull) lag =
      (p : ℂ)⁻¹ * ∑ k : ZMod p,
        crossSpectrum (primeDigitWord b p hb hp.pos) k
          (-((a⁻¹ : (ZMod p)ˣ) : ZMod p) * k) :=
  canonical_primitiveRoot_ramanujan_autocorrelation hb hp hpb hprimitive lag

/-- The spectral zero condition is exactly the finite bin-disjointness
condition. -/
theorem collision_free_multiplier {b p : ℕ}
    (hb : 0 < b) (hp : Nat.Prime p) [NeZero p]
    (a aInv : ZMod p) (hinv : a * aInv = 1) :
    phaseGate (primeDigitWord b p hb hp.pos) aInv = 0 ↔
      ∀ d : Fin b, ∀ r ∈ binSet (primeDigitWord b p hb hp.pos) d,
        a * r ∉ binSet (primeDigitWord b p hb hp.pos) d := by
  have hmass : 0 < assignedMass (primeDigitWord b p hb hp.pos) := by
    rw [prime_assignedMass hb hp.pos]
    exact Nat.sub_pos_of_lt hp.one_lt
  rw [phaseGate_eq_zero_iff _ a aInv hinv hmass]
  exact collisionCount_eq_zero_iff_bins_disjoint _ a

/-- Exact singleton-bin multiplier profile. -/
theorem singleton_bin_collision_profile {b p : ℕ}
    (hb : 0 < b) (hp : Nat.Prime p) [NeZero p]
    (hdp : DigitPartitioning b p) (a : ZMod p) :
    collisionCount (primeDigitWord b p hb hp.pos) a =
      if a = 1 then p - 1 else 0 :=
  prime_singleton_collision_profile hb hp hdp a

/-- Exact singleton-bin cross-spectrum. -/
theorem singleton_bin_cross_spectrum {b p : ℕ}
    (hb : 0 < b) (hp : Nat.Prime p) [NeZero p]
    (hdp : DigitPartitioning b p) (k k' : ZMod p) :
    crossSpectrum (primeDigitWord b p hb hp.pos) k k' =
      primeRamanujan p (k + k') :=
  prime_singleton_crossSpectrum hb hp hdp k k'

/-- The intrinsic Euclidean bin word, including binary entries and the exact
number of excess bins. -/
theorem exact_euclidean_bin_word
    {b p q r : ℕ} (hb : 0 < b) (hp : Nat.Prime p)
    (hr : 0 < r) (hrb : r < b) (hdivision : p = b * q + r)
    (d : Fin b) :
    digitBinPopulation b p d.val = q + excessBinWord b r d.val ∧
      (excessBinWord b r d.val = 0 ∨
        excessBinWord b r d.val = 1) ∧
      (excessOneBins b r).card = r - 1 := by
  exact ⟨digitBinPopulation_eq_quotient_add_excess
      hb hp.pos hr hrb hdivision d,
    excessBinWord_eq_zero_or_one hb hr hrb d.isLt,
    excessOneBins_card hb hr hrb⟩

/-- The coarse excess word determines the Euclidean remainder. -/
theorem excess_word_determines_remainder
    {b r s : ℕ} (hb : 0 < b)
    (hr : 0 < r) (hrb : r < b) (hs : 0 < s) (hsb : s < b)
    (hword : ∀ d, d < b → excessBinWord b r d = excessBinWord b s d) :
    r = s :=
  excessBinWord_injective_in_remainder hb hr hrb hs hsb hword

/-- Coarse zero-frequency mass from an exact Euclidean two-length word. -/
theorem zero_frequency_coarse_mass
    {b q r : ℕ} (n : Fin b → ℕ)
    (hlength : ∀ d, n d = q ∨ n d = q + 1)
    (hlarge :
      (Finset.univ.filter fun d : Fin b => n d = q + 1).card = r - 1) :
    ∑ d : Fin b, n d ^ 2 = b * q ^ 2 + (2 * q + 1) * (r - 1) :=
  euclidean_bin_square_mass n hlength hlarge

/-- Exact rational source of the continued-fraction tail. -/
theorem continued_fraction_tail_source {p b q r : ℕ}
    (hb : 0 < b) (hr : 0 < r) (hdivision : p = b * q + r) :
    (p : ℚ) / b = q + 1 / ((b : ℚ) / r) :=
  euclidean_tail_identity hb hr hdivision

/-- The four exact decimal excess words and continued-fraction tail values. -/
theorem decimal_coarse_table :
    ((List.range 10).map (excessBinWord 10 1) =
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0] ∧
      (List.range 10).map (excessBinWord 10 3) =
        [0, 0, 0, 1, 0, 0, 1, 0, 0, 0] ∧
      (List.range 10).map (excessBinWord 10 7) =
        [0, 1, 1, 0, 1, 1, 0, 1, 1, 0] ∧
      (List.range 10).map (excessBinWord 10 9) =
        [0, 1, 1, 1, 1, 1, 1, 1, 1, 0]) ∧
    ((10 : ℚ) / 1 = 10 ∧
      (10 : ℚ) / 3 = 3 + 1 / 3 ∧
      (10 : ℚ) / 7 = 1 + 1 / (2 + 1 / 3) ∧
      (10 : ℚ) / 9 = 1 + 1 / 9) :=
  ⟨decimal_excess_bin_words, decimal_continued_fraction_tail_values⟩

/-- Exact intrinsic zero-frequency mass. -/
theorem zero_frequency_mass
    {b p q r : ℕ} (hb : 0 < b) (hp : Nat.Prime p)
    (hr : 0 < r) (hrb : r < b) (hdivision : p = b * q + r)
    [NeZero p] :
    crossSpectrum (primeDigitWord b p hb hp.pos) 0 0 =
      (b * q ^ 2 + (2 * q + 1) * (r - 1) : ℕ) :=
  prime_crossSpectrum_zero_euclidean hb hp hr hrb hdivision

#check primeRamanujan_eq
#check ramanujan_collision_identity
#check ramanujan_identity_eq_line_slice
#check multiplicativeCollision_eq_collisionCount
#check sliceSum_eq_collisionCount
#check norm_sliceSum_le_phaseMass
#check total_binFourier_norm_sq
#check total_binFourier_norm_sq_line
#check phaseMass_le_total
#check phaseMass_pos_of_assigned
#check phaseGate_bounds
#check phaseGate_eq_zero_iff
#check phaseGate_ge_reciprocal_of_collision
#check phaseGate_one
#check collisionCount_eq_zero_iff_bins_disjoint
#check prime_phaseGate_certificate
#check prime_singleton_collision_profile
#check euclidean_bin_square_mass
#check euclidean_tail_identity
#check canonical_primitiveRoot_ramanujan_autocorrelation
#check prime_singleton_crossSpectrum
#check digitBinPopulation_eq_quotient_add_excess
#check excessBinWord_eq_zero_or_one
#check excessOneBins_card
#check excessBinWord_injective_in_remainder
#check prime_crossSpectrum_zero_euclidean
#check decimal_excess_bin_words
#check decimal_continued_fraction_tail_values

end NField.Papers.PhaseFilteredRamanujan

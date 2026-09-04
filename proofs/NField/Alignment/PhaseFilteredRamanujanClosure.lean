/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PhaseFilteredRamanujan
import NField.Alignment.AutocorrelationClosure
import NField.Alignment.FloorDigitBinDistribution
import NField.Alignment.FiniteCarrierArithmeticCollapse

/-!
# Exact Euclidean and orbit closure for the phase gate

This module joins the reusable phase-gate construction to the intrinsic
floor-digit populations, the canonical primitive-root orbit, and the exact
decimal coarse-data fixtures.  It contains no prime-sum or asymptotic input.
-/

namespace NField.Alignment.PhaseFilteredRamanujanClosure

open scoped BigOperators
open ZMod
open NField.Alignment
open NField.Alignment.SpectralPower
open NField.Alignment.AutocorrelationFormula
open NField.Alignment.PhaseFilteredRamanujan
open NField.Alignment.FiniteCarrierArithmeticCollapse
open NField.Alignment.FinitePrefixCarryReduction

/-- The manuscript's excess-bin word, with the exceptional zero digit placed
at zero and ceiling increments on every positive digit. -/
def excessBinWord (b r d : ℕ) : ℕ :=
  if d = 0 then 0 else
    ((d + 1) * r) ⌈/⌉ b - (d * r) ⌈/⌉ b

@[simp] theorem excessBinWord_zero (b r : ℕ) :
    excessBinWord b r 0 = 0 := by
  simp [excessBinWord]

/-- Subtracting one from a Euclidean decomposition moves its positive
remainder from `r` to `r-1`. -/
theorem predecessor_quotient_remainder
    {p b q r : ℕ} (hr : 0 < r) (hrb : r < b)
    (hdivision : p = b * q + r) :
    (p - 1) / b = q ∧ (p - 1) % b = r - 1 := by
  have hpminus : p - 1 = b * q + (r - 1) := by
    calc
      p - 1 = (b * q + r) - 1 := by rw [hdivision]
      _ = b * q + (r - 1) :=
        Nat.add_sub_assoc (by omega : 1 ≤ r) (b * q)
  constructor
  · apply Nat.div_eq_of_lt_le
    · rw [hpminus]
      calc
        q * b = b * q := Nat.mul_comm _ _
        _ ≤ b * q + (r - 1) := Nat.le_add_right _ _
    · rw [hpminus]
      calc
        b * q + (r - 1) < b * q + b := Nat.add_lt_add_left (by omega) _
        _ = (q + 1) * b := by ring
  · rw [hpminus, Nat.mul_add_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)

/-- Every intrinsic digit population is the Euclidean quotient plus the
corresponding entry of the exact excess-bin word. -/
theorem digitBinPopulation_eq_quotient_add_excess
    {p b q r : ℕ} (hb : 0 < b) (hp : 0 < p)
    (hr : 0 < r) (hrb : r < b) (hdivision : p = b * q + r)
    (d : Fin b) :
    digitBinPopulation b p d.val = q + excessBinWord b r d.val := by
  have hqr := predecessor_quotient_remainder hr hrb hdivision
  by_cases hd0 : d.val = 0
  · rw [hd0]
    simpa [hqr.1] using digitBinPopulation_zero hb hp
  · have hdpos : 0 < d.val := Nat.pos_of_ne_zero hd0
    have hboundaryPos : 1 ≤ digitBinBoundary b p d.val := by
      have hreach :
          d.val * p ≤ b * digitBinBoundary b p d.val :=
        le_smul_ceilDiv hb
      by_contra hnot
      have hzero : digitBinBoundary b p d.val = 0 := by omega
      have hdp : 0 < d.val * p := Nat.mul_pos hdpos hp
      rw [hzero] at hreach
      simp only [Nat.mul_zero] at hreach
      exact (Nat.not_le_of_gt hdp) hreach
    have hlower :
        digitBinBoundary b p d.val =
          d.val * q + (d.val * r) ⌈/⌉ b := by
      unfold digitBinBoundary
      rw [hdivision]
      have heq : d.val * (b * q + r) =
          b * (d.val * q) + d.val * r := by ring
      rw [heq, ceilDiv_add_multiple hb]
    have hupper :
        digitBinBoundary b p (d.val + 1) =
          (d.val + 1) * q + ((d.val + 1) * r) ⌈/⌉ b := by
      unfold digitBinBoundary
      rw [hdivision]
      have heq : (d.val + 1) * (b * q + r) =
          b * ((d.val + 1) * q) + (d.val + 1) * r := by ring
      rw [heq, ceilDiv_add_multiple hb]
    have hmono :
        (d.val * r) ⌈/⌉ b ≤ ((d.val + 1) * r) ⌈/⌉ b :=
      ceilDiv_mono hb (Nat.mul_le_mul_right r (Nat.le_succ d.val))
    rw [digitBinPopulation_eq_boundary_sub hb hp d.isLt]
    rw [max_eq_right hboundaryPos, hlower, hupper]
    simp only [excessBinWord, if_neg hd0]
    rw [show (d.val + 1) * q = d.val * q + q by ring]
    rw [Nat.add_assoc, Nat.add_sub_add_left]
    exact Nat.add_sub_assoc hmono q

/-- Every excess entry is binary. -/
theorem excessBinWord_eq_zero_or_one
    {b r d : ℕ} (hb : 0 < b) (hr : 0 < r) (hrb : r < b)
    (hdb : d < b) :
    excessBinWord b r d = 0 ∨ excessBinWord b r d = 1 := by
  let p := b + r
  let df : Fin b := ⟨d, hdb⟩
  have hp : 0 < p := by dsimp [p]; omega
  have hdivision : p = b * 1 + r := by dsimp [p]; omega
  have hpop := digitBinPopulation_eq_quotient_add_excess
    hb hp hr hrb hdivision df
  have htwo := digitBinPopulation_eq_quotient_or_succ hb hp hdb
  have hquot :=
    (predecessor_quotient_remainder hr hrb hdivision).1
  rw [hquot] at htwo
  dsimp only [df] at hpop
  rcases htwo with hzero | hone
  · left
    omega
  · right
    omega

/-- Positive positions of the binary excess word. -/
def excessOneBins (b r : ℕ) : Finset ℕ :=
  (Finset.range b).filter (fun d => excessBinWord b r d = 1)

/-- Exactly `r-1` digit bins carry the Euclidean excess. -/
theorem excessOneBins_card
    {b r : ℕ} (hb : 0 < b) (hr : 0 < r) (hrb : r < b) :
    (excessOneBins b r).card = r - 1 := by
  let p := b + r
  have hp : 0 < p := by dsimp [p]; omega
  have hdivision : p = b * 1 + r := by dsimp [p]; omega
  have hqr := predecessor_quotient_remainder hr hrb hdivision
  have hsets : excessOneBins b r = enlargedDigitBins b p := by
    ext d
    simp only [excessOneBins, enlargedDigitBins, Finset.mem_filter,
      Finset.mem_range]
    constructor
    · rintro ⟨hdb, hword⟩
      let df : Fin b := ⟨d, hdb⟩
      have hpop := digitBinPopulation_eq_quotient_add_excess
        hb hp hr hrb hdivision df
      dsimp only [df] at hpop
      rw [hword] at hpop
      refine ⟨hdb, ?_⟩
      rw [hqr.1]
      omega
    · rintro ⟨hdb, hpopLarge⟩
      let df : Fin b := ⟨d, hdb⟩
      have hpop := digitBinPopulation_eq_quotient_add_excess
        hb hp hr hrb hdivision df
      dsimp only [df] at hpop
      rw [hqr.1] at hpopLarge
      have hbinary := excessBinWord_eq_zero_or_one hb hr hrb hdb
      exact ⟨hdb, by omega⟩
  rw [hsets, enlargedDigitBins_card hb hp, hqr.2]

/-- The excess-bin word determines its positive Euclidean remainder. -/
theorem excessBinWord_injective_in_remainder
    {b r s : ℕ} (hb : 0 < b)
    (hr : 0 < r) (hrb : r < b) (hs : 0 < s) (hsb : s < b)
    (hword : ∀ d, d < b → excessBinWord b r d = excessBinWord b s d) :
    r = s := by
  have hsets : excessOneBins b r = excessOneBins b s := by
    ext d
    simp only [excessOneBins, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hdb, hd⟩
      exact ⟨hdb, by rw [← hword d hdb]; exact hd⟩
    · rintro ⟨hdb, hd⟩
      exact ⟨hdb, by rw [hword d hdb]; exact hd⟩
  have hcard := congrArg Finset.card hsets
  rw [excessOneBins_card hb hr hrb,
    excessOneBins_card hb hs hsb] at hcard
  omega

/-- The intrinsic zero-frequency cross-spectrum is the exact Euclidean
square-mass polynomial. -/
theorem prime_crossSpectrum_zero_euclidean
    {b p q r : ℕ} (hb : 0 < b) (hp : Nat.Prime p)
    (hr : 0 < r) (hrb : r < b) (hdivision : p = b * q + r)
    [NeZero p] :
    crossSpectrum (primeDigitWord b p hb hp.pos) 0 0 =
      (b * q ^ 2 + (2 * q + 1) * (r - 1) : ℕ) := by
  have hqr := predecessor_quotient_remainder hr hrb hdivision
  calc
    crossSpectrum (primeDigitWord b p hb hp.pos) 0 0 =
        spectralPower (primeDigitWord b p hb hp.pos) 0 := by
      simpa using
        (crossSpectrum_antidiagonal
          (primeDigitWord b p hb hp.pos) (0 : ZMod p))
    _ = (digitBinSquareSum b p : ℂ) :=
      prime_spectralPower_zero hb hp.pos
    _ = (b * q ^ 2 + (2 * q + 1) * (r - 1) : ℕ) := by
      rw [digitBinSquareSum_eq_quotient_remainder hb hp.pos,
        hqr.1, hqr.2]
      push_cast
      ring

/-- The four decimal excess-bin words in the manuscript table. -/
theorem decimal_excess_bin_words :
    (List.range 10).map (excessBinWord 10 1) =
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0] ∧
      (List.range 10).map (excessBinWord 10 3) =
        [0, 0, 0, 1, 0, 0, 1, 0, 0, 0] ∧
      (List.range 10).map (excessBinWord 10 7) =
        [0, 1, 1, 0, 1, 1, 0, 1, 1, 0] ∧
      (List.range 10).map (excessBinWord 10 9) =
        [0, 1, 1, 1, 1, 1, 1, 1, 1, 0] := by
  decide

/-- The four exact decimal continued-fraction tail values. -/
theorem decimal_continued_fraction_tail_values :
    (10 : ℚ) / 1 = 10 ∧
      (10 : ℚ) / 3 = 3 + 1 / 3 ∧
      (10 : ℚ) / 7 = 1 + 1 / (2 + 1 / 3) ∧
      (10 : ℚ) / 9 = 1 + 1 / 9 := by
  norm_num

local instance primeBasePeriodNeZero {b p : ℕ}
    (hp : Nat.Prime p) (hpb : ¬p ∣ b) :
    NeZero (primeBasePeriod b p hp hpb) :=
  ⟨(primeBasePeriod_pos hp hpb).ne'⟩

/-- A primitive-root power orbit has both the Ramanujan double-sum and the
spectral-line autocorrelation readouts. -/
theorem canonical_primitiveRoot_ramanujan_autocorrelation
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
          (-((a⁻¹ : (ZMod p)ˣ) : ZMod p) * k) := by
  dsimp only
  let hfull := primeBasePeriod_eq_full_of_isPrimitiveRoot hp hpb hprimitive
  let a : (ZMod p)ˣ := (primeBaseUnit b p hp hpb) ^ lag.val
  constructor
  · calc
      fullOrbitAutocorrelation (primeDigitWord b p hb hp.pos)
          (canonicalPrimeOrbitEquiv hp hpb hfull) lag =
        multiplicativeCollision (primeDigitWord b p hb hp.pos)
          (a : ZMod p) := by
            apply fullOrbitAutocorrelation_eq_collision
              (primeDigitWord b p hb hp.pos)
              (canonicalPrimeOrbitEquiv hp hpb hfull) lag
              (a : ZMod p) (primeDigitWord_zero b p hb hp.pos)
            intro t
            exact canonicalPrimeOrbitEquiv_motion hp hpb hfull t lag
      _ = ((p : ℂ)⁻¹) ^ 2 * ∑ k : ZMod p, ∑ k' : ZMod p,
          crossSpectrum (primeDigitWord b p hb hp.pos) k k' *
            primeRamanujan p (k + (a : ZMod p) * k') :=
        ramanujan_collision_identity _ _
          (primeDigitWord_zero b p hb hp.pos)
  · exact canonical_primitiveRoot_autocorrelation_slice hp hpb hprimitive
      (primeDigitWord b p hb hp.pos)
      (primeDigitWord_zero b p hb hp.pos) lag

/-- Digit partitioning turns the intrinsic same-bin kernel into equality on
the nonzero residues. -/
theorem prime_singleton_sameBinKernel
    {b p : ℕ} (hb : 0 < b) (hp : Nat.Prime p) [NeZero p]
    (hdp : DigitPartitioning b p) (x y : ZMod p) :
    sameBinKernel (primeDigitWord b p hb hp.pos) x y =
      if x = y ∧ x ≠ 0 then 1 else 0 := by
  rw [sameBinKernel_eq_indicator]
  have hiff :
      (primeDigitWord b p hb hp.pos x =
          primeDigitWord b p hb hp.pos y ∧
        primeDigitWord b p hb hp.pos x ≠ none) ↔
      x = y ∧ x ≠ 0 := by
    constructor
    · rintro ⟨hxy, hx⟩
      have heq := primeDigitWord_injective_on_assigned
        hb hp.pos hdp hxy hx
      refine ⟨heq, ?_⟩
      intro hx0
      rw [hx0] at hx
      exact hx (primeDigitWord_zero b p hb hp.pos)
    · rintro ⟨rfl, hx⟩
      exact ⟨rfl, by simp [primeDigitWord, hx]⟩
  simp only [hiff]

/-- For singleton digit bins, the full cross-spectrum is exactly the prime
Ramanujan kernel on the sum of the two frequency coordinates. -/
theorem prime_singleton_crossSpectrum
    {b p : ℕ} (hb : 0 < b) (hp : Nat.Prime p) [NeZero p]
    (hdp : DigitPartitioning b p) (k k' : ZMod p) :
    crossSpectrum (primeDigitWord b p hb hp.pos) k k' =
      primeRamanujan p (k + k') := by
  classical
  rw [crossSpectrum_eq_kernel_transform]
  simp_rw [prime_singleton_sameBinKernel hb hp hdp]
  have hinner (x : ZMod p) :
      (∑ y : ZMod p,
        (if x = y ∧ x ≠ 0 then (1 : ℂ) else 0) *
          stdAddChar (-(x * k) - y * k')) =
        if x ≠ 0 then stdAddChar (-(x * (k + k'))) else 0 := by
    by_cases hx : x = 0
    · simp [hx]
    · have hexp : -(x * k) - x * k' = -(x * (k + k')) := by ring
      simp [hx, hexp]
  simp_rw [hinner]
  calc
    (∑ x : ZMod p,
        if x ≠ 0 then stdAddChar (-(x * (k + k'))) else 0) =
      ∑ x ∈ nonzeroSet p, stdAddChar (-(x * (k + k'))) := by
        rw [← Finset.sum_filter]
        congr 1
        ext x
        simp [nonzeroSet]
    _ = primeRamanujan p (-(k + k')) := by
      unfold primeRamanujan subsetExponential
      apply Finset.sum_congr rfl
      intro x _
      congr 1
      ring
    _ = primeRamanujan p (k + k') := by
      have hramanujan_neg (m : ZMod p) :
          primeRamanujan p (-m) = primeRamanujan p m := by
        rw [primeRamanujan_eq, primeRamanujan_eq]
        simp
      exact hramanujan_neg (k + k')

end NField.Alignment.PhaseFilteredRamanujanClosure

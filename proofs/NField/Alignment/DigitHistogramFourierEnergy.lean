/-
Author: Alexander S. Petty
-/

import Mathlib.Analysis.Fourier.ZMod
import NField.Alignment.FloorDigitBinDistribution

/-!
# Fourier energy of the digit histogram

This module proves finite Parseval directly for the unnormalized additive
Fourier transform on `ZMod`, applies it to the digit-bin population vector,
and identifies minimal histogram energy with singleton occupied bins.
-/

namespace NField.Alignment

open scoped BigOperators
open NField.CollisionDefinition
open ZMod

/-- Finite Parseval for the unnormalized additive Fourier transform. -/
theorem zmodDft_parseval_complex {N : ℕ} [NeZero N] (F : ZMod N → ℂ) :
    ∑ k : ZMod N, star (𝓕 F k) * 𝓕 F k =
      (N : ℂ) * ∑ r : ZMod N, star (F r) * F r := by
  classical
  have hstar (k : ZMod N) :
      star (∑ r : ZMod N, stdAddChar (-(r * k)) * F r) =
        ∑ r : ZMod N, stdAddChar (r * k) * star (F r) := by
    change (starRingEnd ℂ) (∑ r : ZMod N, stdAddChar (-(r * k)) * F r) = _
    rw [map_sum (starRingEnd ℂ)]
    apply Finset.sum_congr rfl
    intro r _
    rw [map_mul]
    have hchar : star (stdAddChar (-(r * k))) = stdAddChar (r * k) := by
      simpa only [starRingEnd_apply, neg_neg] using
        (AddChar.map_neg_eq_conj (stdAddChar (N := N)) (-(r * k))).symm
    simpa only [starRingEnd_apply] using
      congrArg (fun z : ℂ => z * star (F r)) hchar
  have horth (r s : ZMod N) :
      ∑ k : ZMod N, stdAddChar ((r - s) * k) =
        if r = s then (N : ℂ) else 0 := by
    split_ifs with hrs
    · subst s
      simp
    · have hdiff : r - s ≠ 0 := sub_ne_zero.mpr hrs
      exact AddChar.sum_eq_zero_of_ne_one (isPrimitive_stdAddChar N hdiff)
  simp only [ZMod.dft_apply, smul_eq_mul, hstar]
  calc
    (∑ k : ZMod N,
        (∑ r : ZMod N, stdAddChar (r * k) * star (F r)) *
          ∑ s : ZMod N, stdAddChar (-(s * k)) * F s) =
      ∑ k : ZMod N, ∑ r : ZMod N, ∑ s : ZMod N,
        stdAddChar ((r - s) * k) * (star (F r) * F s) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro r _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s _
          calc
            stdAddChar (r * k) * star (F r) *
                (stdAddChar (-(s * k)) * F s) =
              (stdAddChar (r * k) * stdAddChar (-(s * k))) *
                (star (F r) * F s) := by ring
            _ = stdAddChar (r * k + -(s * k)) *
                (star (F r) * F s) := by rw [AddChar.map_add_eq_mul]
            _ = stdAddChar ((r - s) * k) *
                (star (F r) * F s) := by congr 2; ring
    _ = ∑ r : ZMod N, ∑ s : ZMod N,
        (∑ k : ZMod N, stdAddChar ((r - s) * k)) *
          (star (F r) * F s) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro r _
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro s _
            rw [Finset.sum_mul]
    _ = ∑ r : ZMod N, ∑ s : ZMod N,
        (if r = s then (N : ℂ) else 0) * (star (F r) * F s) := by
          simp_rw [horth]
    _ = (N : ℂ) * ∑ r : ZMod N, star (F r) * F r := by
      simp [Finset.mul_sum]

/-- The digit population vector, intrinsically indexed by the base cycle. -/
def digitHistogramSignal (b p : ℕ) [NeZero b] (d : ZMod b) : ℂ :=
  digitBinPopulation b p d.val

/-- Canonical residue representatives identify `ZMod b` with `Fin b`. -/
noncomputable def zmodFinResidueEquiv (b : ℕ) [NeZero b] : ZMod b ≃ Fin b where
  toFun d := ⟨d.val, d.val_lt⟩
  invFun i := (i.val : ZMod b)
  left_inv d := ZMod.natCast_zmod_val d
  right_inv i := Fin.ext (ZMod.val_natCast_of_lt i.isLt)

/-- The manuscript's positive-sign digit-histogram Fourier coefficient. -/
noncomputable def digitHistogramFourier (b p : ℕ) [NeZero b]
    (j : ZMod b) : ℂ :=
  𝓕 (digitHistogramSignal b p) (-j)

/-- Expansion of the intrinsic transform gives the printed exponential sum. -/
theorem digitHistogramFourier_eq_sum {b p : ℕ} [NeZero b]
    (j : ZMod b) :
    digitHistogramFourier b p j =
      ∑ d : ZMod b, (digitBinPopulation b p d.val : ℂ) *
        stdAddChar (d * j) := by
  unfold digitHistogramFourier digitHistogramSignal
  rw [ZMod.dft_apply]
  apply Finset.sum_congr rfl
  intro d _
  simp only [mul_neg, neg_neg, smul_eq_mul]
  ring

/-- Reindexing the intrinsic histogram by `Fin b` recovers the defining
sum of squared digit-bin populations. -/
theorem digitHistogramSignal_square_sum {b p : ℕ} [NeZero b] :
    ∑ d : ZMod b, star (digitHistogramSignal b p d) *
        digitHistogramSignal b p d = (digitBinSquareSum b p : ℂ) := by
  calc
    ∑ d : ZMod b, star (digitHistogramSignal b p d) *
        digitHistogramSignal b p d =
      ∑ i : Fin b, (((digitBinPopulation b p i.val) ^ 2 : ℕ) : ℂ) := by
        rw [← (zmodFinResidueEquiv b).sum_comp]
        apply Finset.sum_congr rfl
        intro d _
        simp [zmodFinResidueEquiv, digitHistogramSignal, pow_two]
    _ = (digitBinSquareSum b p : ℂ) := by
      norm_cast
      simpa [digitBinSquareSum] using
        (Fin.sum_univ_eq_sum_range
          (fun d => digitBinPopulation b p d ^ 2) b)

/-- Exact Fourier-energy identity for the digit histogram. -/
theorem digitHistogram_fourier_energy {b p : ℕ} [NeZero b] :
    ∑ j : ZMod b,
        star (digitHistogramFourier b p j) * digitHistogramFourier b p j =
      (b : ℂ) * (digitBinSquareSum b p : ℂ) := by
  unfold digitHistogramFourier
  rw [show (∑ j : ZMod b,
      star (𝓕 (digitHistogramSignal b p) (-j)) *
        𝓕 (digitHistogramSignal b p) (-j)) =
      ∑ k : ZMod b,
        star (𝓕 (digitHistogramSignal b p) k) *
          𝓕 (digitHistogramSignal b p) k by
    exact Fintype.sum_equiv (Equiv.neg (ZMod b)) _ _ (fun j => rfl)]
  rw [zmodDft_parseval_complex, digitHistogramSignal_square_sum]

/-- The manuscript's normalized Parseval form `S=(1/b) sum |n-hat|^2`. -/
theorem digitBinSquareSum_eq_normalized_fourier_energy {b p : ℕ}
    [NeZero b] (hb : 0 < b) :
    ((digitBinSquareSum b p : ℕ) : ℂ) =
      (1 / (b : ℂ)) * ∑ j : ZMod b,
        star (digitHistogramFourier b p j) * digitHistogramFourier b p j := by
  rw [digitHistogram_fourier_energy]
  have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hb
  field_simp

/-- Squaring a natural number never decreases it. -/
theorem sum_le_sum_sq {α : Type*} (s : Finset α) (f : α → ℕ) :
    ∑ x ∈ s, f x ≤ ∑ x ∈ s, (f x) ^ 2 := by
  apply Finset.sum_le_sum
  intro x _
  nlinarith

/-- Equality of total mass and square mass forces every term to be zero or
one, and conversely. -/
theorem sum_sq_eq_sum_iff_le_one {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℕ) :
    (∑ x ∈ s, (f x) ^ 2 = ∑ x ∈ s, f x) ↔
      ∀ x ∈ s, f x ≤ 1 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      constructor
      · intro hsum
        have htailLe := sum_le_sum_sq s f
        have haLe : f a ≤ (f a) ^ 2 := by nlinarith
        have haEq : (f a) ^ 2 = f a := by omega
        have htailEq : ∑ x ∈ s, (f x) ^ 2 = ∑ x ∈ s, f x := by omega
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hxs
        · nlinarith
        · exact (ih.mp htailEq) x hxs
      · intro hall
        have haone := hall a (by simp)
        have htail : ∀ x ∈ s, f x ≤ 1 := by
          intro x hx
          exact hall x (by simp [hx])
        rw [(ih.mpr htail)]
        nlinarith

/-- Minimal square mass is equivalent to every digit bin containing at most
one nonzero remainder. -/
theorem digitBinSquareSum_eq_mass_iff {b p : ℕ} (hb : 0 < b) (hp : 0 < p) :
    digitBinSquareSum b p = p - 1 ↔
      ∀ d ∈ Finset.range b, digitBinPopulation b p d ≤ 1 := by
  unfold digitBinSquareSum
  rw [← digitBinPopulation_sum hb hp]
  exact sum_sq_eq_sum_iff_le_one (Finset.range b) (digitBinPopulation b p)

/-- Having at most one residue in every bin is exactly injectivity of the
digit function on nonzero residues. -/
theorem digitPartitioning_iff_population_le_one {b p : ℕ} (hb : 0 < b)
    (hp : 0 < p) :
    DigitPartitioning b p ↔
      ∀ d ∈ Finset.range b, digitBinPopulation b p d ≤ 1 := by
  constructor
  · intro hdp d _
    exact digitBinPopulation_le_one_of_digitPartitioning hdp
  · intro hpopulation r s hr0 hrp hs0 hsp hdigit
    have hdlt : digitBin b p r < b := digitBin_lt_base hb hp hrp
    have hrmem : r ∈ (nonzeroResidues p).filter
        (fun x => digitBin b p x = digitBin b p r) := by
      simp [nonzeroResidues, hr0.ne', hrp]
    have hsmem : s ∈ (nonzeroResidues p).filter
        (fun x => digitBin b p x = digitBin b p r) := by
      simp [nonzeroResidues, hs0.ne', hsp, hdigit]
    have hcard : ((nonzeroResidues p).filter
        (fun x => digitBin b p x = digitBin b p r)).card ≤ 1 := by
      exact hpopulation (digitBin b p r) (Finset.mem_range.mpr hdlt)
    rw [Finset.card_le_one_iff] at hcard
    exact hcard hrmem hsmem

/-- The Fourier energy is minimal exactly when every occupied digit bin is a
singleton, equivalently exactly in the digit-partitioning regime. -/
theorem digitBinSquareSum_minimal_iff_digitPartitioning {b p : ℕ}
    (hb : 0 < b) (hp : 0 < p) :
    digitBinSquareSum b p = p - 1 ↔ DigitPartitioning b p := by
  rw [digitBinSquareSum_eq_mass_iff hb hp,
    digitPartitioning_iff_population_le_one hb hp]

end NField.Alignment

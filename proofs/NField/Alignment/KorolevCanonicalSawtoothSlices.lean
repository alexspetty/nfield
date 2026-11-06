/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevCanonicalPhaseSlices
import NField.Alignment.InverseResiduePrefixCompletion

/-! # Exact Fourier reduction of the actual canonical sawtooth slice -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevCanonicalSawtoothSlices
open KorolevCanonicalPrimeSlices KorolevCanonicalPhaseSlices KorolevCanonicalPrimeFactors
  DedekindInverseResidueTransform DedekindReciprocity DedekindFourierMoment CarryBoundarySpectra
open scoped BigOperators Classical

/-- On unit arguments the manuscript's rational sawtooth has the exact intrinsic Fourier expansion. -/
theorem sawtooth_fourier_on_unit {m : ℕ} [NeZero m] (r n : ℕ) (hn : n.Coprime m) :
    ((rationalSawtooth (r*inverseResidue n m) m : ℚ) : ℂ) =
      (m : ℂ)⁻¹ * ∑ j : ZMod m, ZMod.dft (centeredSawtooth : ZMod m → ℂ) j *
        integerPhase (j*(r : ZMod m)) 0 n := by
  rw [← inverseSawCoefficient_eq_rationalSawtooth (Nat.pos_of_ne_zero (NeZero.ne m)) hn]
  unfold inverseSawCoefficient
  rw [dif_neg (NeZero.ne m), dif_pos hn]
  have he : ((ZMod.unitOfCoprime n hn)⁻¹ : (ZMod m)ˣ).val = (n : ZMod m)⁻¹ := by
    rw [← ZMod.inv_coe_unit]; rfl
  rw [he, centeredSawtooth_fourier_inversion]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  unfold integerPhase
  simp only [zero_mul, add_zero]
  rw [show j*((r : ZMod m)*(n : ZMod m)⁻¹) = (j*(r : ZMod m))*(n : ZMod m)⁻¹ by ring]
  ring

/-- Canonical slices depend only on values at units when their square/residual factors are units. -/
theorem slice_congr_on_units (P Q P₀ Q₀ : Finset ℕ) (l h X m : ℕ)
    (f g : ℕ → ℂ) (hl : l.Coprime m) (hh : h.Coprime m)
    (heq : ∀ n : ℕ, n.Coprime m → f n = g n) :
    primeSliceOn P Q P₀ Q₀ l h X m f = primeSliceOn P Q P₀ Q₀ l h X m g := by
  unfold primeSliceOn
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  split_ifs with hc
  · exact heq _ ((((hl.pow_left 2).mul_left hc.1).mul_left hc.2.2.1).mul_left hh)
  · rfl

/-- The exact prime-slice operator commutes with finite complex linear combinations. -/
theorem slice_linear_sum {ι : Type*} [Fintype ι]
    (P Q P₀ Q₀ : Finset ℕ) (l h X m : ℕ) (K : ℂ) (C : ι → ℂ) (F : ι → ℕ → ℂ) :
    primeSliceOn P Q P₀ Q₀ l h X m (fun n => K * ∑ j, C j * F j n) =
      K * ∑ j, C j * primeSliceOn P Q P₀ Q₀ l h X m (F j) := by
  let keep := fun p q : ℕ => p.Coprime m ∧ Cutoff P h p ∧ q.Coprime m ∧ Cutoff Q h q ∧ l^2*p*q*h ≤ X
  have ht (p q : ℕ) :
      (if keep p q then K * ∑ j, C j * F j (l^2*p*q*h) else 0) =
        K * ∑ j, C j * (if keep p q then F j (l^2*p*q*h) else 0) := by
    by_cases hc : keep p q <;> simp [hc]
  unfold primeSliceOn
  change (∑ p ∈ P₀, ∑ q ∈ Q₀, if keep p q then K * ∑ j, C j * F j (l^2*p*q*h) else 0) = _
  simp_rw [ht, ← Finset.mul_sum]
  congr 1
  simp_rw [Finset.sum_comm (s := Q₀) (t := Finset.univ)]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
  rfl

/-- The actual rational-sawtooth slice is an exact finite combination of canonical inverse phases. -/
theorem sawtooth_slice_fourier {m : ℕ} [NeZero m]
    (P Q P₀ Q₀ : Finset ℕ) (l h X r : ℕ) (hl : l.Coprime m) (hh : h.Coprime m) :
    primeSliceOn P Q P₀ Q₀ l h X m
      (fun n => ((rationalSawtooth (r*inverseResidue n m) m : ℚ) : ℂ)) =
      (m : ℂ)⁻¹ * ∑ j : ZMod m, ZMod.dft (centeredSawtooth : ZMod m → ℂ) j *
        primeSliceOn P Q P₀ Q₀ l h X m (integerPhase (j*(r : ZMod m)) 0) := by
  rw [slice_congr_on_units P Q P₀ Q₀ l h X m _
    (fun n => (m : ℂ)⁻¹ * ∑ j : ZMod m, ZMod.dft (centeredSawtooth : ZMod m → ℂ) j *
      integerPhase (j*(r : ZMod m)) 0 n) hl hh (fun n hn => sawtooth_fourier_on_unit r n hn)]
  exact slice_linear_sum P Q P₀ Q₀ l h X m _ _ _

/-- Exact sawtooth inversion and product completion retain the full frequency-dependent bounds. -/
theorem norm_sawtooth_slice_le {m : ℕ} [NeZero m]
    (P Q P₀ Q₀ : Finset ℕ) (l h X r : ℕ)
    (hlpos : 0 < l) (hhpos : 0 < h) (hl : l.Coprime m) (hh : h.Coprime m)
    (hrect : ∀ p ∈ P₀, ∀ q ∈ Q₀, p*q < m) (B : ZMod m → ℝ)
    (hbound : ∀ j c : ZMod m,
      ‖KaratsubaBilinearReduction.bilinearPrimeSum (canonicalDomain P P₀ h m) (canonicalDomain Q Q₀ h m)
        ((j*(r : ZMod m))*((l^2*h : ℕ) : ZMod m)⁻¹) c‖ ≤ B j) :
    ‖primeSliceOn P Q P₀ Q₀ l h X m
      (fun n => ((rationalSawtooth (r*inverseResidue n m) m : ℚ) : ℂ))‖ ≤
      (1+(harmonic m : ℝ))/(m : ℝ) *
        ∑ j : ZMod m, ‖ZMod.dft (centeredSawtooth : ZMod m → ℂ) j‖ * B j := by
  rw [sawtooth_slice_fourier P Q P₀ Q₀ l h X r hl hh, norm_mul, norm_inv, Complex.norm_natCast]
  have hterm (j : ZMod m) :
      ‖primeSliceOn P Q P₀ Q₀ l h X m (integerPhase (j*(r : ZMod m)) 0)‖ ≤
        (1+(harmonic m : ℝ))*B j := by
    apply norm_primeSliceOn_le P Q P₀ Q₀ l h X (j*(r : ZMod m)) 0 hlpos hhpos hl hh hrect
    simpa only [zero_mul, zero_add] using hbound j
  have hs : ‖∑ j : ZMod m, ZMod.dft (centeredSawtooth : ZMod m → ℂ) j *
      primeSliceOn P Q P₀ Q₀ l h X m (integerPhase (j*(r : ZMod m)) 0)‖ ≤
      ∑ j : ZMod m, ‖ZMod.dft (centeredSawtooth : ZMod m → ℂ) j‖ * ((1+(harmonic m : ℝ))*B j) := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro j hj
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hterm j) (norm_nonneg _)
  calc
    _ ≤ (m : ℝ)⁻¹ * ∑ j : ZMod m, ‖ZMod.dft (centeredSawtooth : ZMod m → ℂ) j‖ *
        ((1+(harmonic m : ℝ))*B j) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- All unit scalings preserve the sawtooth frequency's original gcd cost. -/
theorem sawtooth_frequency_gcd {m l h r : ℕ} [NeZero m] (j : ZMod m)
    (hl : l.Coprime m) (hh : h.Coprime m) (hr : r.Coprime m) :
    (((j*(r : ZMod m))*((l^2*h : ℕ) : ZMod m)⁻¹).val).gcd m = j.val.gcd m := by
  rw [scaled_frequency_gcd (j*(r : ZMod m)) hl hh]
  exact PrimePowerGcdBound.gcd_val_mul_coprime m j r hr

end NField.Alignment.KorolevCanonicalSawtoothSlices

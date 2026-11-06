/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevCanonicalSawtoothSlices
import NField.Alignment.KorolevActualPrimeBlocks
import NField.Alignment.KorolevSourceFrequencyWeight

/-! # Absolute block bounds and their canonical sawtooth consumer

Normalization is removed only after checking the empty-domain cases.
The inverse-frequency gcd and the coupled product completion are retained.
-/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevBlockSawtoothBound
open KaratsubaBilinearReduction KaratsubaProductCutoffCompletion
  KorolevCanonicalPrimeSlices KorolevCanonicalPhaseSlices KorolevCanonicalSawtoothSlices
  KorolevLogarithmicPartition KaratsubaSourcePrimeBlocks
open scoped BigOperators Classical

/-- A normalized subset estimate gives an absolute estimate even for empty ambient blocks. -/
theorem absolute_of_normalized {m : ℕ} [NeZero m]
    {P Q P₀ Q₀ : Finset ℕ} (hP : P₀ ⊆ P) (hQ : Q₀ ⊆ Q)
    (a b : ZMod m) {B : ℝ}
    (hb : ‖bilinearPrimeSum P₀ Q₀ a b‖ / ((P.card : ℝ)*(Q.card : ℝ)) ≤ B) :
    ‖bilinearPrimeSum P₀ Q₀ a b‖ ≤ B*(P.card : ℝ)*(Q.card : ℝ) := by
  by_cases hp : P = ∅
  · have hp₀ : P₀ = ∅ := Finset.subset_empty.mp (hp ▸ hP)
    simp [hp, hp₀, bilinear_eq_double_sum]
  by_cases hq : Q = ∅
  · have hq₀ : Q₀ = ∅ := Finset.subset_empty.mp (hq ▸ hQ)
    simp [hq, hq₀, bilinear_eq_double_sum]
  have hpPos : (0 : ℝ) < P.card := by
    exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hp)
  have hqPos : (0 : ℝ) < Q.card := by
    exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hq)
  simpa only [mul_assoc] using (div_le_iff₀ (mul_pos hpPos hqPos)).mp hb

/-- Canonical filters inside a raw block are subsets of its full coprime block. -/
theorem canonicalDomain_subset (P : Finset ℕ) (h m : ℕ) (l D A : ℝ) (i : ℕ) :
    canonicalDomain P (block l D A i) h m ⊆ coprimeBlock m l D A i := by
  intro p hp
  obtain ⟨hp, hc, _⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨hp, hc⟩

/-- Weighted Fourier control consumes absolute bilinear bounds with their exact gcd root. -/
theorem norm_sawtooth_of_frequency_bound {m : ℕ} [NeZero m]
    (P Q P₀ Q₀ : Finset ℕ) (l h X r : ℕ)
    (hlpos : 0 < l) (hhpos : 0 < h) (hl : l.Coprime m) (hh : h.Coprime m)
    (hr : r.Coprime m) (hrect : ∀ p ∈ P₀, ∀ q ∈ Q₀, p*q < m)
    (ε δ N F : ℝ) (hδ : 0 ≤ δ) (hN : 0 ≤ N)
    (hbil : ∀ a b : ZMod m,
      ‖bilinearPrimeSum (canonicalDomain P P₀ h m) (canonicalDomain Q Q₀ h m) a b‖ ≤
        (a.val.gcd m : ℝ)^ε*δ*N)
    (hfreq : (∑ j : ZMod m,
      ‖ZMod.dft (CarryBoundarySpectra.centeredSawtooth : ZMod m → ℂ) j‖ *
        (j.val.gcd m : ℝ)^ε)/(m : ℝ) ≤ F) :
    ‖primeSliceOn P Q P₀ Q₀ l h X m
      (fun n => ((DedekindReciprocity.rationalSawtooth
        (r*DedekindInverseResidueTransform.inverseResidue n m) m : ℚ) : ℂ))‖ ≤
      (1+(harmonic m : ℝ))*F*δ*N := by
  have hH : 0 ≤ (harmonic m : ℝ) := by
    have hQ : (0 : ℚ) ≤ harmonic m := by unfold harmonic; positivity
    exact_mod_cast hQ
  have hb (j c : ZMod m) :
      ‖bilinearPrimeSum (canonicalDomain P P₀ h m) (canonicalDomain Q Q₀ h m)
        ((j*(r : ZMod m))*((l^2*h : ℕ) : ZMod m)⁻¹) c‖ ≤
          (j.val.gcd m : ℝ)^ε*δ*N := by
    have hh' := hbil ((j*(r : ZMod m))*((l^2*h : ℕ) : ZMod m)⁻¹) c
    rwa [sawtooth_frequency_gcd j hl hh hr] at hh'
  have hs := norm_sawtooth_slice_le P Q P₀ Q₀ l h X r hlpos hhpos hl hh hrect
    (fun j => (j.val.gcd m : ℝ)^ε*δ*N) hb
  have hid : (∑ j : ZMod m,
      ‖ZMod.dft (CarryBoundarySpectra.centeredSawtooth : ZMod m → ℂ) j‖ *
        ((j.val.gcd m : ℝ)^ε*δ*N)) =
      (∑ j : ZMod m,
        ‖ZMod.dft (CarryBoundarySpectra.centeredSawtooth : ZMod m → ℂ) j‖ *
          (j.val.gcd m : ℝ)^ε)*δ*N := by
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hid] at hs
  calc
    _ ≤ (1+(harmonic m : ℝ))/(m : ℝ) *
        ((∑ j : ZMod m,
          ‖ZMod.dft (CarryBoundarySpectra.centeredSawtooth : ZMod m → ℂ) j‖ *
            (j.val.gcd m : ℝ)^ε)*δ*N) := hs
    _ = (1+(harmonic m : ℝ))*
        ((∑ j : ZMod m,
          ‖ZMod.dft (CarryBoundarySpectra.centeredSawtooth : ZMod m → ℂ) j‖ *
            (j.val.gcd m : ℝ)^ε)/(m : ℝ))*δ*N := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hfreq (by positivity)) hδ) hN

end NField.Alignment.KorolevBlockSawtoothBound

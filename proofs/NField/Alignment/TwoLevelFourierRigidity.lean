/-
Author: Alexander S. Petty
-/

import NField.Alignment.CosetFourierReduction
import NField.Alignment.SpectralStructure

/-!
# Fourier rigidity for nonnegative cyclic overlap

This module connects constant Fourier magnitude to the single-shift support
criterion for a nonnegative cyclic count.  It supplies the Fourier bridge
between the two-coset branch formula and the point-mass overlap theorem.
-/

namespace NField.Alignment.TwoLevelFourierRigidity

open scoped BigOperators
open ZMod
open NField.Alignment.CosetFourierReduction
open NField.Alignment.SpectralStructure

variable {L : ℕ} [NeZero L]

/-- Unnormalized negative-sign DFT of a natural-valued cyclic count. -/
noncomputable def naturalDFT (Q : ZMod L → ℕ) (j : ZMod L) : ℂ :=
  ZMod.dft (fun t => (Q t : ℂ)) j

/-- Unnormalized DFT of the cyclic self-overlap of a natural-valued count. -/
noncomputable def overlapDFT (Q : ZMod L → ℕ) (j : ZMod L) : ℂ :=
  ZMod.dft (fun shift => (overlapMass Q shift : ℂ)) j

/-- Fourier transformation of cyclic self-overlap is the squared Fourier
magnitude. -/
theorem overlapDFT_neg_eq_normSq (Q : ZMod L → ℕ) (j : ZMod L) :
    overlapDFT Q (-j) = Complex.normSq (naturalDFT Q j) := by
  let q : ZMod L → ℂ := fun t => (Q t : ℂ)
  have hcorr : (fun shift => (overlapMass Q shift : ℂ)) =
      complexCrossCorrelation q q := by
    funext shift
    simp only [overlapMass, complexCrossCorrelation, q]
    push_cast
    apply Finset.sum_congr rfl
    intro t ht
    ring
  rw [overlapDFT, hcorr, dft_complexCrossCorrelation_neg]
  have hstar :
      (∑ x : ZMod L, stdAddChar (x * j) * q x) =
        starRingEnd ℂ
          (∑ t : ZMod L, stdAddChar (-(t * j)) * q t) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro t ht
    rw [map_mul (starRingEnd ℂ)]
    have hchar : starRingEnd ℂ (stdAddChar (-(t * j))) =
        stdAddChar (t * j) := by
      simpa only [starRingEnd_apply, neg_neg] using
        (AddChar.map_neg_eq_conj (stdAddChar (N := L)) (-(t * j))).symm
    rw [hchar]
    simp [q]
  rw [hstar]
  rw [Complex.normSq_eq_conj_mul_self]
  congr 1

/-- A natural point mass has constant Fourier magnitude equal to its mass. -/
theorem naturalDFT_pointMass_normSq (s : ZMod L) (mass : ℕ)
    (j : ZMod L) :
    Complex.normSq
        (naturalDFT (fun t => if t = s then mass else 0) j) =
      (mass : ℝ) ^ 2 := by
  simp [naturalDFT, ZMod.dft_apply, Complex.normSq_eq_norm_sq,
    pow_two, AddChar.norm_apply]

/-- Constant squared Fourier magnitude forces every nonzero cyclic
self-overlap to vanish. -/
theorem constant_normSq_overlap_zero (Q : ZMod L → ℕ) (mass : ℕ)
    (hconstant : ∀ j,
      Complex.normSq (naturalDFT Q j) = (mass : ℝ) ^ 2) :
    ∀ shift : ZMod L, shift ≠ 0 → overlapMass Q shift = 0 := by
  let R : ZMod L → ℂ := fun shift => (overlapMass Q shift : ℂ)
  let P : ZMod L → ℂ := fun shift =>
    if shift = 0 then ((mass : ℝ) ^ 2 : ℂ) else 0
  have hdft : ZMod.dft R = ZMod.dft P := by
    funext k
    calc
      ZMod.dft R k = overlapDFT Q k := by rfl
      _ = Complex.normSq (naturalDFT Q (-k)) := by
        simpa using overlapDFT_neg_eq_normSq Q (-k)
      _ = ((mass : ℝ) ^ 2 : ℂ) := by
        exact_mod_cast hconstant (-k)
      _ = ZMod.dft P k := by
        simp [P, ZMod.dft_apply]
  have hRP : R = P := ZMod.dft.injective hdft
  intro shift hshift
  have hvalue := congrFun hRP shift
  simp [R, P, hshift] at hvalue
  exact_mod_cast hvalue

/-- Constant Fourier magnitude is equivalent to single-shift support for a
nonzero nonnegative cyclic count. -/
theorem constant_normSq_iff_pointMass (Q : ZMod L → ℕ)
    (hmass : 0 < ∑ t, Q t) :
    (∃ mass : ℕ, 0 < mass ∧ ∀ j,
        Complex.normSq (naturalDFT Q j) = (mass : ℝ) ^ 2) ↔
      ∃ s : ZMod L, ∃ mass : ℕ, 0 < mass ∧
        Q = fun t => if t = s then mass else 0 := by
  constructor
  · rintro ⟨mass, hmassPositive, hconstant⟩
    have hoff := constant_normSq_overlap_zero Q mass hconstant
    obtain ⟨s, pointMass, hpointMass, hQ⟩ :=
      (overlap_zero_iff_point_mass Q hmass).mp hoff
    refine ⟨s, pointMass, ?_, hQ⟩
    rw [hpointMass]
    exact hmass
  · rintro ⟨s, mass, hmassPositive, rfl⟩
    exact ⟨mass, hmassPositive, naturalDFT_pointMass_normSq s mass⟩

end NField.Alignment.TwoLevelFourierRigidity

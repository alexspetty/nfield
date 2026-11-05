/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionComplexCyclicity

/-!
# Literal translation spectral measures and cyclicity

The conductor sums below use the actual reduced numerators in 1..q-1.
Those sets are empty for q=0 and q=1, so the sums start at q=2. The Borel
measures on (0,1) represent circle frequencies through periodic Fourier
tests. Both moment identities and both real and complex cyclic-span claims
concern the actual profinite Haar observables.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionSpectralMeasures

open scoped BigOperators
open MeasureTheory ProfiniteRemainderMeasure CollisionPotentialHilbert
open CollisionPotentialConvergence CollisionPotentialCoboundary CollisionOdometerRecurrence
open CollisionAtomicSpectra CollisionSpectralWeights CollisionSpectralSupport
open CollisionPotentialSpectralMoments CollisionSpectralMomentRecurrence
open CollisionWeightMultiples CollisionJordanVariance CollisionTranslationSubspace
open CollisionIncrementCyclicity CollisionComplexCyclicity

theorem primitiveNumerators_empty_below_two {q : ℕ} (hq : q<2) :
    primitiveNumerators q=∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro a ha
  have hi := Finset.mem_Ico.mp (Finset.mem_filter.mp ha).1
  omega

theorem atomicMeasure_by_conductor (w : SpectralAddress → ℝ) :
    atomicMeasure w=Measure.sum (fun q : ℕ => Measure.sum
      (fun a : {a : ℕ // a ∈ primitiveNumerators q} =>
        ENNReal.ofReal (w ⟨q,a⟩) • Measure.dirac (frequency ⟨q,a⟩))) := by
  ext s hs
  simp only [atomicMeasure, Measure.sum_apply _ hs]
  exact ENNReal.tsum_sigma' _

theorem incrementMeasure_literal : incrementMeasure=Measure.sum (fun q : ℕ =>
    ∑ a ∈ primitiveNumerators q, ENNReal.ofReal ((4/9 : ℝ)*(amplitude q)^2) •
      Measure.dirac ((a : ℝ)/(q : ℝ))) := by
  rw [incrementMeasure, atomicMeasure_by_conductor]
  congr 1
  funext q
  change Measure.sum (fun a : {a : ℕ // a ∈ primitiveNumerators q} =>
    ENNReal.ofReal ((4/9 : ℝ)*(amplitude q)^2) • Measure.dirac ((a.1 : ℝ)/(q : ℝ)))=_
  exact Measure.sum_coe_finset (primitiveNumerators q)
    (fun a : ℕ => ENNReal.ofReal ((4/9 : ℝ)*(amplitude q)^2) •
      Measure.dirac ((a : ℝ)/(q : ℝ)))

theorem potentialMeasure_literal : potentialMeasure=Measure.sum (fun q : ℕ =>
    ∑ a ∈ primitiveNumerators q, ENNReal.ofReal ((1/9 : ℝ)*(amplitude q)^2*
      (Real.sin (Real.pi*(a : ℝ)/(q : ℝ))^2)⁻¹) • Measure.dirac ((a : ℝ)/(q : ℝ))) := by
  rw [potentialMeasure, atomicMeasure_by_conductor]
  simp only [potentialMass_literal, frequency]
  congr 1
  funext q
  exact Measure.sum_coe_finset (primitiveNumerators q)
    (fun a : ℕ => ENNReal.ofReal ((1/9 : ℝ)*(amplitude q)^2*
      (Real.sin (Real.pi*(a : ℝ)/(q : ℝ))^2)⁻¹) • Measure.dirac ((a : ℝ)/(q : ℝ)))

theorem literal_translation_spectral_measures :
    incrementMeasure=Measure.sum (fun q : ℕ =>
      ∑ a ∈ primitiveNumerators q, ENNReal.ofReal ((4/9 : ℝ)*(amplitude q)^2) •
        Measure.dirac ((a : ℝ)/(q : ℝ))) ∧
    potentialMeasure=Measure.sum (fun q : ℕ =>
      ∑ a ∈ primitiveNumerators q, ENNReal.ofReal ((1/9 : ℝ)*(amplitude q)^2*
        (Real.sin (Real.pi*(a : ℝ)/(q : ℝ))^2)⁻¹) • Measure.dirac ((a : ℝ)/(q : ℝ))) ∧
    IsFiniteMeasure incrementMeasure ∧ IsFiniteMeasure potentialMeasure ∧
    (∀ h : ℤ, (∫ t, fourierCharacter h t ∂incrementMeasure)=(incrementCovariance h : ℂ)) ∧
    (∀ h : ℤ, (∫ t, fourierCharacter h t ∂potentialMeasure)=
      (haarCovariance collisionPotential h : ℂ)) ∧
    (∀ i : SpectralAddress, 0 < incrementMeasure {frequency i} ∧ 0 < potentialMeasure {frequency i}) ∧
    (∀ V : HaarL2, V ∈ cyclicSpace incrementVector ↔ (∫ x, V x ∂phaseHaar)=0) ∧
    (∀ V : ComplexHaarL2, V ∈ complexCyclicSpace ↔ (∫ x, V x ∂phaseHaar)=0) := by
  exact ⟨incrementMeasure_literal, potentialMeasure_literal, inferInstance, inferInstance,
    incrementMeasure_fourier, potentialMeasure_fourier,
    fun i => ⟨incrementMeasure_atom_pos i, potentialMeasure_atom_pos i⟩,
    literal_increment_cyclic_span, literal_complex_increment_cyclic_span⟩

end NField.Alignment.CollisionSpectralMeasures

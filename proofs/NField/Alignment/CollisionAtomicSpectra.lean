/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionSpectralWeights
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Atomic measures and their absolutely convergent Fourier moments

Both measures are actual finite positive Borel measures on the open unit
interval, regarded as a fundamental domain for rational circle frequencies.
Their translation test functions are periodic. The increment's moments
are identified with the already proved Haar covariance.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionAtomicSpectra

open scoped BigOperators
open MeasureTheory CollisionSpectralWeights CollisionRamanujan
open CollisionWeightMultiples CollisionJordanVariance CollisionRamanujanCovariance
open CollisionDivisibilityCovariance CollisionOdometerRecurrence

def atomicMeasure (w : SpectralAddress → ℝ) : Measure ℝ :=
  Measure.sum (fun i => ENNReal.ofReal (w i) • Measure.dirac (frequency i))

def incrementMeasure : Measure ℝ := atomicMeasure incrementMass
def potentialMeasure : Measure ℝ := atomicMeasure potentialMass

def fourierCharacter (h : ℤ) (t : ℝ) : ℂ :=
  Complex.exp (2*(Real.pi : ℂ)*Complex.I*(h : ℂ)*(t : ℂ))

theorem fourierCharacter_frequency (h : ℤ) (i : SpectralAddress) :
    fourierCharacter h (frequency i) = phase i.1 h i.2.1 := by
  unfold fourierCharacter frequency phase
  push_cast
  congr 1
  ring

theorem atomicMeasure_mass (w : SpectralAddress → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : Summable w) : atomicMeasure w Set.univ = ENNReal.ofReal (∑' i, w i) := by
  simp only [atomicMeasure, Measure.sum_apply _ MeasurableSet.univ,
    Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  exact (ENNReal.ofReal_tsum_of_nonneg hw hs).symm

theorem atomicMeasure_finite (w : SpectralAddress → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : Summable w) : IsFiniteMeasure (atomicMeasure w) := by
  constructor
  rw [atomicMeasure_mass w hw hs]
  exact ENNReal.ofReal_lt_top

instance incrementMeasure_finite : IsFiniteMeasure incrementMeasure :=
  atomicMeasure_finite _ incrementMass_nonneg incrementMass_summable

instance potentialMeasure_finite : IsFiniteMeasure potentialMeasure :=
  atomicMeasure_finite _ potentialMass_nonneg potentialMass_summable

theorem atomicMeasure_outside (w : SpectralAddress → ℝ) :
    atomicMeasure w (Set.Ioo (0 : ℝ) 1)ᶜ = 0 := by
  rw [atomicMeasure, Measure.sum_apply _ measurableSet_Ioo.compl]
  apply ENNReal.tsum_eq_zero.mpr
  intro i
  simp [Measure.smul_apply, Measure.dirac_apply' _ measurableSet_Ioo.compl,
    frequency_mem i]

theorem weightedPhase_norm (w : SpectralAddress → ℝ) (hw : ∀ i, 0 ≤ w i)
    (h : ℤ) (i : SpectralAddress) : ‖(w i : ℂ)*phase i.1 h i.2.1‖ = w i := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i), phase_norm,
    mul_one]

theorem weightedPhase_summable (w : SpectralAddress → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : Summable w) (h : ℤ) : Summable (fun i => (w i : ℂ)*phase i.1 h i.2.1) := by
  apply Summable.of_norm
  simpa only [weightedPhase_norm w hw h] using hs

theorem fourierCharacter_integrable (w : SpectralAddress → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : Summable w) (h : ℤ) : Integrable (fourierCharacter h) (atomicMeasure w) := by
  apply integrable_sum_dirac (fun i => ENNReal.ofReal_ne_top)
  simpa only [fourierCharacter_frequency, phase_norm, mul_one,
    ENNReal.toReal_ofReal (hw _)] using hs

theorem atomicMeasure_fourier (w : SpectralAddress → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : Summable w) (h : ℤ) :
    (∫ t, fourierCharacter h t ∂atomicMeasure w) =
      ∑' i, (w i : ℂ)*phase i.1 h i.2.1 := by
  have hn : Summable (fun i => (ENNReal.ofReal (w i)).toReal *
      ‖fourierCharacter h (frequency i)‖) := by
    simpa only [fourierCharacter_frequency, phase_norm, mul_one,
      ENNReal.toReal_ofReal (hw _)] using hs
  rw [atomicMeasure, integral_sum_dirac_eq_tsum (fun i => ENNReal.ofReal_ne_top) hn]
  simp only [ENNReal.toReal_ofReal (hw _), fourierCharacter_frequency,
    Complex.real_smul]

theorem incrementPhase_fiber (q : ℕ) (h : ℤ) :
    (∑ a : {a : ℕ // a ∈ primitiveNumerators q},
      (incrementMass ⟨q,a⟩ : ℂ)*phase q h a.1) =
      (4/9 : ℂ)*complexCovarianceCoefficient h q := by
  classical
  by_cases hq : 2 ≤ q
  · simp only [incrementMass, Complex.ofReal_mul, Complex.ofReal_div,
      Complex.ofReal_ofNat, Complex.ofReal_pow]
    rw [← Finset.mul_sum, Finset.sum_coe_sort]
    simp only [complexCovarianceCoefficient, if_pos hq, primitiveSum,
      if_neg (show q ≠ 1 by omega), zero_add, primitiveNumerators]
    ring
  · haveI : IsEmpty {a : ℕ // a ∈ primitiveNumerators q} := ⟨by
      intro a
      have hi := Finset.mem_Ico.mp (Finset.mem_filter.mp a.2).1
      omega⟩
    simp [complexCovarianceCoefficient, hq]

theorem incrementMeasure_fourier (h : ℤ) :
    (∫ t, fourierCharacter h t ∂incrementMeasure) = (incrementCovariance h : ℂ) := by
  rw [incrementMeasure, atomicMeasure_fourier _ incrementMass_nonneg incrementMass_summable]
  rw [(weightedPhase_summable _ incrementMass_nonneg incrementMass_summable h).tsum_sigma]
  simp_rw [tsum_fintype, incrementPhase_fiber]
  rw [tsum_mul_left, incrementCovariance_primitive]

theorem potentialMeasure_mass : potentialMeasure Set.univ =
    ENNReal.ofReal (‖CollisionPotentialConvergence.collisionPotential‖^2) := by
  rw [potentialMeasure, atomicMeasure_mass _ potentialMass_nonneg potentialMass_summable,
    potentialMass_total]

end NField.Alignment.CollisionAtomicSpectra

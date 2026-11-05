/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperPrimeBlockGaussian
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Actual joint block events and the independent normal product law

The joint event uses the literal source-block logarithms under the actual
weighted phase measure. The comparison law is the finite product of the
actual normal measures. Both rectangle probabilities factor exactly.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperPrimeBlockJointLaw
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set SteinhausMoment HarperPrimeBlocks
  HarperPrimeBlockLaw HarperPrimeBlockGaussian HarperTiltedMeasure HarperEulerIntegral

variable {ι : Type*} [Fintype ι]

def jointBlockEvent (x : ℝ) (l : ι → ℕ) (t : ι → ℝ) (I : ι → Set ℝ) : Set PhaseSpace :=
  {ω | ∀ i, blockLog x (l i) (t i) ω ∈ I i}

def normalProductLaw (x : ℝ) (l : ι → ℕ) (t : ι → ℝ) : Measure (ι → ℝ) :=
  Measure.pi (fun i => blockNormal x (l i) (t i))

theorem jointBlockEvent_measurable (x : ℝ) (l : ι → ℕ) (t : ι → ℝ)
    (I : ι → Set ℝ) (hI : ∀ i, MeasurableSet (I i)) :
    MeasurableSet (jointBlockEvent x l t I) := by
  have he : jointBlockEvent x l t I = ⋂ i, (blockLog x (l i) (t i)) ⁻¹' I i := by
    ext ω
    simp [jointBlockEvent]
  rw [he]
  exact MeasurableSet.iInter (fun i => (hI i).preimage (blockLog_measurable x (l i) (t i)))

theorem normalProductLaw_probability (x : ℝ) (l : ι → ℕ) (t : ι → ℝ) :
    IsProbabilityMeasure (normalProductLaw x l t) := by
  unfold normalProductLaw blockNormal
  infer_instance

theorem jointBlockEvent_probability {x : ℝ} (hx : 1 ≤ x)
    (l : ι → ℕ) (hl : Function.Injective l) (t : ι → ℝ)
    (I : ι → Set ℝ) (hI : ∀ i, MeasurableSet (I i)) :
    (tiltedMeasure (sourceCutoff x) (linePoint (1/2) 0)).real (jointBlockEvent x l t I) =
      ∏ i, (blockLaw x (l i) (t i)).real (I i) := by
  classical
  have hi := blockLogs_independent hx l hl t
  have he : jointBlockEvent x l t I =
      ⋂ i ∈ (Finset.univ : Finset ι), (blockLog x (l i) (t i)) ⁻¹' I i := by
    ext ω
    simp [jointBlockEvent]
  have h := hi.measure_inter_preimage_eq_mul Finset.univ (fun i _ => hI i)
  rw [← he] at h
  rw [measureReal_def, h, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [measureReal_def, blockLaw,
    Measure.map_apply (blockLog_measurable x (l i) (t i)) (hI i)]

theorem normalProductLaw_rectangle (x : ℝ) (l : ι → ℕ) (t : ι → ℝ)
    (I : ι → Set ℝ) :
    (normalProductLaw x l t).real (Set.univ.pi I) =
      ∏ i, (blockNormal x (l i) (t i)).real (I i) := by
  unfold normalProductLaw blockNormal
  rw [measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]
  rfl

end NField.Alignment.HarperPrimeBlockJointLaw

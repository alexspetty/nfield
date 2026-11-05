/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionIntegerLawTests
import NField.Alignment.CollisionIntegerIncrementMoments
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Actual weak empirical joint laws for fixed increments

The empirical measure assigns equal mass to samples 1 through N+1. Its
weak limit is the Haar push-forward, first for resets and then for the
continuous affine transformation giving the literal increments.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionIntegerJointLaw

open scoped BigOperators Classical NNReal
open Filter MeasureTheory
open ProfiniteRemainderMeasure ProfinitePeriodicTesting CollisionRemainderDynamics
open CollisionResetIntegrability CollisionPotentialCoboundary CollisionJointMoments
open CollisionIntegerJointMoments CollisionIntegerIncrementMoments CollisionIntegerLawTests

def uniformSample (N : ℕ) : ProbabilityMeasure (Fin (N+1)) :=
  ⟨(PMF.uniformOfFintype (Fin (N+1))).toMeasure, inferInstance⟩

def empiricalLaw {Ω : Type*} [MeasurableSpace Ω] (N : ℕ) (u : ℕ → Ω) :
    ProbabilityMeasure Ω :=
  (uniformSample N).map (measurable_of_finite (fun j : Fin (N+1) => u (j.val+1))).aemeasurable

theorem empiricalLaw_integral {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    [BorelSpace Ω] (N : ℕ) (u : ℕ → Ω) {φ : Ω → ℝ} (hφ : Continuous φ) :
    (∫ x, φ x ∂(empiricalLaw N u))=orbitAverage (N+1) (fun n => φ (u n)) := by
  change (∫ x, φ x ∂Measure.map (fun j : Fin (N+1) => u (j.val+1))
    (PMF.uniformOfFintype (Fin (N+1))).toMeasure)=_
  rw [integral_map (measurable_of_finite _).aemeasurable hφ.aestronglyMeasurable,
    PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fin, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul, ← Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun n => φ (u (n+1))) (N+1)]
  unfold orbitAverage
  rw [div_eq_mul_inv, mul_comm]

def phaseProbability : ProbabilityMeasure Phase := ⟨phaseHaar, inferInstance⟩

def haarResetLaw (r : ℕ) (h : Fin r → ℕ) : ProbabilityMeasure (Fin r → ℝ) :=
  phaseProbability.map (jointResetPhase_aemeasurable r h)

def empiricalResetLaw (r : ℕ) (h : Fin r → ℕ) (N : ℕ) : ProbabilityMeasure (Fin r → ℝ) :=
  empiricalLaw N (fun n => jointResetPhase r h (integerPhase n))

theorem haarResetLaw_integral (r : ℕ) (h : Fin r → ℕ) {φ : (Fin r → ℝ) → ℝ}
    (hφ : Continuous φ) :
    (∫ v, φ v ∂(haarResetLaw r h))=∫ x, φ (jointResetPhase r h x) ∂phaseHaar := by
  exact integral_map (jointResetPhase_aemeasurable r h) hφ.aestronglyMeasurable

theorem empiricalResetLaw_tendsto (r : ℕ) (h : Fin r → ℕ) :
    Tendsto (empiricalResetLaw r h) atTop (nhds (haarResetLaw r h)) := by
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  intro φ hb hL
  obtain ⟨L,hφ⟩ := hL
  have ht := (joint_reset_bounded_lipschitz_tendsto r h hφ hb).comp (tendsto_add_atTop_nat 1)
  simp only [empiricalResetLaw, empiricalLaw_integral _ _ hφ.continuous,
    haarResetLaw_integral r h hφ.continuous]
  convert! ht using 1

def incrementMap (r : ℕ) (v : Fin r → ℝ) : Fin r → ℝ := fun i => (2/3 : ℝ)*(1-v i)

theorem incrementMap_continuous (r : ℕ) : Continuous (incrementMap r) := by
  unfold incrementMap
  fun_prop

def jointIncrementPhase (r : ℕ) (h : Fin r → ℕ) (x : Phase) : Fin r → ℝ :=
  fun i => increment (CollisionPotentialCoboundary.translate (h i : ℤ) x)

theorem jointIncrementPhase_eq_map (r : ℕ) (h : Fin r → ℕ) :
    jointIncrementPhase r h=incrementMap r ∘ jointResetPhase r h := rfl

theorem jointIncrementPhase_aemeasurable (r : ℕ) (h : Fin r → ℕ) :
    AEMeasurable (jointIncrementPhase r h) phaseHaar :=
  (incrementMap_continuous r).measurable.comp_aemeasurable (jointResetPhase_aemeasurable r h)

def haarIncrementLaw (r : ℕ) (h : Fin r → ℕ) : ProbabilityMeasure (Fin r → ℝ) :=
  phaseProbability.map (jointIncrementPhase_aemeasurable r h)

def empiricalIncrementLaw (r : ℕ) (h : Fin r → ℕ) (N : ℕ) : ProbabilityMeasure (Fin r → ℝ) :=
  empiricalLaw N (fun n i => increment (integerPhase (n+h i : ℕ)))

theorem haarIncrementLaw_eq_map (r : ℕ) (h : Fin r → ℕ) :
    haarIncrementLaw r h=(haarResetLaw r h).map (incrementMap_continuous r).measurable.aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (jointIncrementPhase r h) phaseHaar =
    Measure.map (incrementMap r) (Measure.map (jointResetPhase r h) phaseHaar)
  rw [AEMeasurable.map_map_of_aemeasurable (incrementMap_continuous r).measurable.aemeasurable
    (jointResetPhase_aemeasurable r h), jointIncrementPhase_eq_map]

theorem empiricalIncrementLaw_eq_map (r : ℕ) (h : Fin r → ℕ) (N : ℕ) :
    empiricalIncrementLaw r h N=(empiricalResetLaw r h N).map
      (incrementMap_continuous r).measurable.aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (fun j : Fin (N+1) => fun i => increment (integerPhase (j.val+1+h i : ℕ)))
      (PMF.uniformOfFintype (Fin (N+1))).toMeasure =
    Measure.map (incrementMap r) (Measure.map
      (fun j : Fin (N+1) => jointResetPhase r h (integerPhase (j.val+1 : ℕ)))
      (PMF.uniformOfFintype (Fin (N+1))).toMeasure)
  rw [Measure.map_map (incrementMap_continuous r).measurable (measurable_of_finite _)]
  congr 1
  funext j i
  simp only [Function.comp_apply, incrementMap, jointResetPhase, translate_integerPhase, increment]

theorem empiricalIncrementLaw_tendsto (r : ℕ) (h : Fin r → ℕ) :
    Tendsto (empiricalIncrementLaw r h) atTop (nhds (haarIncrementLaw r h)) := by
  have ht := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (empiricalResetLaw r h) (haarResetLaw r h) (empiricalResetLaw_tendsto r h)
    (incrementMap_continuous r)
  change Tendsto (fun N => empiricalIncrementLaw r h N) atTop (nhds (haarIncrementLaw r h))
  simp only [empiricalIncrementLaw_eq_map, haarIncrementLaw_eq_map]
  exact ht

theorem integer_laws_for_fixed_increments (r : ℕ) (h : Fin r → ℕ) :
    Tendsto (empiricalIncrementLaw r h) atTop (nhds (haarIncrementLaw r h)) ∧
    (∀ p : Fin r → ℕ, Tendsto (fun N => orbitAverage N
      (fun n => ∏ i, increment (integerPhase (n+h i : ℕ))^(p i))) atTop
      (nhds (∫ x, ∏ i, increment
        (CollisionPotentialCoboundary.translate (h i : ℤ) x)^(p i) ∂phaseHaar))) ∧
    HasSum (jointCRTTerm r h) (∫ x, ∏ i, resetFunction
      (CollisionPotentialCoboundary.translate (h i : ℤ) x) ∂phaseHaar) ∧
    (∀ H : ℕ, Tendsto (fun N => orbitAverage N
      (fun n => |CollisionMassReadout.deficit (n+H)-CollisionMassReadout.deficit n|^2)) atTop
      (nhds (∫ x, |blockFunction H x|^2 ∂phaseHaar))) :=
  ⟨empiricalIncrementLaw_tendsto r h, increment_mixed_moment_tendsto r h,
    joint_moment_CRT_hasSum r h, deficit_block_second_moment_tendsto⟩

end NField.Alignment.CollisionIntegerJointLaw

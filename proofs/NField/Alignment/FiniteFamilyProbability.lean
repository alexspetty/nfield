/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.FiniteFamilyTransversality
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.Basic

/-! # Uniform counting and independent finite CRT coordinates -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.FiniteFamilyProbability
open scoped BigOperators Classical ENNReal
open MeasureTheory ProbabilityTheory

def uniformMeasure (α : Type*) [Fintype α] [Nonempty α] [MeasurableSpace α] : Measure α :=
  (PMF.uniformOfFintype α).toMeasure

instance {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α] :
    IsProbabilityMeasure (uniformMeasure α) := inferInstanceAs
      (IsProbabilityMeasure (PMF.uniformOfFintype α).toMeasure)

theorem uniformMeasure_singleton {α : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (a : α) :
    uniformMeasure α {a} = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  rw [uniformMeasure, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a),
    PMF.uniformOfFintype_apply]

theorem uniformMeasure_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)] [∀ i, MeasurableSpace (α i)]
    [∀ i, MeasurableSingletonClass (α i)] :
    uniformMeasure (∀ i, α i) = Measure.pi (fun i => uniformMeasure (α i)) := by
  classical
  apply Measure.ext_of_singleton
  intro a
  rw [uniformMeasure_singleton, Measure.pi_singleton]
  simp only [uniformMeasure_singleton, Fintype.card_pi, Nat.cast_prod]
  exact ENNReal.prod_inv_distrib (fun _ _ _ _ _ => Or.inr (ENNReal.natCast_ne_top _))

theorem uniformMeasure_map_equiv {α β : Type*} [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β] [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β] (e : α ≃ β) :
    (uniformMeasure α).map e = uniformMeasure β := by
  classical
  apply Measure.ext_of_singleton
  intro b
  rw [Measure.map_apply (measurable_of_finite e) (measurableSet_singleton b)]
  have he : e ⁻¹' {b} = {e.symm b} := by ext a; simp [Equiv.eq_symm_apply]
  rw [he, uniformMeasure_singleton, uniformMeasure_singleton, Fintype.card_congr e]

theorem uniformMeasure_map_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)] [∀ i, MeasurableSpace (α i)]
    [∀ i, MeasurableSingletonClass (α i)] (i : ι) :
    (uniformMeasure (∀ i, α i)).map (fun x => x i) = uniformMeasure (α i) := by
  rw [uniformMeasure_pi]
  exact (measurePreserving_eval (fun i => uniformMeasure (α i)) i).map_eq

/-- Every finite bijection to the product carries uniform counting to independent coordinates. -/
theorem independent_coordinates_equiv {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [Nonempty Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    {α : ι → Type*} [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSingletonClass (α i)]
    (e : Ω ≃ ∀ i, α i) :
    iIndepFun (fun i x => e x i) (uniformMeasure Ω) := by
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (fun i => (measurable_of_finite (fun x => e x i)).aemeasurable)).mpr
  have hi (i : ι) : (uniformMeasure Ω).map (fun x => e x i) = uniformMeasure (α i) := by
    change (uniformMeasure Ω).map ((fun x : ∀ i, α i => x i) ∘ e) = _
    rw [← Measure.map_map (measurable_of_finite (fun x : ∀ i, α i => x i))
      (measurable_of_finite e), uniformMeasure_map_equiv, uniformMeasure_map_coordinate]
  simp_rw [hi]
  exact (uniformMeasure_map_equiv e).trans uniformMeasure_pi

/-- Coordinate signals are independent, with no centering hypothesis required. -/
theorem independent_signals_equiv {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [Nonempty Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    {α β : ι → Type*} [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSingletonClass (α i)]
    [∀ i, MeasurableSpace (β i)] (e : Ω ≃ ∀ i, α i) (f : ∀ i, α i → β i) :
    iIndepFun (fun i x => f i (e x i)) (uniformMeasure Ω) :=
  (independent_coordinates_equiv e).comp f (fun i => measurable_of_finite (f i))

end NField.Alignment.FiniteFamilyProbability

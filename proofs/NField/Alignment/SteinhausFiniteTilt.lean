/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.SteinhausCoordinates
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Finite coordinate weighting of the actual infinite Haar product

A finite product of normalized coordinate densities gives exactly the
infinite product of the weighted coordinate laws. The proof checks every
measurable finite cylinder, retaining untouched coordinates. This will be
applied to the actual Euler-factor densities, whose normalization is proved
separately rather than assumed in the analytic consumer.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.SteinhausFiniteTilt
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory SteinhausMoment

theorem coordinate_lintegral (q : ℕ) {f : UnitAddCircle → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ ω, f (ω q) ∂phaseMeasure) = ∫⁻ x, f x ∂AddCircle.haarAddCircle := by
  rw [← lintegral_map hf (measurable_pi_apply q), phaseMeasure, Measure.infinitePi_map_eval]

theorem finite_density_product_law (S : Finset ℕ) (w : ℕ → UnitAddCircle → ℝ≥0∞)
    (hm : ∀ q, Measurable (w q))
    (hone : ∀ q, (∫⁻ x, w q x ∂AddCircle.haarAddCircle) = 1)
    (hout : ∀ q ∉ S, ∀ x, w q x = 1) :
    phaseMeasure.withDensity (fun ω => ∏ q ∈ S, w q (ω q)) =
      Measure.infinitePi (fun q => AddCircle.haarAddCircle.withDensity (w q)) := by
  classical
  letI (q : ℕ) : IsProbabilityMeasure (AddCircle.haarAddCircle.withDensity (w q)) := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hone q]
  apply Measure.eq_infinitePi
  intro T t ht
  have hset : MeasurableSet ((T : Set ℕ).pi t) :=
    MeasurableSet.pi T.countable_toSet (fun q _ => ht q)
  let g (q : ℕ) (x : UnitAddCircle) : ℝ≥0∞ :=
    w q x * if q ∈ T then (t q).indicator 1 x else 1
  have hgm (q : ℕ) : Measurable (g q) := by
    unfold g
    split_ifs with hq
    · exact (hm q).mul (measurable_const.indicator (ht q))
    · exact (hm q).mul measurable_const
  have he (ω : PhaseSpace) :
      ((T : Set ℕ).pi t).indicator (fun ω => ∏ q ∈ S, w q (ω q)) ω =
        ∏ q ∈ S ∪ T, g q (ω q) := by
    have hw : (∏ q ∈ S ∪ T, w q (ω q)) = ∏ q ∈ S, w q (ω q) :=
      (Finset.prod_subset Finset.subset_union_left (fun q _ hq => hout q hq _)).symm
    have hi : (∏ q ∈ S ∪ T, if q ∈ T then (t q).indicator (M := ℝ≥0∞) 1 (ω q) else 1) =
        ((T : Set ℕ).pi t).indicator 1 ω := by
      rw [Set.indicator_pi_one_apply]
      calc
        _ = ∏ q ∈ T, if q ∈ T then (t q).indicator (M := ℝ≥0∞) 1 (ω q) else 1 :=
          (Finset.prod_subset Finset.subset_union_right (fun q _ hq => by simp [hq])).symm
        _ = _ := Finset.prod_congr rfl (fun q hq => by simp only [if_pos hq])
    simp only [g, Finset.prod_mul_distrib, hw, hi]
    by_cases hω : ω ∈ (T : Set ℕ).pi t <;> simp [hω]
  have hlocal (q : ℕ) : (∫⁻ ω, g q (ω q) ∂phaseMeasure) =
      if q ∈ T then (AddCircle.haarAddCircle.withDensity (w q)) (t q) else 1 := by
    rw [coordinate_lintegral q (hgm q)]
    by_cases hq : q ∈ T
    · rw [if_pos hq, withDensity_apply _ (ht q)]
      have hi : g q = (t q).indicator (w q) := by
        funext x
        by_cases hx : x ∈ t q <;> simp [g, hq, hx]
      rw [hi, lintegral_indicator (ht q)]
    · simp only [g, if_neg hq, mul_one, hone q]
  rw [withDensity_apply _ hset, ← lintegral_indicator hset]
  simp_rw [he]
  have hprod : (∫⁻ ω : PhaseSpace, ∏ q ∈ S ∪ T, g q (ω q) ∂phaseMeasure) =
      ∏ q ∈ S ∪ T, ∫⁻ ω : PhaseSpace, g q (ω q) ∂phaseMeasure :=
    lintegral_prod_eq_prod_lintegral_of_indepFun (S ∪ T)
      (fun (q : ℕ) (ω : PhaseSpace) => g q (ω q)) (iIndepFun_infinitePi hgm)
      (fun q => (hgm q).comp (measurable_pi_apply q))
  rw [hprod]
  simp_rw [hlocal]
  calc
    _ = ∏ q ∈ T, if q ∈ T then (AddCircle.haarAddCircle.withDensity (w q)) (t q) else 1 :=
      (Finset.prod_subset Finset.subset_union_right (fun q _ hq => by simp [hq])).symm
    _ = _ := Finset.prod_congr rfl (fun q hq => by simp only [if_pos hq])

end NField.Alignment.SteinhausFiniteTilt

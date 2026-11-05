/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperUnweightedFactors

/-!
# Products on distinct original Haar coordinates

The coordinate functions may vary with both block and prime. Pairwise
disjoint finite prime sets give an injective coordinate map, so their
nested product integral factors under the original phaseMeasure.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperUnweightedCoordinateProducts
open scoped BigOperators
open MeasureTheory ProbabilityTheory SteinhausMoment

theorem integral_distinct_coordinates {ι : Type*} [Fintype ι]
    (idx : ι → ℕ) (hinj : Function.Injective idx)
    (f : ι → UnitAddCircle → ℝ) (hf : ∀ i, Measurable (f i)) :
    (∫ ω, ∏ i, f i (ω (idx i)) ∂phaseMeasure) =
      ∏ i, ∫ z, f i z ∂AddCircle.haarAddCircle := by
  have hi : iIndepFun (fun q (ω : PhaseSpace) => ω q) phaseMeasure :=
    iIndepFun_infinitePi (fun _ => measurable_id)
  have h := ((hi.precomp hinj).comp f hf).integral_fun_prod_eq_prod_integral
    (fun i => ((hf i).comp (measurable_pi_apply (idx i))).aestronglyMeasurable)
  simp only [Function.comp_apply] at h
  rw [h]
  apply Finset.prod_congr rfl
  intro i _
  rw [← integral_map (measurable_pi_apply (idx i)).aemeasurable
    (hf i).aestronglyMeasurable,phaseMeasure,Measure.infinitePi_map_eval]

theorem integral_nested_coordinates (s : Finset ℕ) (S : ℕ → Finset ℕ)
    (hS : Set.PairwiseDisjoint (↑s) S)
    (f : ℕ → ℕ → UnitAddCircle → ℝ) (hf : ∀ l q, Measurable (f l q)) :
    (∫ ω, ∏ l ∈ s, ∏ q ∈ S l, f l q (ω q) ∂phaseMeasure) =
      ∏ l ∈ s, ∏ q ∈ S l, ∫ z, f l q z ∂AddCircle.haarAddCircle := by
  classical
  let ι := (l : s) × S l.val
  let idx : ι → ℕ := fun a => a.2.val
  have hinj : Function.Injective idx := by
    rintro ⟨l,q⟩ ⟨m,r⟩ he
    change q.val = r.val at he
    have hlm : l = m := by
      apply Subtype.ext
      by_contra hn
      exact Finset.disjoint_left.mp (hS l.property m.property hn) q.property (he.symm ▸ r.property)
    subst m
    congr 1
    exact Subtype.ext he
  have h := integral_distinct_coordinates idx hinj (fun a z => f a.1.val a.2.val z)
    (fun a => hf a.1.val a.2.val)
  have flatten (g : ℕ → ℕ → ℝ) : (∏ a : ι, g a.1.val a.2.val) =
      ∏ l ∈ s, ∏ q ∈ S l, g l q := by
    rw [Fintype.prod_sigma]
    calc
      _ = ∏ l : s, ∏ q ∈ S l.val, g l.val q :=
        Finset.prod_congr rfl (fun l _ => (S l.val).prod_coe_sort (g l.val))
      _ = _ := s.prod_coe_sort (fun l => ∏ q ∈ S l, g l q)
  have he (ω : PhaseSpace) : (∏ a : ι, f a.1.val a.2.val (ω a.2.val)) =
      ∏ l ∈ s, ∏ q ∈ S l, f l q (ω q) := by
    exact flatten (fun l q => f l q (ω q))
  have he' : (∏ a : ι, ∫ z, f a.1.val a.2.val z ∂AddCircle.haarAddCircle) =
      ∏ l ∈ s, ∏ q ∈ S l, ∫ z, f l q z ∂AddCircle.haarAddCircle := by
    exact flatten (fun l q => ∫ z, f l q z ∂AddCircle.haarAddCircle)
  change (∫ ω, ∏ a : ι, f a.1.val a.2.val (ω a.2.val) ∂phaseMeasure) = _ at h
  simp_rw [he] at h
  rw [he'] at h
  exact h

end NField.Alignment.HarperUnweightedCoordinateProducts

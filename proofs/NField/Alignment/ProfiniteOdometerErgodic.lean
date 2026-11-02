/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionPotentialCoboundary
import Mathlib.Dynamics.Ergodic.Action.OfMinimal
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Ergodicity and uniqueness for the actual profinite odometer

The integer generator is dense in its profinite completion. Haar ergodicity
therefore makes every translation-invariant L² function constant.
-/

noncomputable section

namespace NField.Alignment.ProfiniteOdometerErgodic

open MeasureTheory Filter
open ProfiniteRemainderMeasure CollisionPotentialHilbert CollisionPotentialConvergence
open CollisionPotentialCoboundary

instance integerSubgroups_countable : Countable (Subgroup (Multiplicative ℤ)) := by
  apply Function.Surjective.countable (f := Subgroup.zpowers)
  intro H
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic H)
  refine ⟨(g : Multiplicative ℤ), ?_⟩
  have hm := congrArg (Subgroup.map H.subtype) hg
  simp only [MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hm
  change Subgroup.zpowers (g : Multiplicative ℤ) = H at hm
  exact hm

instance integerFiniteIndex_countable :
    Countable (FiniteIndexNormalSubgroup (Multiplicative ℤ)) :=
  Function.Injective.countable FiniteIndexNormalSubgroup.toSubgroup_injective

instance phaseSecondCountable : SecondCountableTopology Phase := by
  letI (H : FiniteIndexNormalSubgroup (Multiplicative ℤ)) :
      SecondCountableTopology ((ProfiniteGrp.ProfiniteCompletion.diagram
        (GrpCat.of (Multiplicative ℤ))).obj H) := by
    letI : Finite ((ProfiniteGrp.ProfiniteCompletion.diagram
        (GrpCat.of (Multiplicative ℤ))).obj H) :=
      inferInstanceAs (Finite ((Multiplicative ℤ) ⧸ H.toSubgroup))
    infer_instance
  change SecondCountableTopology
    ↥(ProfiniteGrp.limitConePtAux (ProfiniteGrp.ProfiniteCompletion.diagram
      (GrpCat.of (Multiplicative ℤ))))
  haveI : SecondCountableTopology ((H : FiniteIndexNormalSubgroup (Multiplicative ℤ)) →
      (ProfiniteGrp.ProfiniteCompletion.diagram (GrpCat.of (Multiplicative ℤ))).obj H) :=
    inferInstance
  exact TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val

theorem integerPhase_zpow (z : ℤ) : integerPhase z = integerPhase 1 ^ z := by
  let f : Multiplicative ℤ →* Phase :=
    (ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of (Multiplicative ℤ))).hom
  have h := map_zpow f (Multiplicative.ofAdd (1 : ℤ)) z
  change f (Multiplicative.ofAdd (z • (1 : ℤ))) = f (Multiplicative.ofAdd 1) ^ z at h
  have hi (w : ℤ) : f (Multiplicative.ofAdd w) = integerPhase w := rfl
  simpa only [zsmul_eq_mul, mul_one, Int.cast_id, hi] using h

theorem integerPhase_dense : DenseRange integerPhase := by
  have hd := ProfiniteGrp.ProfiniteCompletion.denseRange (G := GrpCat.of (Multiplicative ℤ))
  exact hd.comp (show Function.Surjective (Multiplicative.ofAdd : ℤ → Multiplicative ℤ) from
    fun x => ⟨x.toAdd, rfl⟩).denseRange continuous_of_discreteTopology

theorem odometer_ergodic : Ergodic (CollisionPotentialCoboundary.translate 1) phaseHaar := by
  have hd : DenseRange (fun z : ℤ => integerPhase 1 ^ z) := by
    simpa only [← integerPhase_zpow] using integerPhase_dense
  exact ergodic_mul_left_of_denseRange_zpow hd phaseHaar

theorem translation_invariant_constant (f : HaarL2) (hf : shift 1 f = f) :
    ∃ c : ℝ, (fun x => f x) =ᵐ[phaseHaar] (fun _ => c) := by
  have he : f ∘ CollisionPotentialCoboundary.translate 1 =ᵐ[phaseHaar] f := by
    have h := shift_coe 1 f
    rw [hf] at h
    exact h.symm
  exact odometer_ergodic.ae_eq_const_of_ae_eq_comp_ae (Lp.aestronglyMeasurable f) he

theorem translation_invariant_zero (f : HaarL2) (hf : shift 1 f = f)
    (hm : (∫ x, f x ∂phaseHaar) = 0) : f = 0 := by
  obtain ⟨c, hc⟩ := translation_invariant_constant f hf
  have hi := integral_congr_ae hc
  rw [hm, integral_const, probReal_univ, one_smul] at hi
  apply Lp.ext
  exact hc.trans (by rw [← hi]; exact (Lp.coeFn_zero ℝ 2 phaseHaar).symm)

theorem mean_zero_coboundary_unique (f g : HaarL2)
    (hf : (∫ x, f x ∂phaseHaar) = 0) (hg : (∫ x, g x ∂phaseHaar) = 0)
    (he : f - shift (-1) f = g - shift (-1) g) : f = g := by
  have hinv : shift 1 (f-g) = f-g := by
    have hback : shift (-1) (f-g) = f-g := by
      rw [map_sub]
      exact (sub_eq_sub_iff_sub_eq_sub.mp he).symm
    have h := congrArg (shift 1) hback
    rw [← shift_add, show (1 : ℤ)+(-1)=0 by norm_num, shift_zero] at h
    exact h.symm
  have hm : (∫ x, (f-g) x ∂phaseHaar) = 0 := by
    rw [← mean_inner_eq_integral, inner_sub_right, mean_inner_eq_integral,
      mean_inner_eq_integral, hf, hg, sub_self]
  exact sub_eq_zero.mp (translation_invariant_zero (f-g) hinv hm)

end NField.Alignment.ProfiniteOdometerErgodic

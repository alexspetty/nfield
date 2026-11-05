/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.SteinhausMoment

/-!
# Independence of disjoint finite groups of Haar coordinates

A measurable function invariant under changes outside a finite coordinate set
factors through that finite tuple. Disjoint tuples are independent in the
concrete Steinhaus probability space.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.SteinhausCoordinates

open scoped BigOperators
open MeasureTheory ProbabilityTheory SteinhausMoment

def DependsOn (s : Finset ℕ) (f : PhaseSpace → ℂ) : Prop :=
  ∀ ⦃ω ω' : PhaseSpace⦄, (∀ r ∈ s, ω r = ω' r) → f ω = f ω'

def extendCoordinates (s : Finset ℕ) (ω : s → UnitAddCircle) : PhaseSpace :=
  fun r => if h : r ∈ s then ω ⟨r, h⟩ else 0

theorem extendCoordinates_measurable (s : Finset ℕ) :
    Measurable (extendCoordinates s) := by
  apply measurable_pi_lambda
  intro r
  by_cases hr : r ∈ s
  · simpa only [extendCoordinates, dif_pos hr] using
      (measurable_pi_apply (⟨r, hr⟩ : s))
  · simp only [extendCoordinates, dif_neg hr]
    exact measurable_const

theorem dependsOn_factorization {s : Finset ℕ} {f : PhaseSpace → ℂ}
    (hf : DependsOn s f) (ω : PhaseSpace) :
    f (extendCoordinates s (fun r => ω r)) = f ω := by
  apply hf
  intro r hr
  simp only [extendCoordinates, dif_pos hr]

theorem independent_of_disjoint_coordinates {s t : Finset ℕ}
    (hst : Disjoint s t) {f g : PhaseSpace → ℂ}
    (hf : Measurable f) (hg : Measurable g)
    (hfs : DependsOn s f) (hgt : DependsOn t g) :
    IndepFun f g phaseMeasure := by
  have hi : iIndepFun (fun r (ω : PhaseSpace) => ω r) phaseMeasure :=
    iIndepFun_infinitePi (X := fun _ (x : UnitAddCircle) => x)
      (fun _ => measurable_id)
  have h := (hi.indepFun_finset s t hst (fun r => measurable_pi_apply r)).comp
    (hf.comp (extendCoordinates_measurable s))
    (hg.comp (extendCoordinates_measurable t))
  have hs : (f ∘ extendCoordinates s) ∘ (fun ω (r : s) => ω r) = f :=
    funext (dependsOn_factorization hfs)
  have ht : (g ∘ extendCoordinates t) ∘ (fun ω (r : t) => ω r) = g :=
    funext (dependsOn_factorization hgt)
  rwa [hs, ht] at h

theorem integral_mul_of_disjoint_coordinates {s t : Finset ℕ}
    (hst : Disjoint s t) {f g : PhaseSpace → ℂ}
    (hf : Measurable f) (hg : Measurable g)
    (hfs : DependsOn s f) (hgt : DependsOn t g) :
    (∫ ω, f ω * g ω ∂phaseMeasure) =
      (∫ ω, f ω ∂phaseMeasure) * (∫ ω, g ω ∂phaseMeasure) :=
  (independent_of_disjoint_coordinates hst hf hg hfs hgt).integral_fun_mul_eq_mul_integral
    hf.aestronglyMeasurable hg.aestronglyMeasurable

theorem steinhaus_dependsOn (n : ℕ) : DependsOn n.primeFactors (steinhaus n) := by
  intro ω ω' h
  by_cases hn : n = 0
  · simp [hn]
  · simp only [steinhaus, if_neg hn]
    apply Finset.prod_congr rfl
    intro r hr
    unfold phase
    rw [h r hr]

theorem steinhaus_pair_dependsOn (u v : ℕ) :
    DependsOn (u.primeFactors ∪ v.primeFactors)
      (fun ω => steinhaus u ω * star (steinhaus v ω)) := by
  intro ω ω' h
  change steinhaus u ω * star (steinhaus v ω) = steinhaus u ω' * star (steinhaus v ω')
  rw [steinhaus_dependsOn u (fun r hr => h r (Finset.mem_union_left _ hr)),
    steinhaus_dependsOn v (fun r hr => h r (Finset.mem_union_right _ hr))]

end NField.Alignment.SteinhausCoordinates

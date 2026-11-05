/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionBernoulliActivationFinite
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Real

/-!
# Bernoulli activation for actual independent random variables

Every finite joint atom is identified from independence, then finite
additivity identifies arbitrary events of the Boolean configuration with
the proved product law. The concentration constant is dimension-free.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionBernoulliActivation

open scoped BigOperators Classical ENNReal
open MeasureTheory ProbabilityTheory
open CollisionBernoulliProduct CollisionBernoulliMoments CollisionBernoulliActivationFinite

variable {α Ω : Type*} [Fintype α] [DecidableEq α] [MeasurableSpace Ω]

def activeSet (X : α → Ω → Bool) (ω : Ω) : Finset α :=
  Finset.univ.filter (fun i => X i ω=true)

omit [MeasurableSpace Ω] in
theorem activeSet_eq_iff (X : α → Ω → Bool) (ω : Ω) (A : Finset α) :
    activeSet X ω=A ↔ ∀ i, X i ω=decide (i∈A) := by
  rw [Finset.ext_iff]
  simp only [activeSet,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro h i
    have hi := h i
    cases hx : X i ω <;> simp_all
  · intro h i
    rw [h i]
    simp

omit [MeasurableSpace Ω] in
theorem activeSet_atom (X : α → Ω → Bool) (A : Finset α) :
    {ω : Ω | activeSet X ω=A}=⋂ i : α, X i ⁻¹' {decide (i∈A)} := by
  ext ω
  simp only [Set.mem_setOf_eq,Set.mem_iInter,Set.mem_preimage,Set.mem_singleton_iff,activeSet_eq_iff]

theorem activeSet_atom_measurable (X : α → Ω → Bool) (hX : ∀ i, Measurable (X i)) (A : Finset α) :
    MeasurableSet {ω : Ω | activeSet X ω=A} := by
  rw [activeSet_atom]
  exact MeasurableSet.iInter (fun i => (measurableSet_singleton _).preimage (hX i))

theorem weightOn_univ_product (b : α → ℝ) (A : Finset α) :
    weightOn b Finset.univ A=∏ i : α, if i∈A then b i else 1-b i := by
  rw [Finset.prod_ite]
  simp only [weightOn,Finset.filter_mem_eq_inter,Finset.univ_inter,Finset.sdiff_eq_filter]

theorem independent_activeSet_atom (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : α → Ω → Bool) (hX : ∀ i, Measurable (X i)) (hI : iIndepFun X μ)
    (b : α → ℝ) (hb : ∀ i, μ.real {ω | X i ω=true}=b i) (A : Finset α) :
    μ.real {ω | activeSet X ω=A}=weightOn b Finset.univ A := by
  have h := hI.measure_inter_preimage_eq_mul Finset.univ
    (sets := fun i => {decide (i∈A)}) (fun _ _ => measurableSet_singleton _)
  have hr := congrArg ENNReal.toReal h
  simp only [Finset.mem_univ,Set.iInter_true,ENNReal.toReal_prod] at hr
  have hterm (i : α) : μ.real (X i ⁻¹' {decide (i∈A)})=if i∈A then b i else 1-b i := by
    by_cases hi : i∈A
    · simp only [hi,decide_true,if_true]
      change μ.real {ω | X i ω=true}=b i
      exact hb i
    · have he : X i ⁻¹' {false}=(X i ⁻¹' {true})ᶜ := by
        ext ω
        cases X i ω <;> simp
      simp only [hi,decide_false,if_false]
      rw [he,measureReal_compl ((measurableSet_singleton true).preimage (hX i)),probReal_univ]
      exact congrArg (fun x : ℝ => 1-x) (hb i)
  rw [activeSet_atom,weightOn_univ_product]
  calc
    _ = ∏ i : α, μ.real (X i ⁻¹' {decide (i∈A)}) := hr
    _ = _ := Finset.prod_congr rfl (fun i _ => hterm i)

theorem independent_activeSet_event (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : α → Ω → Bool) (hX : ∀ i, Measurable (X i)) (hI : iIndepFun X μ)
    (b : α → ℝ) (hb : ∀ i, μ.real {ω | X i ω=true}=b i)
    (P : Finset α → Prop) [DecidablePred P] :
    μ.real {ω | P (activeSet X ω)}=
      bernoulliAverage b Finset.univ (fun A => if P A then 1 else 0) := by
  let E : Finset α → Set Ω := fun A => if P A then {ω | activeSet X ω=A} else ∅
  have hE (A : Finset α) : MeasurableSet (E A) := by
    dsimp [E]
    split_ifs
    · exact activeSet_atom_measurable X hX A
    · exact MeasurableSet.empty
  have hd : Pairwise (fun A B => Disjoint (E A) (E B)) := by
    intro A B hne
    apply Set.disjoint_left.mpr
    intro ω hA hB
    by_cases hPA : P A
    · by_cases hPB : P B
      · simp only [E,if_pos hPA,if_pos hPB,Set.mem_setOf_eq] at hA hB
        exact hne (hA.symm.trans hB)
      · simp only [E,if_neg hPB,Set.mem_empty_iff_false] at hB
    · simp only [E,if_neg hPA,Set.mem_empty_iff_false] at hA
  have hu : {ω | P (activeSet X ω)}=⋃ A : Finset α, E A := by
    ext ω
    simp only [Set.mem_setOf_eq,Set.mem_iUnion]
    constructor
    · intro h
      exact ⟨activeSet X ω,by simp [E,h]⟩
    · rintro ⟨A,hA⟩
      by_cases hPA : P A
      · simp only [E,if_pos hPA,Set.mem_setOf_eq] at hA
        rwa [hA]
      · simp only [E,if_neg hPA,Set.mem_empty_iff_false] at hA
  rw [hu,measureReal_iUnion_fintype hd hE]
  unfold bernoulliAverage
  rw [Finset.powerset_univ]
  apply Finset.sum_congr rfl
  intro A _
  by_cases hPA : P A
  · simp only [E,if_pos hPA,mul_one,independent_activeSet_atom μ X hX hI b hb A]
  · simp only [E,if_neg hPA,mul_zero,measureReal_empty]

theorem bernoulli_activation (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : α → Ω → Bool) (hX : ∀ i, Measurable (X i)) (hI : iIndepFun X μ)
    (hb : ∀ i, μ.real {ω | X i ω=true} ≤ 1/2)
    (F : Finset α → ℝ) {a u v : ℝ} (ha : 0<a) (huv : v-u<a)
    (hF : ∀ s i, i∉s → F s+a ≤ F (insert i s)) :
    μ.real {ω | F (activeSet X ω)∈Set.Icc u v} ≤
      20/Real.sqrt (1+∑ i : α, μ.real {ω | X i ω=true}) := by
  let b : α → ℝ := fun i => μ.real {ω | X i ω=true}
  rw [independent_activeSet_event μ X hX hI b (fun _ => rfl)
    (fun A => F A∈Set.Icc u v)]
  exact bernoulli_product_short_interval_bound b Finset.univ
    (fun i _ => ⟨measureReal_nonneg,hb i⟩) F ha huv hF

end NField.Alignment.CollisionBernoulliActivation

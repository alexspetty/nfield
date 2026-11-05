/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionFiniteActivationMixture
import Mathlib.Logic.Equiv.Prod

/-!
# Conditioning on unselected finite coordinates

An arbitrary selected subfamily is activated while all other coordinates
are fixed. Averaging the uniform bound over the latter preserves it.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionActivationSubfamily

open scoped BigOperators Classical
open CollisionFiniteActivationMixture

theorem uniform_product_section_bound {α β : Type*} [Fintype α] [Fintype β] [Nonempty β]
    (F : α × β → ℝ) (C : ℝ)
    (hF : ∀ b, (∑ a, F (a,b))/(Fintype.card α : ℝ)≤C) :
    (∑ x, F x)/(Fintype.card (α × β) : ℝ)≤C := by
  have hb : (0 : ℝ)<Fintype.card β := by exact_mod_cast Fintype.card_pos
  calc
    _ = (∑ b, (∑ a, F (a,b))/(Fintype.card α : ℝ))/(Fintype.card β : ℝ) := by
      rw [Fintype.card_prod,Nat.cast_mul,Fintype.sum_prod_type,Finset.sum_comm,← Finset.sum_div]
      ring
    _ ≤ (∑ _b : β, C)/(Fintype.card β : ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun b _ => hF b)) hb.le
    _ = C := by simp [hb.ne']

def extend {ι : Type*} {β : ι → Type*} (S : ι → Prop)
    (x : ∀ i : {i // S i}, β i) (y : ∀ i : {i // ¬S i}, β i) : ∀ i, β i :=
  (Equiv.piEquivPiSubtypeProd S β).symm (x,y)

theorem extend_selected {ι : Type*} {β : ι → Type*} (S : ι → Prop)
    (x : ∀ i : {i // S i}, β i) (y : ∀ i : {i // ¬S i}, β i) (i : {i // S i}) :
    extend S x y i=x i := by
  simp [extend,Equiv.piEquivPiSubtypeProd,i.property]

theorem extend_update {ι : Type*} {β : ι → Type*} (S : ι → Prop)
    (x : ∀ i : {i // S i}, β i) (y : ∀ i : {i // ¬S i}, β i) (i : {i // S i}) (z : β i) :
    extend S (Function.update x i z) y=Function.update (extend S x y) i.val z := by
  funext j
  by_cases hji : j=i.val
  · subst j
    simp [extend_selected]
  · have hsub : ∀ hj : S j, (⟨j,hj⟩ : {i // S i})≠i := by
      intro hj he
      exact hji (congrArg Subtype.val he)
    simp [extend,Equiv.piEquivPiSubtypeProd,hji,hsub]

theorem uniform_subfamily_activation_bound {ι : Type*} [Fintype ι]
    {β : ι → Type*} [∀ i, Fintype (β i)] [∀ i, Nonempty (β i)]
    (S : ι → Prop) (P : ∀ i, β i → Prop)
    (h0 : ∀ i, S i → Nonempty {x // ¬P i x})
    (h1 : ∀ i, S i → Nonempty {x // P i x})
    (hb : ∀ i, S i → hitRatio (P i)≤1/2)
    (F : (∀ i, β i) → ℝ) {a u v : ℝ} (ha : 0<a) (huv : v-u<a)
    (hF : ∀ (x : ∀ i, β i) i, S i → ∀ y, ¬P i (x i) → P i y →
      F x+a≤F (Function.update x i y)) :
    (∑ x, if F x∈Set.Icc u v then (1 : ℝ) else 0)/(Fintype.card (∀ i, β i) : ℝ)≤
      20/Real.sqrt (1+∑ i : {i // S i}, hitRatio (P i)) := by
  letI : DecidableEq {i // S i} := fun a b => Classical.propDecidable (a=b)
  letI : DecidableEq {i // ¬S i} := fun a b => Classical.propDecidable (a=b)
  let e := Equiv.piEquivPiSubtypeProd S β
  rw [Fintype.card_congr e,← Equiv.sum_comp e.symm]
  apply uniform_product_section_bound
  intro y
  apply uniform_coordinate_activation_bound (fun i : {i // S i} => P i)
    (fun i => h0 i i.property) (fun i => h1 i i.property) (fun i => hb i i.property)
    (fun x => F (extend S x y)) ha huv
  intro x i z hx hz
  have he : extend S (Function.update x i z) y=Function.update (extend S x y) i.val z := by
    convert extend_update S x y i z using 1
    congr 1
    funext j
    by_cases hj : j=i
    · subst j
      simp
    · simp [hj]
  rw [he]
  apply hF _ i.val i.property z
  · simpa only [extend_selected] using hx
  · exact hz

end NField.Alignment.CollisionActivationSubfamily

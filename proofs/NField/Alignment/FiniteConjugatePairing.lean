/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic

/-! # Finite regrouping under a fixed-point-free involution -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.FiniteConjugatePairing
open scoped BigOperators

variable {α : Type*} [Fintype α]

abbrev Representatives (f : α → α) :=
  {x : α // Fintype.equivFin α x < Fintype.equivFin α (f x)}

def complementEquiv (f : α → α) (hf : Function.Involutive f) (hne : ∀ x, f x ≠ x) :
    Representatives f ≃ {x : α // ¬Fintype.equivFin α x < Fintype.equivFin α (f x)} where
  toFun x := ⟨f x.val, by
    rw [hf x.val]
    exact not_lt_of_gt x.property⟩
  invFun x := ⟨f x.val, by
    rw [hf x.val]
    have hneq : Fintype.equivFin α (f x.val) ≠ Fintype.equivFin α x.val :=
      fun h => hne x.val ((Fintype.equivFin α).injective h)
    exact lt_of_le_of_ne (le_of_not_gt x.property) hneq⟩
  left_inv x := Subtype.ext (hf x.val)
  right_inv x := Subtype.ext (hf x.val)

def pairEquiv (f : α → α) (hf : Function.Involutive f) (hne : ∀ x, f x ≠ x) :
    Bool × Representatives f ≃ α :=
  (Equiv.boolProdEquivSum _).trans
    ((Equiv.sumCongr (Equiv.refl _) (complementEquiv f hf hne)).trans
      (Equiv.sumCompl (fun x : α => Fintype.equivFin α x < Fintype.equivFin α (f x))))

theorem pairEquiv_false (f : α → α) (hf : Function.Involutive f)
    (hne : ∀ x, f x ≠ x) (x : Representatives f) : pairEquiv f hf hne (false, x) = x := rfl

theorem pairEquiv_true (f : α → α) (hf : Function.Involutive f)
    (hne : ∀ x, f x ≠ x) (x : Representatives f) : pairEquiv f hf hne (true, x) = f x := rfl

theorem twice_pair_count (f : α → α) (hf : Function.Involutive f) (hne : ∀ x, f x ≠ x) :
    2 * Fintype.card (Representatives f) = Fintype.card α := by
  simpa using Fintype.card_congr (pairEquiv f hf hne)

theorem sum_pairs {A : Type*} [AddCommMonoid A]
    (f : α → α) (hf : Function.Involutive f) (hne : ∀ x, f x ≠ x) (w : α → A) :
    ∑ x : α, w x = ∑ r : Representatives f, (w r + w (f r)) := by
  rw [← Equiv.sum_comp (pairEquiv f hf hne)]
  simp [Fintype.sum_prod_type, pairEquiv_false, pairEquiv_true,
    Finset.sum_add_distrib, add_comm]

theorem pair_masses_sum (f : α → α) (hf : Function.Involutive f) (hne : ∀ x, f x ≠ x)
    (w : α → ℝ) (hw : ∑ x, w x = 1) :
    ∑ r : Representatives f, (w r + w (f r)) = 1 :=
  (sum_pairs f hf hne w).symm.trans hw

theorem scaled_overlap_pairs (f : α → α) (hf : Function.Involutive f)
    (hne : ∀ x, f x ≠ x) (w v : α → ℝ)
    (hw : ∀ x, w (f x) = w x) (hv : ∀ x, v (f x) = v x) :
    (Fintype.card α : ℝ) * ∑ x : α, w x * v x =
      (Fintype.card (Representatives f) : ℝ) *
        ∑ r : Representatives f, (w r + w (f r)) * (v r + v (f r)) := by
  have hc : (Fintype.card α : ℝ) = 2 * (Fintype.card (Representatives f) : ℝ) := by
    exact_mod_cast (twice_pair_count f hf hne).symm
  rw [hc, sum_pairs f hf hne (fun x => w x * v x)]
  simp only [hw, hv]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

end NField.Alignment.FiniteConjugatePairing

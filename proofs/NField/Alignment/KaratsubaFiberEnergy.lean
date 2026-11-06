/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KaratsubaPrimeMoment
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Reciprocal-sum fibers and their finite energy

The squared fiber counts equal the actual ordered collision count.
Translation correlations are bounded by the unshifted energy, retaining
the multiplicities of the original finite domain.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KaratsubaFiberEnergy
open scoped BigOperators

def fiberCount {α β : Type*} [Fintype α] [DecidableEq β] (f : α → β) (y : β) : ℕ :=
  (Finset.univ.filter fun x => f x = y).card

theorem sum_fiberCount {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) : ∑ y, fiberCount f y = Fintype.card α := by
  simpa only [fiberCount, Finset.card_univ] using
    (Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ)
      (f := f) (fun _ _ => Finset.mem_univ _)).symm

theorem sum_fiberCount_sq {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) : ∑ y, fiberCount f y ^ 2 = ∑ x, fiberCount f (f x) := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ f (fun x => fiberCount f (f x))]
  apply Finset.sum_congr rfl
  intro y _
  calc
    fiberCount f y ^ 2 = ∑ _x ∈ Finset.univ with f _x = y, fiberCount f y := by
      simp [fiberCount, pow_two]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]

theorem translation_correlation_le {G : Type*} [AddGroup G] [Fintype G]
    (c : G → ℕ) (t : G) : ∑ y, c y * c (y + t) ≤ ∑ y, c y ^ 2 := by
  have hs : ∑ y, c (y + t) ^ 2 = ∑ y, c y ^ 2 :=
    Equiv.sum_comp (Equiv.addRight t) (fun y => c y ^ 2)
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ c (fun y => c (y + t))
  rw [hs] at h
  rw [← pow_two] at h
  exact (Nat.pow_le_pow_iff_left (by decide : (2 : ℕ) ≠ 0)).mp h

theorem fiberCount_comp_le {α β γ : Type*} [Fintype α] [DecidableEq β] [DecidableEq γ]
    (f : α → β) (g : β → γ) (y : β) : fiberCount f y ≤ fiberCount (g ∘ f) (g y) := by
  apply Finset.card_le_card
  intro x hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, congrArg g (Finset.mem_filter.mp hx).2⟩

/-- Remembering another coordinate can only decrease collision energy. -/
theorem refinement_energy_le {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] (f : α → β) (g : β → γ) :
    ∑ y, fiberCount f y ^ 2 ≤ ∑ z, fiberCount (g ∘ f) z ^ 2 := by
  rw [sum_fiberCount_sq, sum_fiberCount_sq]
  exact Finset.sum_le_sum fun x _ => fiberCount_comp_le f g (f x)

open KaratsubaPrimeMoment

/-- The exact second moment of the reciprocal-sum populations. -/
theorem reciprocal_energy_eq_collisionCount (P : Finset ℕ) (m k : ℕ) [NeZero m] :
    (∑ y : ZMod m, fiberCount (fun u : PrimeTuple P k =>
      reciprocalSum m (fun i => (u i).val)) y ^ 2) = reciprocalCollisionCount P m k := by
  rw [sum_fiberCount_sq]
  rfl

/-- The finite energy estimate retains the actual prime populations. -/
theorem reciprocal_energy_le {P : Finset ℕ} {m k : ℕ} [NeZero m] {X : ℝ}
    (hX : 1 ≤ X) (hprime : ∀ p ∈ P, p.Prime) (hcop : ∀ p ∈ P, p.Coprime m)
    (hlower : ∀ p ∈ P, k < p) (hupper : ∀ p ∈ P, (p : ℝ) ≤ X)
    (hsize : (k : ℝ) * X ^ (2 * k - 1) < m) :
    (∑ y : ZMod m, fiberCount (fun u : PrimeTuple P k =>
      reciprocalSum m (fun i => (u i).val)) y ^ 2) ≤ k.factorial * P.card ^ k := by
  rw [reciprocal_energy_eq_collisionCount]
  exact reciprocalCollisionCount_le hX hprime hcop hlower hupper hsize

/-- Uniform translated population correlation, with no loss in the factorial constant. -/
theorem reciprocal_translation_correlation_le {P : Finset ℕ} {m k : ℕ} [NeZero m] {X : ℝ}
    (hX : 1 ≤ X) (hprime : ∀ p ∈ P, p.Prime) (hcop : ∀ p ∈ P, p.Coprime m)
    (hlower : ∀ p ∈ P, k < p) (hupper : ∀ p ∈ P, (p : ℝ) ≤ X)
    (hsize : (k : ℝ) * X ^ (2 * k - 1) < m) (t : ZMod m) :
    let c := fiberCount (fun u : PrimeTuple P k => reciprocalSum m (fun i => (u i).val))
    ∑ y, c y * c (y + t) ≤ k.factorial * P.card ^ k := by
  exact (translation_correlation_le _ t).trans
    (reciprocal_energy_le hX hprime hcop hlower hupper hsize)

end NField.Alignment.KaratsubaFiberEnergy
